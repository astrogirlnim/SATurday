"""
Proof source cache for loop native import (docs/prd/proof-import.md M1).

Auto wakes only read the cache. Operators populate it with:
  satday proof-source fetch <id> --from-dir /path/to/Expander_Graphs
  satday proof-source fetch <id> --network   # requires allow_network_fetch
"""

from __future__ import annotations

import json
import shutil
import tarfile
import urllib.request
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from infra.config.schemas import ProofImportCatalogEntry, ProofImportConfig, SaturdayLoopConfig


REQUIRED_META_FILES = ("LICENSE", "SOURCE.json")


@dataclass
class SourceStatus:
    """Readiness report for one catalog entry."""

    id: str
    title: str
    root: Path
    ready: bool
    license_ok: bool
    source_json_ok: bool
    thy_count: int
    primary_theory_hits: List[str] = field(default_factory=list)
    missing_primary: List[str] = field(default_factory=list)
    maps_to_frontier: List[str] = field(default_factory=list)
    notes: str = ""
    blockers: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        d = asdict(self)
        d["root"] = str(self.root)
        return d


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def load_proof_import_config(repo_root: Path) -> ProofImportConfig:
    """Load saturday_loop.proof_import from defaults (and env overrides via ConfigLoader)."""
    from infra.config.loader import ConfigLoader

    print(f"[saturday.proof_source] load_proof_import_config repo_root={repo_root}")
    cfg = ConfigLoader(repo_root=repo_root).load()
    loop: SaturdayLoopConfig = cfg.saturday_loop
    pi = loop.proof_import
    print(
        f"[saturday.proof_source] enabled={pi.enabled} "
        f"cache_dir={pi.cache_dir!r} allow_network_fetch={pi.allow_network_fetch} "
        f"catalog_size={len(pi.catalog)}"
    )
    return pi


def cache_root(repo_root: Path, cfg: ProofImportConfig) -> Path:
    root = (repo_root / cfg.cache_dir).resolve()
    print(f"[saturday.proof_source] cache_root={root}")
    return root


def entry_by_id(cfg: ProofImportConfig, source_id: str) -> ProofImportCatalogEntry:
    for e in cfg.catalog:
        if e.id == source_id:
            return e
    known = [e.id for e in cfg.catalog]
    raise KeyError(f"unknown proof source id={source_id!r}; catalog={known}")


def source_dir(repo_root: Path, cfg: ProofImportConfig, entry: ProofImportCatalogEntry) -> Path:
    return cache_root(repo_root, cfg) / entry.root


def thys_dir(src: Path) -> Path:
    return src / "thys"


def _list_thy_files(src: Path) -> List[Path]:
    thys = thys_dir(src)
    if not thys.is_dir():
        return []
    return sorted(
        p for p in thys.rglob("*.thy") if p.is_file() and not p.name.startswith("._")
    )


def _primary_hits(entry: ProofImportCatalogEntry, thy_files: List[Path]) -> Tuple[List[str], List[str]]:
    names = {p.stem for p in thy_files}
    hits = [t for t in entry.primary_theories if t in names]
    missing = [t for t in entry.primary_theories if t not in names]
    return hits, missing


def status_for_entry(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
) -> SourceStatus:
    """Compute whether an entry is ready for import prove (LICENSE + theories)."""
    print(f"[saturday.proof_source] status_for_entry id={entry.id}")
    root = source_dir(repo_root, cfg, entry)
    license_ok = (root / "LICENSE").is_file()
    source_json_ok = (root / "SOURCE.json").is_file()
    thy_files = _list_thy_files(root)
    hits, missing = _primary_hits(entry, thy_files)
    blockers: List[str] = []
    if not root.is_dir():
        blockers.append("source root missing")
    if not license_ok:
        blockers.append("LICENSE missing")
    if not source_json_ok:
        blockers.append("SOURCE.json missing")
    if not thy_files:
        blockers.append("no .thy files under thys/")
    if missing:
        blockers.append(f"missing primary theories: {', '.join(missing)}")
    ready = not blockers
    print(
        f"[saturday.proof_source] id={entry.id} ready={ready} "
        f"thy_count={len(thy_files)} blockers={blockers}"
    )
    return SourceStatus(
        id=entry.id,
        title=entry.title or entry.id,
        root=root,
        ready=ready,
        license_ok=license_ok,
        source_json_ok=source_json_ok,
        thy_count=len(thy_files),
        primary_theory_hits=hits,
        missing_primary=missing,
        maps_to_frontier=list(entry.maps_to_frontier),
        notes=entry.notes,
        blockers=blockers,
    )


def status_all(repo_root: Path, cfg: Optional[ProofImportConfig] = None) -> List[SourceStatus]:
    cfg = cfg or load_proof_import_config(repo_root)
    print(f"[saturday.proof_source] status_all catalog_size={len(cfg.catalog)}")
    return [status_for_entry(repo_root, cfg, e) for e in cfg.catalog]


def is_source_ready(repo_root: Path, source_id: str, cfg: Optional[ProofImportConfig] = None) -> bool:
    """M2 hook: import prove should refuse if False."""
    cfg = cfg or load_proof_import_config(repo_root)
    entry = entry_by_id(cfg, source_id)
    return status_for_entry(repo_root, cfg, entry).ready


def _write_source_json(
    root: Path,
    entry: ProofImportCatalogEntry,
    *,
    method: str,
    revision: str,
    extra: Optional[Dict[str, Any]] = None,
) -> None:
    payload: Dict[str, Any] = {
        "id": entry.id,
        "title": entry.title,
        "itps": list(entry.itps),
        "license": entry.license,
        "vendored_at": _now_iso(),
        "method": method,
        "revision": revision,
        "primary_theories": list(entry.primary_theories),
        "maps_to_rungs": list(entry.maps_to_rungs),
        "maps_to_frontier": list(entry.maps_to_frontier),
        "notes": entry.notes,
        "afp_entry_url": "https://isa-afp.org/entries/Expander_Graphs.html",
    }
    if extra:
        payload.update(extra)
    path = root / "SOURCE.json"
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"[saturday.proof_source] wrote {path}")


def _ensure_license(root: Path, entry: ProofImportCatalogEntry) -> None:
    path = root / "LICENSE"
    if path.is_file():
        print(f"[saturday.proof_source] LICENSE already present at {path}")
        return
    text = (
        f"Foreign proof source: {entry.title or entry.id}\n"
        f"Declared license class: {entry.license}\n"
        "\n"
        "This directory holds a vendored copy of Isabelle AFP theories for use as\n"
        "a human readable import blueprint by the SATurday loop. See ATTRIBUTION.md\n"
        "and https://isa-afp.org/entries/Expander_Graphs.html for upstream terms.\n"
        "Do not treat these files as Lean axioms.\n"
    )
    path.write_text(text, encoding="utf-8")
    print(f"[saturday.proof_source] wrote stub LICENSE at {path}")


def _copy_thy_tree(src: Path, dest_thys: Path) -> int:
    """Copy .thy (and ROOT if present) from src into dest_thys. Returns file count."""
    print(f"[saturday.proof_source] copy_thy_tree src={src} dest={dest_thys}")
    if not src.is_dir():
        raise FileNotFoundError(f"from-dir is not a directory: {src}")
    if dest_thys.exists():
        print(f"[saturday.proof_source] removing prior thys at {dest_thys}")
        shutil.rmtree(dest_thys, ignore_errors=True)
        if dest_thys.exists():
            # macOS AppleDouble leftovers; force remove remaining entries
            for leftover in dest_thys.rglob("*"):
                try:
                    if leftover.is_file() or leftover.is_symlink():
                        leftover.unlink(missing_ok=True)
                except OSError as exc:
                    print(f"[saturday.proof_source] unlink warn {leftover}: {exc}")
            shutil.rmtree(dest_thys, ignore_errors=True)
    dest_thys.mkdir(parents=True, exist_ok=True)
    copied = 0
    for path in src.rglob("*"):
        if not path.is_file():
            continue
        if path.name.startswith("._"):
            continue
        if path.suffix not in {".thy", ".ML"} and path.name not in {"ROOT", "ROOTS"}:
            continue
        rel = path.relative_to(src)
        out = dest_thys / rel
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, out)
        copied += 1
        print(f"[saturday.proof_source] copied {rel}")
    # Also accept src already being a flat folder of .thy
    if copied == 0:
        for path in src.glob("*.thy"):
            shutil.copy2(path, dest_thys / path.name)
            copied += 1
            print(f"[saturday.proof_source] copied flat {path.name}")
    print(f"[saturday.proof_source] copy_thy_tree done count={copied}")
    return copied


def fetch_from_dir(
    repo_root: Path,
    source_id: str,
    from_dir: Path,
    cfg: Optional[ProofImportConfig] = None,
) -> SourceStatus:
    """Offline vendor: copy a local AFP session directory into the cache."""
    cfg = cfg or load_proof_import_config(repo_root)
    entry = entry_by_id(cfg, source_id)
    root = source_dir(repo_root, cfg, entry)
    print(
        f"[saturday.proof_source] fetch_from_dir id={source_id} "
        f"from_dir={from_dir} root={root}"
    )
    root.mkdir(parents=True, exist_ok=True)
    (root / "plans").mkdir(exist_ok=True)
    copied = _copy_thy_tree(from_dir.resolve(), thys_dir(root))
    if copied == 0:
        raise RuntimeError(f"no Isabelle theory files found under {from_dir}")
    _ensure_license(root, entry)
    _write_source_json(
        root,
        entry,
        method="from-dir",
        revision=str(from_dir.resolve()),
        extra={"copied_files": copied},
    )
    return status_for_entry(repo_root, cfg, entry)


def _extract_archive_member(archive: Path, member: str, dest_thys: Path) -> int:
    """Extract archive_member directory from tar.gz into dest_thys."""
    print(
        f"[saturday.proof_source] extract_archive archive={archive} "
        f"member={member!r} dest={dest_thys}"
    )
    if dest_thys.exists():
        shutil.rmtree(dest_thys)
    dest_thys.mkdir(parents=True, exist_ok=True)
    member = member.strip("/")
    copied = 0
    with tarfile.open(archive, "r:gz") as tf:
        members = [m for m in tf.getmembers() if m.name.replace("\\", "/").find(member) >= 0]
        print(f"[saturday.proof_source] matching tar members={len(members)}")
        # Prefer paths that contain the member as a path segment
        filtered = []
        for m in members:
            norm = m.name.replace("\\", "/")
            if f"/{member}/" in f"/{norm}/" or norm.endswith(f"/{member}") or norm == member:
                filtered.append(m)
        if not filtered:
            # Fallback: any path ending with Expander_Graphs/...
            leaf = member.split("/")[-1]
            filtered = [
                m
                for m in tf.getmembers()
                if f"/{leaf}/" in f"/{m.name.replace(chr(92), '/')}/"
                or m.name.replace("\\", "/").endswith(f"/{leaf}")
            ]
        print(f"[saturday.proof_source] filtered tar members={len(filtered)}")
        for m in filtered:
            if not m.isfile():
                continue
            norm = m.name.replace("\\", "/")
            # Strip up to and including the member prefix
            idx = norm.find(member)
            if idx < 0:
                leaf = member.split("/")[-1]
                idx = norm.find(leaf)
                if idx < 0:
                    continue
                rel = norm[idx + len(leaf) :].lstrip("/")
            else:
                rel = norm[idx + len(member) :].lstrip("/")
            if not rel:
                continue
            if not (rel.endswith(".thy") or rel.endswith(".ML") or rel in {"ROOT", "ROOTS"}):
                # Still copy ROOT and theory adjacent files
                if Path(rel).suffix not in {".thy", ".ML"} and Path(rel).name not in {
                    "ROOT",
                    "ROOTS",
                }:
                    continue
            out = dest_thys / rel
            out.parent.mkdir(parents=True, exist_ok=True)
            extracted = tf.extractfile(m)
            if extracted is None:
                continue
            out.write_bytes(extracted.read())
            copied += 1
            print(f"[saturday.proof_source] extracted {rel}")
    print(f"[saturday.proof_source] extract done count={copied}")
    return copied


def fetch_network(
    repo_root: Path,
    source_id: str,
    cfg: Optional[ProofImportConfig] = None,
    *,
    force: bool = False,
) -> SourceStatus:
    """
    Download the configured archive and extract the session member.

    Requires cfg.allow_network_fetch unless force=True (CLI --network with
    explicit operator override logged).
    """
    cfg = cfg or load_proof_import_config(repo_root)
    entry = entry_by_id(cfg, source_id)
    print(
        f"[saturday.proof_source] fetch_network id={source_id} "
        f"allow={cfg.allow_network_fetch} force={force} url={entry.fetch_url!r}"
    )
    if not cfg.allow_network_fetch and not force:
        raise RuntimeError(
            "network fetch disabled (saturday_loop.proof_import.allow_network_fetch=false). "
            "Vendor offline with: satday proof-source fetch "
            f"{source_id} --from-dir /path/to/afp/thys/Expander_Graphs "
            "or pass --network after setting allow_network_fetch true "
            "(or --network --force)."
        )
    if not entry.fetch_url:
        raise RuntimeError(f"catalog entry {source_id} has empty fetch_url")
    if not entry.archive_member:
        raise RuntimeError(f"catalog entry {source_id} has empty archive_member")

    root = source_dir(repo_root, cfg, entry)
    root.mkdir(parents=True, exist_ok=True)
    (root / "plans").mkdir(exist_ok=True)
    downloads = root / "downloads"
    downloads.mkdir(exist_ok=True)
    archive_path = downloads / "afp-current.tar.gz"

    print(f"[saturday.proof_source] downloading {entry.fetch_url} -> {archive_path}")
    urllib.request.urlretrieve(entry.fetch_url, archive_path)
    print(
        f"[saturday.proof_source] download complete bytes={archive_path.stat().st_size}"
    )

    copied = _extract_archive_member(archive_path, entry.archive_member, thys_dir(root))
    if copied == 0:
        raise RuntimeError(
            f"archive extract produced no theory files for member={entry.archive_member!r}"
        )
    _ensure_license(root, entry)
    _write_source_json(
        root,
        entry,
        method="network",
        revision=entry.fetch_url,
        extra={
            "archive_path": str(archive_path.relative_to(repo_root)),
            "archive_member": entry.archive_member,
            "copied_files": copied,
            "force": force,
        },
    )
    return status_for_entry(repo_root, cfg, entry)


def vendor_instructions(entry: ProofImportCatalogEntry) -> str:
    """Human readable offline vendor steps."""
    return (
        f"Vendor steps for {entry.id} ({entry.title}):\n"
        "1. Download AFP current from https://www.isa-afp.org/download/\n"
        "2. Unpack and locate thys/Expander_Graphs (or clone AFP and use that path).\n"
        f"3. Run: satday proof-source fetch {entry.id} "
        "--from-dir /path/to/thys/Expander_Graphs\n"
        "4. Run: satday proof-source status\n"
        "5. Confirm ready=true before enabling import prove in the loop (M2).\n"
        "Do not copy Isabelle sources into theory/. Cache only under search/proof_sources/.\n"
    )
