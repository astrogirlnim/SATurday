"""
Proof source cache for loop native import (docs/prd/proof-import.md M1).

Auto wakes only read the cache. Operators populate it with:
  satday proof-source fetch <id> --from-dir /path/to/Expander_Graphs
  satday proof-source fetch <id> --network   # requires allow_network_fetch
"""

from __future__ import annotations

import json
import re
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


def catalog_entries_for_rung(
    cfg: ProofImportConfig, rung_id: str
) -> List[ProofImportCatalogEntry]:
    """Catalog rows that map to this ladder rung."""
    rows = [e for e in cfg.catalog if rung_id in e.maps_to_rungs]
    print(
        f"[saturday.proof_source] catalog_entries_for_rung rung={rung_id} "
        f"hits={[e.id for e in rows]}"
    )
    return rows


def plans_dir(repo_root: Path, cfg: ProofImportConfig, entry: ProofImportCatalogEntry) -> Path:
    return source_dir(repo_root, cfg, entry) / "plans"


def accepted_plan_path(
    repo_root: Path, cfg: ProofImportConfig, entry: ProofImportCatalogEntry
) -> Path:
    return plans_dir(repo_root, cfg, entry) / "accepted.json"


def load_accepted_plan(
    repo_root: Path, cfg: ProofImportConfig, entry: ProofImportCatalogEntry
) -> Optional[Dict[str, Any]]:
    path = accepted_plan_path(repo_root, cfg, entry)
    if not path.is_file():
        print(f"[saturday.proof_source] no accepted plan at {path}")
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    print(
        f"[saturday.proof_source] loaded accepted plan id={entry.id} "
        f"steps={len(data.get('steps') or [])}"
    )
    return data


def save_accepted_plan(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    plan: Dict[str, Any],
) -> Path:
    """Write accepted.json and a timestamped copy under plans/."""
    pdir = plans_dir(repo_root, cfg, entry)
    pdir.mkdir(parents=True, exist_ok=True)
    plan = dict(plan)
    plan.setdefault("source_id", entry.id)
    plan.setdefault("accepted_at", _now_iso())
    stamped = pdir / f"plan_{_now_iso().replace(':', '')}.json"
    text = json.dumps(plan, indent=2) + "\n"
    stamped.write_text(text, encoding="utf-8")
    accepted = accepted_plan_path(repo_root, cfg, entry)
    accepted.write_text(text, encoding="utf-8")
    print(f"[saturday.proof_source] saved plan {stamped} and {accepted}")
    return accepted


def next_plan_step(plan: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """First step with status not done."""
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) != "done":
            return step
    return None


# AFP Graph_Theory / locale surface we have not ported into MGG.lean yet.
# Calling the model on these burns tokens and always invents types.
_UNPORTED_FOREIGN_SURFACE = frozenset(
    {
        "wf_digraph",
        "fin_digraph",
        "pre_digraph",
        "digraph_iso",
        "digraph_isomorphism",
        "arc",
        "arcs",
        "arcs_pos",
        "arcs_neg",
        "verts",
        "tail",
        "head",
        "strongly_explicit_expander",
        "see_mgg",
        "graph_of",
        "unfold_locales",
        # Fourier / complex analysis cluster (needs Complex + noncomputable)
        "omega_f",
        "ft",
        "periodic",
        "t_1",
        "s_1",
        "t_2",
        "s_2",
        "gamma_aux",
        "gamma",
        "compare",
        "alpha",
        "parseval",
        "plancharel",
        "complex.cis",
        "complex.exp",
        "fourier",
        "tau",
        "phi",
        "mgg_bound",
        "l",
        "real.cos",
        "real.sin",
    }
)

_EXECUTABLE_FOREIGN_KINDS = frozenset(
    {"fun", "definition", "abbreviation", "consts", "def", "primrec"}
)

_PROOF_FOREIGN_KINDS = frozenset(
    {"lemma", "theorem", "corollary", "proposition"}
)


def _normalize_foreign_name(name: str) -> str:
    """Strip Isabelle symbol markup so \<tau> matches tau."""
    text = (name or "").lower()
    text = re.sub(r"\\?<[^>]+>", "", text)  # leftover
    text = text.replace("\\<", "").replace(">", "")
    # Common: \<tau> -> after removing markup junk becomes tau if we extract
    m = re.search(r"\\?<([a-z0-9]+)>", (name or "").lower())
    if m:
        return m.group(1)
    m = re.search(r"\\<([a-z0-9]+)>", (name or "").lower())
    if m:
        return m.group(1)
    # lean_name mggImport_tau -> tau
    short = text.rsplit(".", 1)[-1]
    if short.startswith("mggimport_"):
        return short[len("mggimport_") :]
    return short


def step_needs_unported_surface(step: Dict[str, Any]) -> bool:
    """True when the foreign names require AFP digraph locales we lack."""
    names = []
    for fl in step.get("foreign_lemmas") or []:
        names.append(_normalize_foreign_name(str(fl)))
    lean_norm = _normalize_foreign_name(str(step.get("lean_name") or ""))
    if lean_norm:
        names.append(lean_norm)
    goal = str(step.get("goal") or "").lower()
    lean = str(step.get("lean_name") or "").lower()
    blob = " ".join(names) + " " + goal + " " + lean
    kind = str(step.get("foreign_kind") or "").lower()
    # Allow already-landed MGG Finset ports even if goal text mentions digraph.
    if any(n in {"mgg_graph", "mgg_graph_step"} for n in names):
        return False
    if any(n in _UNPORTED_FOREIGN_SURFACE for n in names):
        return True
    # Substring match only for longer tokens (avoid 'l' matching everything).
    long_toks = [t for t in _UNPORTED_FOREIGN_SURFACE if len(t) >= 4]
    if any(tok in blob for tok in long_toks):
        if kind in _EXECUTABLE_FOREIGN_KINDS and any(
            n.startswith("mgg_graph") for n in names
        ):
            return False
        return True
    return False


# Frontier pins that need Gabber Galil / Fourier / Complex analysis, not Finset.
_ANALYSIS_FRONTIER_MARKERS = (
    "gabber",
    "galil",
    "fourier",
    "rayleigh",
    "mgg-cheeger-multi",
    "mgg_has_multi_cheeger",
    "mgg-inv-glue",
    "mgggraph_hasexpansioninv",
    "real.cos",
    "complex",
)


def step_needs_analysis_surface(step: Dict[str, Any]) -> bool:
    """True when discharging this pin needs Real/Complex analysis imports."""
    blob = " ".join(
        [
            str(step.get("id") or ""),
            str(step.get("lean_name") or ""),
            str(step.get("goal") or ""),
        ]
    ).lower()
    return any(m in blob for m in _ANALYSIS_FRONTIER_MARKERS)


def module_has_analysis_surface(module_text: str) -> bool:
    """True when the Lean module already imports analysis / Complex."""
    text = module_text or ""
    needles = (
        "Mathlib.Analysis",
        "Mathlib.Data.Complex",
        "Mathlib.Analysis.SpecialFunctions",
        "import Mathlib.Topology",
    )
    return any(n in text for n in needles)


def step_is_cheap_executable(
    step: Dict[str, Any],
    *,
    module_text: Optional[str] = None,
) -> bool:
    """
    True when formalize should spend tokens on this micro today.

    Proof micros (lemma/theorem/...) are not executable without an explicit
    lean_sig and a Lean surface that already hosts the foreign API.
    Spectral / Gabber Galil Frontier pins stay non-executable until the host
    module imports an analysis surface (avoids local models inventing Nat
    witnesses like mgg_gabber_galil_cheeger_nat_witness).
    """
    if str(step.get("fill_mode") or "") == "sorry_replace":
        if step_needs_analysis_surface(step):
            if module_text is None or not module_has_analysis_surface(module_text):
                print(
                    f"[saturday.proof_source] skip spectral sorry_replace "
                    f"id={step.get('id')} lean_name={step.get('lean_name')} "
                    f"(no analysis surface; keep pending)"
                )
                return False
        return True
    kind = str(step.get("foreign_kind") or "").lower()
    if step_needs_unported_surface(step):
        return False
    if kind in _PROOF_FOREIGN_KINDS:
        # Only attempt proof micros when an explicit Lean signature was pinned.
        if not str(step.get("lean_sig") or "").strip():
            return False
    if kind in _EXECUTABLE_FOREIGN_KINDS:
        return True
    if kind in _PROOF_FOREIGN_KINDS and str(step.get("lean_sig") or "").strip():
        return True
    # Unknown kind: do not burn tokens.
    return False


def auto_defer_unportable_steps(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    plan: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Mark pending helper_insert micros done(deferred) when they are not
    executable on the current Lean surface (proof decls, digraph locales).
    """
    changed = False
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) == "done":
            continue
        if str(step.get("fill_mode") or "") != "helper_insert":
            continue
        if step_is_cheap_executable(step):
            continue
        reason = "deferred_missing_lean_surface"
        kind = str(step.get("foreign_kind") or "").lower()
        if kind in _PROOF_FOREIGN_KINDS:
            reason = "deferred_proof_micro_no_lean_surface"
        step["status"] = "done"
        step["done_reason"] = reason
        step["done_at"] = _now_iso()
        changed = True
        print(
            f"[saturday.proof_source] auto_defer step={step.get('id')} "
            f"lean_name={step.get('lean_name')} foreign_kind={kind} "
            f"reason={reason}"
        )
    if changed:
        save_accepted_plan(repo_root, cfg, entry, plan)
    return plan


def load_entry_module_text(
    repo_root: Path, entry: ProofImportCatalogEntry
) -> str:
    """Load the Lean module text for a catalog entry (empty if missing)."""
    module = str(getattr(entry, "lean_module", "") or "")
    if not module:
        return ""
    path = repo_root / module
    if not path.is_file():
        print(f"[saturday.proof_source] module missing path={path}")
        return ""
    text = path.read_text(encoding="utf-8")
    print(
        f"[saturday.proof_source] loaded module={module} chars={len(text)} "
        f"analysis={module_has_analysis_surface(text)}"
    )
    return text


def next_executable_plan_step(
    plan: Dict[str, Any],
    *,
    module_text: Optional[str] = None,
) -> Optional[Dict[str, Any]]:
    """
    First pending step that is cheap to attempt with the current Lean surface.

    Prefers fun/definition micros; does not fall back to proof micros that
    would only invent AFP types. Spectral sorry_replace pins stay pending but
    non-executable until module_text has an analysis surface.
    """
    pending = [
        s
        for s in (plan.get("steps") or [])
        if str(s.get("status", "pending")) != "done"
    ]
    for step in pending:
        if step_is_cheap_executable(step, module_text=module_text):
            print(
                f"[saturday.proof_source] next_executable "
                f"id={step.get('id')} kind={step.get('foreign_kind')}"
            )
            return step
    print(
        f"[saturday.proof_source] next_executable none "
        f"(pending={len(pending)} all deferred or non-executable)"
    )
    return None


def parse_import_cluster_target(target: str) -> Tuple[Optional[str], Optional[str]]:
    """
    Parse `import cluster: <source_id> step=<step_id>` into (source_id, step_id).

    Also accepts `import plan: <source_id> -> ...` (step_id None).
    """
    t = (target or "").strip()
    lower = t.lower()
    source_id: Optional[str] = None
    step_id: Optional[str] = None
    if lower.startswith("import cluster:"):
        rest = t[len("import cluster:") :].strip()
        parts = rest.split()
        if parts:
            source_id = parts[0].strip()
        for p in parts[1:]:
            if p.lower().startswith("step="):
                step_id = p.split("=", 1)[1].strip()
                break
    elif lower.startswith("import plan:"):
        rest = t[len("import plan:") :].strip()
        source_id = rest.split()[0].strip() if rest else None
    print(
        f"[saturday.proof_source] parse_import_cluster_target "
        f"source_id={source_id!r} step_id={step_id!r}"
    )
    return source_id, step_id


def plan_step_by_id(plan: Dict[str, Any], step_id: str) -> Optional[Dict[str, Any]]:
    """Lookup one plan step by id."""
    for step in plan.get("steps") or []:
        if str(step.get("id") or "") == step_id:
            return step
    print(f"[saturday.proof_source] plan_step_by_id miss id={step_id!r}")
    return None


def frontier_ns_for_module(module: str) -> str:
    """Map Lean module path to the Frontier namespace that owns import pins."""
    mod = (module or "").replace("\\", "/")
    if mod.endswith("MGG.lean") or "/MGG.lean" in mod:
        return "MGGFrontier"
    if "Bridge/ProofSystem.lean" in mod or mod.endswith("ProofSystem.lean"):
        return "ProofSystemFrontier"
    if mod.endswith("CSExpansion.lean") or "/CSExpansion.lean" in mod:
        return "CSExpansionFrontier"
    print(
        f"[saturday.proof_source] frontier_ns_for_module default "
        f"CSExpansionFrontier module={module!r}"
    )
    return "CSExpansionFrontier"


def lean_name_is_open_sorry(
    module_text: str, lean_name: str, *, quiet: bool = False
) -> bool:
    """True when lean_name is an open `:= by sorry` theorem/lemma in module_text."""
    from search.saturday.apply_lean import extract_open_frontier_obligations

    open_names = set(extract_open_frontier_obligations(module_text))
    short = (lean_name or "").rsplit(".", 1)[-1]
    hit = lean_name in open_names or short in open_names
    if not quiet:
        print(
            f"[saturday.proof_source] lean_name_is_open_sorry name={lean_name} "
            f"short={short} hit={hit} open_n={len(open_names)}"
        )
    return hit


def lean_name_is_certified(
    module_text: str, lean_name: str, *, quiet: bool = False
) -> bool:
    """
    True when lean_name appears as theorem/lemma/def/abbrev with a non-sorry body.

    Used to auto-advance micro-steps that were already landed by prior clusters.
    Import ladder helpers are often `def` (not theorem); those must count.
    """
    if not lean_name:
        return False
    if lean_name_is_open_sorry(module_text, lean_name, quiet=True):
        return False
    short = lean_name.rsplit(".", 1)[-1]
    pat = re.compile(
        rf"(?m)^\s*(?:theorem|lemma|def|abbrev)\s+{re.escape(short)}\b"
    )
    hit = bool(pat.search(module_text))
    if not quiet:
        print(
            f"[saturday.proof_source] lean_name_is_certified name={lean_name} hit={hit}"
        )
    return hit


def mark_plan_step_done(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    step_id: str,
    *,
    reason: str = "formalize_applied",
) -> Optional[Dict[str, Any]]:
    """Flip one step to done and rewrite accepted.json (plus stamped copy)."""
    plan = load_accepted_plan(repo_root, cfg, entry)
    if plan is None:
        return None
    found = False
    for step in plan.get("steps") or []:
        if str(step.get("id") or "") == step_id:
            prev = step.get("status")
            step["status"] = "done"
            step["done_reason"] = reason
            step["done_at"] = _now_iso()
            found = True
            print(
                f"[saturday.proof_source] mark_plan_step_done id={step_id} "
                f"prev={prev!r} reason={reason}"
            )
            break
    if not found:
        print(f"[saturday.proof_source] mark_plan_step_done miss id={step_id}")
        return None
    save_accepted_plan(repo_root, cfg, entry, plan)
    return plan


def auto_advance_certified_steps(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    plan: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Mark pending micro-steps done when their lean_name is already certified
    in the step module (no open sorry).

    Reads each Lean module at most once (critical for large import ladders).
    """
    changed = False
    module_cache: Dict[str, str] = {}
    for step in plan.get("steps") or []:
        if str(step.get("status", "pending")) == "done":
            continue
        lean_name = str(step.get("lean_name") or "")
        module = str(step.get("module") or "")
        if not lean_name or not module:
            continue
        path_m = repo_root / module
        if not path_m.is_file():
            print(
                f"[saturday.proof_source] auto_advance skip missing module={module}"
            )
            continue
        if module not in module_cache:
            module_cache[module] = path_m.read_text(encoding="utf-8")
            print(
                f"[saturday.proof_source] auto_advance loaded module={module} "
                f"chars={len(module_cache[module])}"
            )
        text_m = module_cache[module]
        if lean_name_is_certified(text_m, lean_name, quiet=True):
            step["status"] = "done"
            step["done_reason"] = "already_certified"
            step["done_at"] = _now_iso()
            changed = True
            print(
                f"[saturday.proof_source] auto_advance certified "
                f"step={step.get('id')} lean_name={lean_name}"
            )
    if changed:
        save_accepted_plan(repo_root, cfg, entry, plan)
    return plan



def theory_excerpt(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    theory_stem: str,
    *,
    max_chars: int = 12000,
) -> str:
    """Load a vendored .thy text for prompt injection."""
    thys = thys_dir(source_dir(repo_root, cfg, entry))
    path = thys / f"{theory_stem}.thy"
    if not path.is_file():
        matches = list(thys.rglob(f"{theory_stem}.thy"))
        path = matches[0] if matches else path
    if not path.is_file():
        print(f"[saturday.proof_source] theory missing {theory_stem}")
        return f"(missing theory {theory_stem}.thy under {thys})"
    text = path.read_text(encoding="utf-8", errors="replace")
    print(
        f"[saturday.proof_source] theory_excerpt stem={theory_stem} "
        f"chars={len(text)} path={path}"
    )
    if len(text) <= max_chars:
        return text
    head = max_chars // 2
    tail = max_chars - head
    return text[:head] + "\n\n...(truncated)...\n\n" + text[-tail:]


def build_import_prompt_context(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    *,
    theory_stems: Optional[List[str]] = None,
    max_chars_per_theory: int = 8000,
    step: Optional[Dict[str, Any]] = None,
    budget: Optional[int] = None,
) -> str:
    """Concatenate theory excerpts for import prove or formalize.

    When ``step`` is set (formalize micro-cluster), prefer that step's
    ``foreign_theories`` / ``max_chars`` so Qwen sized wakes do not ingest a
    full AFP dump.
    """
    step = step or {}
    step_stems = list(step.get("foreign_theories") or [])
    stems = theory_stems or step_stems or list(entry.primary_theories) or []
    # Prefer Cheeger + MGG when present in cache (full plan prove only)
    preferred: List[str] = []
    if not step_stems:
        preferred = [
            "Expander_Graphs_MGG",
            "Expander_Graphs_Cheeger_Inequality",
            "Expander_Graphs_Eigenvalues",
            "Expander_Graphs_Definition",
        ]
    ordered: List[str] = []
    for s in preferred + stems:
        if s and s not in ordered:
            ordered.append(s)
    # Micro-steps: tight budget (default 4k total); megasteps keep 24k.
    step_max = step.get("max_chars")
    if budget is None:
        if step_max is not None:
            budget = int(step_max)
        elif step_stems:
            budget = 4000
        else:
            budget = 24000
    per_theory = int(step.get("max_chars_per_theory") or max_chars_per_theory)
    if step_stems:
        per_theory = min(per_theory, max(800, budget))
    parts = [
        f"Import source id: {entry.id}",
        f"Title: {entry.title}",
        f"ITPs: {', '.join(entry.itps)}",
        f"Frontier targets: {', '.join(entry.maps_to_frontier)}",
        "Rule: adapt the foreign argument into a Lean port plan. "
        "Never treat the foreign proof as a Lean axiom. "
        "Critical path close requires zero sorry.",
    ]
    used = 0
    if step:
        parts.append(
            "Current micro step id: "
            + str(step.get("id") or "")
            + "\nForeign lemmas (focus): "
            + ", ".join(str(x) for x in (step.get("foreign_lemmas") or []))
        )
        try:
            from search.saturday.import_ladder import lemma_focus_excerpt_for_step

            focus = lemma_focus_excerpt_for_step(
                repo_root,
                cfg,
                entry,
                step,
                max_chars=min(3500, int(step.get("max_chars") or 3500)),
            )
            if focus:
                parts.append(focus)
                used += len(focus)
                print(
                    "[saturday.proof_source] injected lemma focus excerpt "
                    f"chars={len(focus)}"
                )
        except Exception as exc:
            print(f"[saturday.proof_source] lemma focus skipped: {exc}")
    for stem in ordered:
        if used >= budget:
            break
        room = min(per_theory, budget - used)
        excerpt = theory_excerpt(
            repo_root, cfg, entry, stem, max_chars=room
        )
        block = f"\n--- theory {stem}.thy ---\n{excerpt}\n"
        parts.append(block)
        used += len(block)
    print(
        f"[saturday.proof_source] import_prompt_context theories={ordered} "
        f"chars={used} budget={budget} step={step.get('id')}"
    )
    return "\n".join(parts)


def suggest_import_action(
    repo_root: Path,
    rung_id: str,
    cfg: Optional[ProofImportConfig] = None,
) -> Optional[Tuple[str, str, str]]:
    """
    If this rung has a ready catalog source, return (action, target, rationale).

    Prove when no accepted plan yet; formalize when a plan step remains.
    """
    cfg = cfg or load_proof_import_config(repo_root)
    if not cfg.enabled:
        print("[saturday.proof_source] suggest_import_action disabled")
        return None
    entries = catalog_entries_for_rung(cfg, rung_id)
    if not entries:
        return None
    entry = entries[0]
    st = status_for_entry(repo_root, cfg, entry)
    if not st.ready:
        print(f"[saturday.proof_source] source not ready id={entry.id}")
        return None
    plan = load_accepted_plan(repo_root, cfg, entry)
    if plan is None:
        target = (
            f"import plan: {entry.id} -> "
            + (entry.maps_to_frontier[0] if entry.maps_to_frontier else "Frontier")
        )
        rationale = (
            f"Ready proof source {entry.id}; build import plan before formalize"
        )
        print(f"[saturday.proof_source] suggest prove target={target!r}")
        return "prove", target, rationale
    plan = auto_advance_certified_steps(repo_root, cfg, entry, plan)
    plan = auto_defer_unportable_steps(repo_root, cfg, entry, plan)
    module_text = load_entry_module_text(repo_root, entry)
    step = next_executable_plan_step(plan, module_text=module_text)
    if step is None:
        print(
            "[saturday.proof_source] accepted plan has no executable steps "
            "(spectral Frontier pins may remain pending without analysis surface)"
        )
        return None
    step_id = str(step.get("id") or step.get("lean_name") or "next")
    unit = str(step.get("unit") or "cluster")
    target = f"import cluster: {entry.id} step={step_id}"
    rationale = (
        f"Accepted import plan for {entry.id}; formalize next {unit} "
        f"lean_name={step.get('lean_name')} foreign_kind={step.get('foreign_kind')}"
    )
    print(f"[saturday.proof_source] suggest formalize target={target!r}")
    return "formalize", target, rationale


def is_import_target(target: str) -> bool:
    t = (target or "").strip().lower()
    return t.startswith("import plan:") or t.startswith("import cluster:")


def resolve_import_step(
    repo_root: Path,
    rung_id: str,
    target: str,
    cfg: Optional[ProofImportConfig] = None,
) -> Optional[Tuple[ProofImportCatalogEntry, Dict[str, Any], Dict[str, Any]]]:
    """
    Resolve (entry, plan, step) for an import cluster target.

    Returns None when the target is not an import cluster or the plan/step
    cannot be loaded.
    """
    cfg = cfg or load_proof_import_config(repo_root)
    if not is_import_target(target):
        return None
    source_id, step_id = parse_import_cluster_target(target)
    entry: Optional[ProofImportCatalogEntry] = None
    if source_id:
        try:
            entry = entry_by_id(cfg, source_id)
        except Exception as exc:
            print(f"[saturday.proof_source] resolve entry_by_id failed: {exc}")
            entry = None
    if entry is None:
        entries = catalog_entries_for_rung(cfg, rung_id)
        entry = entries[0] if entries else None
    if entry is None:
        print("[saturday.proof_source] resolve_import_step: no catalog entry")
        return None
    plan = load_accepted_plan(repo_root, cfg, entry)
    if plan is None:
        return None
    plan = auto_advance_certified_steps(repo_root, cfg, entry, plan)
    plan = auto_defer_unportable_steps(repo_root, cfg, entry, plan)
    module_text = load_entry_module_text(repo_root, entry)
    step: Optional[Dict[str, Any]] = None
    if step_id:
        step = plan_step_by_id(plan, step_id)
        # Chooser may still name a step that auto_advance/defer just closed.
        if step is not None and str(step.get("status", "pending")) == "done":
            print(
                f"[saturday.proof_source] resolve_import_step step={step_id} "
                "already done; advancing to next executable"
            )
            step = None
        elif step is not None and not step_is_cheap_executable(
            step, module_text=module_text
        ):
            print(
                f"[saturday.proof_source] resolve_import_step step={step_id} "
                "not executable on current Lean surface; advancing"
            )
            step = None
    if step is None:
        step = next_executable_plan_step(plan, module_text=module_text)
    if step is None:
        print("[saturday.proof_source] resolve_import_step: no open step")
        return None
    print(
        f"[saturday.proof_source] resolve_import_step entry={entry.id} "
        f"step={step.get('id')} module={step.get('module')}"
    )
    return entry, plan, step
