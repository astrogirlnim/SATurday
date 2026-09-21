"""
Discrete import ladder: foreign ITP theories -> ordered plan micros.

Generalizable across catalog entries. First parser: Isabelle .thy.
Does not write Lean. Emits / merges plans under search/proof_sources/<id>/plans/.

CLI: satday proof-source ladder <source_id>
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set

from infra.config.schemas import ProofImportCatalogEntry, ProofImportConfig

# Isabelle symbol fragments commonly appearing in decl names.
_ISABELLE_SYM: Dict[str, str] = {
    r"\<omega>": "omega",
    r"\<alpha>": "alpha",
    r"\<beta>": "beta",
    r"\<gamma>": "gamma",
    r"\<delta>": "delta",
    r"\<epsilon>": "epsilon",
    r"\<zeta>": "zeta",
    r"\<eta>": "eta",
    r"\<theta>": "theta",
    r"\<lambda>": "lambda",
    r"\<mu>": "mu",
    r"\<nu>": "nu",
    r"\<xi>": "xi",
    r"\<pi>": "pi",
    r"\<rho>": "rho",
    r"\<sigma>": "sigma",
    r"\<tau>": "tau",
    r"\<phi>": "phi",
    r"\<chi>": "chi",
    r"\<psi>": "psi",
    r"\<Sigma>": "Sigma",
    r"\<Gamma>": "Gamma",
    r"\<Delta>": "Delta",
    r"\<Lambda>": "Lambda",
    r"\<Phi>": "Phi",
    r"\<Psi>": "Psi",
    r"\<Omega>": "Omega",
    r"\<^sub>": "_",
    r"\<^sup>": "_",
    r"\<acute>": "",
    r"\<prime>": "prime",
}

# Top-level Isabelle declarations we turn into plan micros.
_ISABELLE_KINDS = (
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "definition",
    "fun",
    "primrec",
)

_ISABELLE_DECL_RE = re.compile(
    r"(?m)^(?P<kind>"
    + "|".join(_ISABELLE_KINDS)
    + r")\s+(?P<name>\S+?)(?:\s*::|\s*where\b|\s*:|\s*\[|\s*$)"
)


@dataclass
class ForeignDecl:
    """One named declaration extracted from a foreign theory file."""

    kind: str
    name: str
    theory: str
    line: int
    itp: str = "isabelle"
    raw_line: str = ""


@dataclass
class LadderBuildResult:
    """Outcome of building or merging an import ladder plan."""

    plan: Dict[str, Any]
    path: Optional[Path] = None
    decls_extracted: int = 0
    steps_emitted: int = 0
    steps_kept_done: int = 0
    theories: List[str] = field(default_factory=list)
    notes: str = ""


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sanitize_lean_ident(name: str) -> str:
    """Map a foreign identifier to a Lean-safe ASCII name fragment."""
    out = name or ""
    for sym, repl in _ISABELLE_SYM.items():
        out = out.replace(sym, repl)
    out = re.sub(r"\\<[A-Za-z0-9_]+>", "_", out)
    out = re.sub(r"[^A-Za-z0-9_]", "_", out)
    out = re.sub(r"_+", "_", out).strip("_")
    if not out:
        out = "anon"
    if out[0].isdigit():
        out = "n_" + out
    return out


def lean_name_prefix(entry: ProofImportCatalogEntry) -> str:
    """Stable Lean prefix for helpers ported from this source."""
    for pin in entry.maps_to_frontier or []:
        if "MGG" in pin:
            return "mggImport_"
        if "ProofSystem" in pin:
            return "psImport_"
        if "CSExpansion" in pin:
            return "cseImport_"
    slug = re.sub(r"[^A-Za-z0-9]+", "_", entry.id).strip("_")
    return (slug[:24] + "_") if slug else "import_"


def lean_module_for_entry(entry: ProofImportCatalogEntry) -> str:
    """Resolve Lean module path for plan steps (catalog or frontier heuristic)."""
    configured = (getattr(entry, "lean_module", None) or "").strip()
    if configured:
        print(f"[saturday.import_ladder] lean_module catalog={configured}")
        return configured
    for pin in entry.maps_to_frontier or []:
        if pin.startswith("MGGFrontier") or "MGGFrontier." in pin:
            return "theory/Theory/ProofComplexity/MGG.lean"
        if "ProofSystemFrontier" in pin:
            return "theory/Theory/ProofComplexity/Bridge/ProofSystem.lean"
        if "CSExpansionFrontier" in pin:
            return "theory/Theory/ProofComplexity/CSExpansion.lean"
    if "r5-cook-reckhow-bridge" in (entry.maps_to_rungs or []):
        return "theory/Theory/ProofComplexity/Bridge/ProofSystem.lean"
    if "r2-width-machinery" in (entry.maps_to_rungs or []):
        return "theory/Theory/ProofComplexity/MGG.lean"
    print("[saturday.import_ladder] lean_module fallback CSExpansion.lean")
    return "theory/Theory/ProofComplexity/CSExpansion.lean"


def extract_isabelle_decls(thy_text: str, theory: str) -> List[ForeignDecl]:
    """Parse top-level named decls from one Isabelle .thy body."""
    decls: List[ForeignDecl] = []
    for match in _ISABELLE_DECL_RE.finditer(thy_text or ""):
        kind = match.group("kind")
        name = match.group("name")
        if not name or name.startswith("["):
            continue
        # Skip Isabelle attributes-only forms without a real name.
        if name in {"shows", "assumes", "fixes", "defines", "obtains"}:
            continue
        line = (thy_text or "")[: match.start()].count("\n") + 1
        decls.append(
            ForeignDecl(
                kind=kind,
                name=name,
                theory=theory,
                line=line,
                itp="isabelle",
                raw_line=match.group(0).strip()[:200],
            )
        )
    print(
        f"[saturday.import_ladder] extract_isabelle theory={theory} "
        f"decls={len(decls)}"
    )
    return decls


def extract_decls_for_itp(
    itp: str, thy_text: str, theory: str
) -> List[ForeignDecl]:
    """Dispatch to the parser for this ITP family."""
    key = (itp or "isabelle").lower().strip()
    parsers: Dict[str, Callable[[str, str], List[ForeignDecl]]] = {
        "isabelle": extract_isabelle_decls,
        "afp": extract_isabelle_decls,
    }
    parser = parsers.get(key)
    if parser is None:
        raise ValueError(
            f"no import ladder parser for itp={itp!r}; "
            f"supported={sorted(parsers)}"
        )
    return parser(thy_text, theory)


def load_theory_text(
    thys_root: Path, theory_stem: str
) -> tuple[Optional[Path], str]:
    """Locate <stem>.thy under thys_root and return (path, text)."""
    path = thys_root / f"{theory_stem}.thy"
    if not path.is_file():
        matches = list(thys_root.rglob(f"{theory_stem}.thy"))
        path = matches[0] if matches else path
    if not path.is_file():
        print(f"[saturday.import_ladder] missing theory={theory_stem}")
        return None, ""
    text = path.read_text(encoding="utf-8", errors="replace")
    print(
        f"[saturday.import_ladder] loaded theory={theory_stem} "
        f"path={path} chars={len(text)}"
    )
    return path, text


def excerpt_decl(
    thy_text: str,
    decl_name: str,
    *,
    max_chars: int = 3500,
    context_lines_before: int = 2,
) -> str:
    """Slice thy_text from the named decl through a reasonable window."""
    if not thy_text or not decl_name:
        return ""
    # Match the decl line; Isabelle names may contain backslash symbols.
    pat = re.compile(
        rf"(?m)^(?:{'|'.join(_ISABELLE_KINDS)})\s+"
        + re.escape(decl_name)
        + r"(?:\s*::|\s*where\b|\s*:|\s*\[|\s*$)"
    )
    match = pat.search(thy_text)
    if not match:
        print(f"[saturday.import_ladder] excerpt miss name={decl_name!r}")
        return ""
    start = match.start()
    # Walk back a few lines for locale / fixes context.
    line_start = thy_text.rfind("\n", 0, start)
    for _ in range(context_lines_before):
        prev = thy_text.rfind("\n", 0, max(0, line_start))
        if prev < 0:
            break
        line_start = prev
    start = max(0, line_start + 1 if line_start >= 0 else 0)
    # End at next top-level decl of same class or soft char budget.
    rest = thy_text[match.end() :]
    next_decl = _ISABELLE_DECL_RE.search(rest)
    end = match.end() + (next_decl.start() if next_decl else len(rest))
    chunk = thy_text[start:end]
    if len(chunk) > max_chars:
        chunk = chunk[:max_chars] + "\n...(truncated)...\n"
    print(
        f"[saturday.import_ladder] excerpt name={decl_name!r} "
        f"chars={len(chunk)}"
    )
    return chunk


def step_id_for_decl(theory: str, decl: ForeignDecl) -> str:
    """Deterministic plan step id from theory + foreign name."""
    thy = re.sub(r"[^a-z0-9]+", "-", theory.lower()).strip("-")
    nm = sanitize_lean_ident(decl.name).replace("_", "-").lower()
    return f"thy-{thy}-{nm}"[:120]


def decls_to_micro_steps(
    entry: ProofImportCatalogEntry,
    decls: Sequence[ForeignDecl],
    *,
    kinds: Optional[Set[str]] = None,
    max_steps: Optional[int] = None,
    name_regex: Optional[re.Pattern[str]] = None,
) -> List[Dict[str, Any]]:
    """Turn foreign decls into unit=micro helper_insert plan steps."""
    module = lean_module_for_entry(entry)
    prefix = lean_name_prefix(entry)
    allow = kinds or set(_ISABELLE_KINDS)
    steps: List[Dict[str, Any]] = []
    seen_ids: Set[str] = set()
    for decl in decls:
        if decl.kind not in allow:
            continue
        if name_regex is not None and not name_regex.search(decl.name):
            continue
        sid = step_id_for_decl(decl.theory, decl)
        if sid in seen_ids:
            continue
        seen_ids.add(sid)
        lean = prefix + sanitize_lean_ident(decl.name)
        steps.append(
            {
                "id": sid,
                "status": "pending",
                "unit": "micro",
                "fill_mode": "helper_insert",
                "allowed_tactics": [
                    "exact",
                    "apply",
                    "intro",
                    "have",
                    "refine",
                    "simp",
                    "omega",
                    "decide",
                    "rfl",
                ],
                "max_chars": 4000,
                "foreign_theories": [decl.theory],
                "foreign_lemmas": [decl.name],
                "foreign_kind": decl.kind,
                "foreign_line": decl.line,
                "lean_name": lean,
                "module": module,
                "goal": (
                    f"Port Isabelle {decl.kind} `{decl.name}` from "
                    f"{decl.theory} as Lean helper `{lean}` "
                    f"(no Frontier sorry; no axiom)."
                ),
            }
        )
        if max_steps is not None and len(steps) >= max_steps:
            break
    print(
        f"[saturday.import_ladder] micro_steps={len(steps)} "
        f"from_decls={len(decls)} max={max_steps}"
    )
    return steps


def frontier_pin_steps(
    entry: ProofImportCatalogEntry,
    existing_plan: Optional[Dict[str, Any]] = None,
) -> List[Dict[str, Any]]:
    """Terminal sorry_replace steps for catalog maps_to_frontier pins."""
    module = lean_module_for_entry(entry)
    existing_by_lean: Dict[str, Dict[str, Any]] = {}
    for step in (existing_plan or {}).get("steps") or []:
        ln = str(step.get("lean_name") or "")
        if ln:
            existing_by_lean[ln] = step
    out: List[Dict[str, Any]] = []
    for pin in entry.maps_to_frontier or []:
        short = pin.rsplit(".", 1)[-1]
        prior = existing_by_lean.get(pin) or existing_by_lean.get(short)
        if prior and str(prior.get("status")) == "done":
            out.append(dict(prior))
            continue
        step = {
            "id": f"frontier-{sanitize_lean_ident(short).replace('_', '-').lower()}",
            "status": "pending",
            "unit": "research",
            "fill_mode": "sorry_replace",
            "allowed_tactics": [
                "exact",
                "apply",
                "intro",
                "have",
                "refine",
                "simp",
                "omega",
            ],
            "max_chars": 6000,
            "foreign_theories": list(entry.primary_theories or [])[:3],
            "foreign_lemmas": list(entry.primary_theories or [])[:2],
            "lean_name": pin,
            "module": module,
            "goal": (
                f"Discharge open Frontier sorry `{pin}` using prior "
                f"import micros and accepted decls."
            ),
        }
        if prior:
            for key in (
                "lean_sig",
                "goal",
                "foreign_lemmas",
                "foreign_theories",
                "id",
                "max_chars",
                "allowed_tactics",
            ):
                if prior.get(key) is not None:
                    step[key] = prior[key]
            step["id"] = str(prior.get("id") or step["id"])
        out.append(step)
    print(f"[saturday.import_ladder] frontier_pin_steps={len(out)}")
    return out


def merge_ladder_plan(
    entry: ProofImportCatalogEntry,
    *,
    micro_steps: Sequence[Dict[str, Any]],
    existing: Optional[Dict[str, Any]] = None,
    title: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Merge generated micros with an existing accepted plan.

    Keeps prior done steps. Drops old pending non-frontier research megasteps.
    Appends frontier pins last.
    """
    existing = existing or {}
    done_steps: List[Dict[str, Any]] = []
    done_ids: Set[str] = set()
    done_leans: Set[str] = set()
    for step in existing.get("steps") or []:
        if str(step.get("status", "pending")) != "done":
            continue
        done_steps.append(dict(step))
        done_ids.add(str(step.get("id") or ""))
        ln = str(step.get("lean_name") or "")
        if ln:
            done_leans.add(ln)
            done_leans.add(ln.rsplit(".", 1)[-1])

    pending_micros: List[Dict[str, Any]] = []
    for step in micro_steps:
        sid = str(step.get("id") or "")
        ln = str(step.get("lean_name") or "")
        if sid in done_ids or ln in done_leans:
            print(
                f"[saturday.import_ladder] skip micro already done "
                f"id={sid} lean={ln}"
            )
            continue
        pending_micros.append(dict(step))

    pins = frontier_pin_steps(entry, existing)
    # Avoid duplicating a frontier pin that was already listed as done.
    pending_pins: List[Dict[str, Any]] = []
    for pin in pins:
        if str(pin.get("status")) == "done":
            if str(pin.get("id")) not in done_ids:
                done_steps.append(pin)
            continue
        ln = str(pin.get("lean_name") or "")
        if ln in done_leans or ln.rsplit(".", 1)[-1] in done_leans:
            continue
        pending_pins.append(pin)

    steps = done_steps + pending_micros + pending_pins
    plan: Dict[str, Any] = {
        "source_id": entry.id,
        "title": title
        or existing.get("title")
        or f"{entry.title or entry.id} discrete import ladder",
        "accepted_at": existing.get("accepted_at") or _now_iso(),
        "revised_at": _now_iso(),
        "method": "import_ladder",
        "notes": (
            "Auto-built from foreign theory decls (unit=micro helper_insert) "
            "plus terminal Frontier sorry_replace pins. Generalizable via "
            "catalog primary_theories / maps_to_frontier / lean_module. "
            "Never encode foreign proofs as Lean axioms."
        ),
        "maps_to_frontier": list(entry.maps_to_frontier or []),
        "steps": steps,
        "ladder_meta": {
            "micro_count": len(pending_micros),
            "done_kept": len(done_steps),
            "frontier_pending": len(pending_pins),
            "itps": list(entry.itps or []),
            "lean_module": lean_module_for_entry(entry),
        },
    }
    print(
        f"[saturday.import_ladder] merge steps_total={len(steps)} "
        f"done={len(done_steps)} micro={len(pending_micros)} "
        f"frontier={len(pending_pins)}"
    )
    return plan


def collect_decls_for_entry(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    *,
    theories: Optional[Sequence[str]] = None,
) -> tuple[List[ForeignDecl], List[str]]:
    """Extract decls from vendored theories for one catalog entry."""
    from search.saturday.proof_source import source_dir, thys_dir

    root = source_dir(repo_root, cfg, entry)
    thys = thys_dir(root)
    stems = list(theories) if theories else list(entry.primary_theories or [])
    if not stems:
        stems = sorted(p.stem for p in thys.glob("*.thy"))
    itp = (entry.itps[0] if entry.itps else "isabelle").lower()
    all_decls: List[ForeignDecl] = []
    used: List[str] = []
    for stem in stems:
        _path, text = load_theory_text(thys, stem)
        if not text:
            continue
        used.append(stem)
        all_decls.extend(extract_decls_for_itp(itp, text, stem))
    print(
        f"[saturday.import_ladder] collect_decls entry={entry.id} "
        f"theories={used} decls={len(all_decls)}"
    )
    return all_decls, used


def build_import_ladder(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    *,
    theories: Optional[Sequence[str]] = None,
    kinds: Optional[Iterable[str]] = None,
    max_steps: Optional[int] = None,
    name_pattern: Optional[str] = None,
    merge_existing: bool = True,
    write: bool = True,
) -> LadderBuildResult:
    """
    Build a discrete lemma ladder plan for any ready catalog entry.

    Catalog fields that make this generalizable:
      - primary_theories (or --theories override)
      - maps_to_frontier (terminal pins)
      - lean_module (optional Lean home)
      - itps (parser family)
    """
    from search.saturday.proof_source import load_accepted_plan, save_accepted_plan

    print(
        f"[saturday.import_ladder] build entry={entry.id} "
        f"merge={merge_existing} write={write} max_steps={max_steps}"
    )
    decls, used = collect_decls_for_entry(
        repo_root, cfg, entry, theories=theories
    )
    kind_set = set(kinds) if kinds else set(_ISABELLE_KINDS)
    name_re = re.compile(name_pattern) if name_pattern else None
    micros = decls_to_micro_steps(
        entry,
        decls,
        kinds=kind_set,
        max_steps=max_steps,
        name_regex=name_re,
    )
    existing = (
        load_accepted_plan(repo_root, cfg, entry) if merge_existing else None
    )
    plan = merge_ladder_plan(
        entry, micro_steps=micros, existing=existing
    )
    path: Optional[Path] = None
    if write:
        path = save_accepted_plan(repo_root, cfg, entry, plan)
    meta = plan.get("ladder_meta") or {}
    return LadderBuildResult(
        plan=plan,
        path=path,
        decls_extracted=len(decls),
        steps_emitted=len(plan.get("steps") or []),
        steps_kept_done=int(meta.get("done_kept") or 0),
        theories=used,
        notes=json.dumps(meta),
    )


def lemma_focus_excerpt_for_step(
    repo_root: Path,
    cfg: ProofImportConfig,
    entry: ProofImportCatalogEntry,
    step: Dict[str, Any],
    *,
    max_chars: int = 3500,
) -> str:
    """Best-effort foreign excerpt centered on the step's first foreign lemma."""
    from search.saturday.proof_source import source_dir, thys_dir

    lemmas = [str(x) for x in (step.get("foreign_lemmas") or []) if x]
    theories = [str(x) for x in (step.get("foreign_theories") or []) if x]
    if not lemmas or not theories:
        return ""
    thys = thys_dir(source_dir(repo_root, cfg, entry))
    name = lemmas[0]
    for stem in theories:
        _path, text = load_theory_text(thys, stem)
        if not text:
            continue
        chunk = excerpt_decl(text, name, max_chars=max_chars)
        if chunk:
            return f"--- {stem}.thy focus `{name}` ---\n{chunk}"
    return ""
