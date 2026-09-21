"""
Pre/post gates for formalize drafts before lake spend.

Architecture (reflection loop):
1. Sanitize: deterministic Lean 4 footgun rewrites (List.get! -> xs[i]!)
2. Validate: structure + known-identifier hygiene against excerpt/accepted/open
3. Structured meta: trailing JSON must name decl_name and uses[]
4. Repair: feed gate + lake digest back into the same wake (no new chooser)

Goals:
- Catch known Lean 4 footguns without an LLM call
- Require import-ladder micros to name the planned decl
- Ban sorry on helper_insert fills
- Prefer identifiers that already appear in the module excerpt or accepted list
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Sequence, Set


# Lean 4 removed List.get!; GetElem uses xs[i]!
_LIST_GET_BANG = re.compile(
    r"\b([A-Za-z_][\w']*)\.get!\s+([A-Za-z0-9_']+|\([^)]+\))"
)
_LEAN3_BEGIN = re.compile(r"(?m)(?::=\s*begin\b|^\s*begin\s*$)")
_SORRY = re.compile(r"\bsorry\b")
# Lean 3 ellipsis ranges and pattern `..` that Lean 4 rejects in this codebase
_LEAN3_DOTDOT = re.compile(r"\.\.|\[\s*\d+\s*\.\.\s*\d*\s*\]")
_DECL = re.compile(
    r"(?m)^\s*(theorem|lemma|def|abbrev)\s+([A-Za-z_][\w']*)\b"
)
_MGG_IMPORT = re.compile(r"\bmggImport_[A-Za-z0-9_']+\b")
# Capitalized Lean identifiers (types, lemmas, namespaces pieces)
_CAP_IDENT = re.compile(r"\b([A-Z][A-Za-z0-9_']*)\b")
# Call sites that invent names and burn lake cycles when wrong
_CALL_SITE = re.compile(
    r"\b(?:exact|apply|refine|rw|rwa|simp\s+only|simpa|have|let|exists|use|"
    r"convert|trans|calc|congr)\b[^.\n]{0,80}?"
    r"(?<![.])\b([A-Z][A-Za-z0-9_']*)\b"
)
_IDENT_ANY = re.compile(r"\b([A-Za-z_][A-Za-z0-9_']*)\b")

# Always-allowed surface (stdlib / mathlib noise / Lean keywords as idents)
_BUILTIN_CAP: Set[str] = {
    "Nat",
    "List",
    "Bool",
    "Prop",
    "True",
    "False",
    "Unit",
    "PUnit",
    "String",
    "Int",
    "Fin",
    "Option",
    "Sum",
    "Prod",
    "Empty",
    "Decidable",
    "Nonempty",
    "Classical",
    "Mathlib",
    "Lean",
    "Array",
    "HashMap",
    "HashSet",
    "Subtype",
    "Quotient",
    "Set",
    "Finset",
    "Multiset",
    "WithBot",
    "WithTop",
    "ULift",
    "PLift",
    "Iff",
    "And",
    "Or",
    "Not",
    "Exists",
    "Eq",
    "HEq",
    "Ne",
    "LT",
    "LE",
    "GT",
    "GE",
    "Dvd",
    "OfNat",
    "OfScientific",
    "Inhabited",
    "Repr",
    "ToString",
    "Monad",
    "Functor",
    "Applicative",
    "Traversable",
    "Id",
    "IO",
    "Except",
    "Result",
    "Sigma",
    "PSigma",
    "Function",
    "Equiv",
    "Embedding",
    "Order",
    "PartialOrder",
    "LinearOrder",
    "Lattice",
    "BooleanAlgebra",
    "Ring",
    "Semiring",
    "CommRing",
    "Field",
    "Group",
    "AddGroup",
    "Monoid",
    "AddMonoid",
    "Module",
    "Algebra",
    "Topology",
    "MeasurableSpace",
    "ProbabilityMeasure",
    "ENNReal",
    "NNReal",
    "Real",
    "Complex",
    "Rat",
    "BitVec",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "Char",
    "ByteArray",
    "Float",
    "Tactic",
    "Meta",
    "Elab",
    "Parser",
    "Syntax",
    "Name",
    "Expr",
    "Level",
    "MVarId",
    "FVarId",
    "LocalContext",
    "Theory",
    "ProofComplexity",
    "Bridge",
    "Frontier",
    "CSExpansion",
    "CSExpansionFrontier",
    "MGG",
    "MGGFrontier",
    "Resolution",
    "PHP",
    "MonotoneCalculus",
}


@dataclass
class DraftGateResult:
    """Outcome of sanitize + validate."""

    code: str
    ok: bool
    reasons: List[str] = field(default_factory=list)
    repairs: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    decl_kind: str = ""
    decl_name: str = ""
    unknown_idents: List[str] = field(default_factory=list)
    meta_decl_name: str = ""
    meta_uses: List[str] = field(default_factory=list)

    def repair_block(self) -> str:
        parts = []
        if self.reasons:
            parts.append("Validator rejected the draft:\n- " + "\n- ".join(self.reasons))
        if self.warnings:
            parts.append("Validator warnings:\n- " + "\n- ".join(self.warnings))
        if self.repairs:
            parts.append("Applied mechanical fixes:\n- " + "\n- ".join(self.repairs))
        if self.unknown_idents:
            parts.append(
                "Unknown capitalized identifiers (not in excerpt/accepted/builtins):\n- "
                + ", ".join(self.unknown_idents[:24])
            )
        return "\n\n".join(parts)


def sanitize_lean_draft(code: str) -> tuple[str, List[str]]:
    """Deterministic Lean 4 footgun rewrites. Returns (code, repair notes)."""
    text = code or ""
    repairs: List[str] = []

    def _repl_get(m: re.Match[str]) -> str:
        repairs.append(f"rewrote {m.group(0)} to {m.group(1)}[{m.group(2)}]!")
        return f"{m.group(1)}[{m.group(2)}]!"

    new = _LIST_GET_BANG.sub(_repl_get, text)
    if _LEAN3_BEGIN.search(new):
        repairs.append("detected Lean 3 begin/end (reject)")
    print(
        f"[saturday.draft_gate] sanitize repairs={len(repairs)} "
        f"chars_in={len(text)} chars_out={len(new)}"
    )
    return new, repairs


def extract_decl_names(code: str) -> List[str]:
    """All theorem/lemma/def/abbrev names declared in the draft."""
    return [m.group(2) for m in _DECL.finditer(code or "")]


def extract_referenced_cap_idents(code: str) -> List[str]:
    """Capitalized identifiers appearing in the draft (deduped, order kept)."""
    seen: Set[str] = set()
    out: List[str] = []
    for m in _CAP_IDENT.finditer(code or ""):
        name = m.group(1)
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def extract_call_site_idents(code: str) -> List[str]:
    """Identifiers used at exact/apply/rw/... sites (invented names hurt)."""
    seen: Set[str] = set()
    out: List[str] = []
    for m in _CALL_SITE.finditer(code or ""):
        name = m.group(1)
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def build_known_ident_set(
    *,
    module_excerpt: str = "",
    accepted_names: Optional[Sequence[str]] = None,
    open_obligations: Optional[Sequence[str]] = None,
    import_step: Optional[Dict[str, Any]] = None,
    draft_defined: Optional[Sequence[str]] = None,
    extra: Optional[Sequence[str]] = None,
) -> Set[str]:
    """
    Allowlist of short capitalized identifiers the model may cite.

    Sources: builtins, module excerpt, accepted FQ shorts, open Frontier names,
    import plan lean_name, names defined in the draft itself.
    """
    known: Set[str] = set(_BUILTIN_CAP)
    for src in (module_excerpt or "",):
        for m in _IDENT_ANY.finditer(src):
            known.add(m.group(1))
    for fq in accepted_names or []:
        short = str(fq).rsplit(".", 1)[-1]
        if short:
            known.add(short)
        for part in str(fq).split("."):
            if part:
                known.add(part)
    for name in open_obligations or []:
        short = str(name).rsplit(".", 1)[-1]
        if short:
            known.add(short)
    if import_step:
        lean = str(import_step.get("lean_name") or "")
        if lean:
            known.add(lean.rsplit(".", 1)[-1])
            for part in lean.split("."):
                if part:
                    known.add(part)
        for fl in import_step.get("foreign_lemmas") or []:
            short = str(fl).rsplit(".", 1)[-1]
            if short:
                known.add(short)
    for name in draft_defined or []:
        if name:
            known.add(str(name))
    for name in extra or []:
        if name:
            known.add(str(name))
    print(f"[saturday.draft_gate] known_idents size={len(known)}")
    return known


def parse_formalize_meta(meta: Optional[Dict[str, Any]]) -> tuple[str, List[str]]:
    """
    Pull structured fields from trailing JSON.

    Expected keys (soft): decl_name (str), uses (list[str]).
    """
    meta = meta or {}
    decl = str(meta.get("decl_name") or meta.get("lean_name") or "").strip()
    uses_raw = meta.get("uses") or meta.get("identifiers") or []
    uses: List[str] = []
    if isinstance(uses_raw, str):
        uses = [p.strip() for p in uses_raw.split(",") if p.strip()]
    elif isinstance(uses_raw, list):
        uses = [str(u).strip() for u in uses_raw if str(u).strip()]
    print(
        f"[saturday.draft_gate] meta decl_name={decl!r} uses={len(uses)}"
    )
    return decl, uses


def parse_formalize_envelope(meta: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    """Normalize structured formalize JSON (lean envelope)."""
    meta = meta or {}
    decl, uses = parse_formalize_meta(meta)
    extra_raw = meta.get("extra_decls") or []
    if isinstance(extra_raw, str):
        extras = [p.strip() for p in extra_raw.split(",") if p.strip()]
    elif isinstance(extra_raw, list):
        extras = [str(u).strip() for u in extra_raw if str(u).strip()]
    else:
        extras = []
    no_sorry = meta.get("no_sorry")
    if isinstance(no_sorry, str):
        no_sorry_b = no_sorry.strip().lower() in {"true", "1", "yes"}
    else:
        no_sorry_b = bool(no_sorry) if no_sorry is not None else False
    out = {
        "decl_name": decl,
        "uses": uses,
        "extra_decls": extras,
        "no_sorry": no_sorry_b,
        "decl_kind": str(meta.get("decl_kind") or "").strip().lower(),
        "status": str(meta.get("status") or "").strip().lower(),
    }
    print(
        f"[saturday.draft_gate] envelope decl={out['decl_name']!r} "
        f"kind={out['decl_kind']!r} no_sorry={out['no_sorry']} "
        f"extras={out['extra_decls']} status={out['status']!r}"
    )
    return out


def validate_lean_draft(
    code: str,
    *,
    import_step: Optional[Dict[str, Any]] = None,
    allow_sorry: bool = False,
    known_idents: Optional[Set[str]] = None,
    meta: Optional[Dict[str, Any]] = None,
    require_known_call_sites: bool = True,
    require_meta_decl: bool = False,
) -> DraftGateResult:
    """Structural + identifier checks before lake. Fail closed on clear footguns."""
    cleaned, repairs = sanitize_lean_draft(code)
    reasons: List[str] = []
    warnings: List[str] = []
    envelope = parse_formalize_envelope(meta)
    meta_decl = envelope["decl_name"]
    meta_uses = envelope["uses"]
    decls = list(_DECL.finditer(cleaned))
    if envelope["status"] == "blocked":
        reasons.append(
            "model marked status=blocked; refusing apply (missing Lean surface)"
        )
        return DraftGateResult(
            code=cleaned,
            ok=False,
            reasons=reasons,
            repairs=repairs,
            meta_decl_name=meta_decl,
            meta_uses=meta_uses,
        )
    if not decls:
        reasons.append("no theorem/lemma/def/abbrev declaration found")
        return DraftGateResult(
            code=cleaned,
            ok=False,
            reasons=reasons,
            repairs=repairs,
            meta_decl_name=meta_decl,
            meta_uses=meta_uses,
        )
    kind = decls[0].group(1)
    name = decls[0].group(2)
    defined = extract_decl_names(cleaned)
    fill = str((import_step or {}).get("fill_mode") or "")
    want = str((import_step or {}).get("lean_name") or "").rsplit(".", 1)[-1]
    foreign_kind = str((import_step or {}).get("foreign_kind") or "").lower()
    if want and name != want and want not in cleaned:
        reasons.append(
            f"expected decl name {want!r} from import plan; found {name!r}"
        )
    if fill == "helper_insert":
        if len(defined) != 1:
            reasons.append(
                f"helper_insert requires exactly one decl; found {defined}"
            )
        if want and defined and defined[0] != want:
            reasons.append(
                f"helper_insert decl must be {want!r}; found {defined[0]!r}"
            )
        for extra in envelope["extra_decls"]:
            short = extra.rsplit(".", 1)[-1]
            if want and short != want:
                reasons.append(
                    f"extra_decls must be empty or only {want!r}; got {short!r}"
                )
        if not envelope["no_sorry"]:
            reasons.append("JSON no_sorry must be true for helper_insert")
        if foreign_kind in {"fun", "definition", "abbreviation", "consts", "def"}:
            if kind != "def" and kind != "abbrev":
                reasons.append(
                    f"foreign_kind={foreign_kind} expects def/abbrev; got {kind}"
                )
        # Ban inventing other mggImport_* names in the body
        for hit in _MGG_IMPORT.findall(cleaned):
            if want and hit != want:
                reasons.append(
                    f"invented import helper {hit!r}; only {want!r} is allowed"
                )
    if require_meta_decl and meta_decl and meta_decl.rsplit(".", 1)[-1] != name:
        reasons.append(
            f"JSON decl_name {meta_decl!r} does not match Lean decl {name!r}"
        )
    elif meta_decl and meta_decl.rsplit(".", 1)[-1] != name:
        warnings.append(
            f"JSON decl_name {meta_decl!r} differs from Lean decl {name!r}"
        )
    if fill == "helper_insert" and _SORRY.search(cleaned):
        reasons.append("helper_insert forbids sorry")
    if not allow_sorry and fill == "helper_insert" and "sorry" in cleaned:
        reasons.append("sorry present on helper_insert draft")
    if _LEAN3_BEGIN.search(cleaned):
        reasons.append("Lean 3 begin/end is forbidden; use := by")
    if _LEAN3_DOTDOT.search(cleaned):
        reasons.append(
            "Lean 3 ellipsis `..` or [a..b] is forbidden; use Finset.range / List.range"
        )
    if ".get!" in cleaned:
        reasons.append(
            "Lean 4 has no List.get!; use xs[i]! (GetElem) instead of .get!"
        )
    if "begin" in cleaned.split() and "by" not in cleaned[:200]:
        reasons.append("possible Lean 3 proof style")

    unknown: List[str] = []
    if known_idents is not None:
        allow = set(known_idents) | set(defined) | set(_BUILTIN_CAP)
        # Names the model claimed in uses[] must be known
        for u in meta_uses:
            short = u.rsplit(".", 1)[-1]
            if short and short[0].isupper() and short not in allow:
                unknown.append(short)
                reasons.append(
                    f"JSON uses[] cites unknown identifier {short!r}; "
                    "use only excerpt/accepted names"
                )
        if require_known_call_sites:
            for cite in extract_call_site_idents(cleaned):
                if cite in allow:
                    continue
                unknown.append(cite)
                reasons.append(
                    f"call site cites unknown identifier {cite!r}; "
                    "prefer exact/apply of names from the excerpt or accepted list"
                )
        for cite in extract_referenced_cap_idents(cleaned):
            if cite in allow or cite in unknown:
                continue
            if cite.endswith("Frontier") or cite.endswith("Namespace"):
                continue
            warnings.append(f"unfamiliar capitalized token {cite!r}")

    ok = not reasons
    print(
        f"[saturday.draft_gate] validate ok={ok} kind={kind} name={name} "
        f"reasons={len(reasons)} warnings={len(warnings)} unknown={unknown}"
    )
    return DraftGateResult(
        code=cleaned,
        ok=ok,
        reasons=reasons,
        repairs=repairs,
        warnings=warnings,
        decl_kind=kind,
        decl_name=name,
        unknown_idents=unknown,
        meta_decl_name=meta_decl,
        meta_uses=meta_uses,
    )


def build_repair_context(
    *,
    failed_lean: str,
    build_tail: str = "",
    gate: Optional[DraftGateResult] = None,
    max_lean_chars: int = 3500,
) -> str:
    """Pack failed draft + lake/gate errors for the next formalize pass."""
    parts: List[str] = [
        "REPAIR PASS: your previous draft did not land. Fix it; do not start over.",
        "Keep the same declaration name. Prefer the smallest edit that compiles.",
        "Only cite identifiers that appear in the Lean excerpt or accepted list.",
        "After the lean fence, JSON must include decl_name and uses (array of "
        "identifiers you called).",
    ]
    if gate and (not gate.ok or gate.warnings or gate.repairs):
        parts.append(gate.repair_block())
    if build_tail.strip():
        parts.append("Lake / apply digest:\n" + build_tail.strip()[:4000])
    if failed_lean.strip():
        parts.append(
            "Failed draft (do not repeat its mistakes):\n"
            + failed_lean.strip()[:max_lean_chars]
        )
    parts.append(
        "Hard rules: Lean 4 only (`:= by`), no `List.get!` (use `xs[i]!`), "
        "no Lean 3 `begin`, no sorry on helper_insert, no new axioms, "
        "no invented lemma or type names."
    )
    text = "\n\n".join(parts)
    print(f"[saturday.draft_gate] repair_context chars={len(text)}")
    return text


def is_worth_repairing(build_tail: str, gate: Optional[DraftGateResult]) -> bool:
    """True when another model pass is likely cheaper than a fresh wake."""
    if gate is not None and not gate.ok:
        return True
    if gate is not None and gate.unknown_idents:
        return True
    low = (build_tail or "").lower()
    if not low.strip():
        return False
    needles = (
        "type mismatch",
        "unknown identifier",
        "invalid field",
        "not a proposition",
        "application type mismatch",
        "failed to synthesize",
        "get!",
        "function expected",
        "insufficient number of arguments",
        "don't know how to synthesize",
    )
    hit = any(n in low for n in needles)
    print(f"[saturday.draft_gate] worth_repairing={hit}")
    return hit
