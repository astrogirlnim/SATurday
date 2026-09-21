"""
Smart selection of accepted Lean declarations for saturday prompts.

`scripts/accepted_declarations.txt` is the axiom gate allowlist. Formalize
and prove prompts must not dump all ~1700 names. This module ranks a small
subset from (rung hints, open Frontier obligations, target text, excerpt,
prior errors) so models reuse certified lemmas instead of re proving them.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set

from infra.config.schemas import AcceptedSelectConfig

# Split CamelCase and snake_case into overlapping tokens for ranking.
_CAMEL_RE = re.compile(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+")
_IDENT_RE = re.compile(r"\b[A-Za-z][A-Za-z0-9_']{2,}\b")


@dataclass
class AcceptedSelectResult:
    """Ranked subset of accepted declaration names for one wake."""

    names: List[str] = field(default_factory=list)
    scores: Dict[str, float] = field(default_factory=dict)
    query_tokens: List[str] = field(default_factory=list)
    hint_hits: int = 0
    pool_size: int = 0
    decls_path: str = ""
    enabled: bool = True
    notes: str = ""

    def format_block(self, max_chars: int = 4000) -> str:
        """Render a prompt block; empty string when disabled or no hits."""
        if not self.enabled:
            print("[saturday.accepted_select] format_block skipped enabled=False")
            return ""
        if not self.names:
            print("[saturday.accepted_select] format_block empty names")
            return (
                "Accepted declarations (smart select): none ranked for this "
                "target. Prefer identifiers already in the Lean excerpt."
            )
        lines = [
            "Accepted declarations (smart select; reuse these; do not re prove):",
            f"(ranked {len(self.names)} of {self.pool_size}; "
            f"query tokens={','.join(self.query_tokens[:16]) or 'none'})",
        ]
        for fq in self.names:
            short = fq.rsplit(".", 1)[-1]
            score = self.scores.get(fq, 0.0)
            lines.append(f"- {short}  ({fq}, score={score:.1f})")
        text = "\n".join(lines)
        if len(text) > max_chars:
            text = text[: max_chars - 20] + "\n... (truncated)"
        print(
            f"[saturday.accepted_select] format_block chars={len(text)} "
            f"names={len(self.names)}"
        )
        return text


def load_accepted_declaration_names(decls_path: Path) -> List[str]:
    """Load fully qualified names from the axiom gate allowlist."""
    if not decls_path.is_file():
        print(f"[saturday.accepted_select] decls file missing: {decls_path}")
        return []
    names: List[str] = []
    for raw in decls_path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        names.append(line)
    print(f"[saturday.accepted_select] loaded {len(names)} decls from {decls_path}")
    return names


def tokenize_identifier(text: str) -> Set[str]:
    """Lowercase tokens from an identifier or free text blob."""
    out: Set[str] = set()
    for ident in _IDENT_RE.findall(text or ""):
        parts = _CAMEL_RE.findall(ident)
        if not parts:
            parts = ident.replace("'", "").split("_")
        for p in parts:
            p = p.strip("_'").lower()
            if len(p) >= 2 and not p.isdigit():
                out.add(p)
        whole = ident.replace("'", "").lower()
        if len(whole) >= 3:
            out.add(whole)
    return out


def _rung_hints(cfg: AcceptedSelectConfig, rung_id: str) -> List[str]:
    hints = list(cfg.rung_token_hints.get(rung_id) or [])
    print(
        f"[saturday.accepted_select] rung={rung_id} hint_count={len(hints)} "
        f"hints={hints[:12]}"
    )
    return hints


def _query_tokens(
    *,
    target: str,
    open_obligations: Sequence[str],
    module_excerpt: str,
    prior_errors: str,
    extra_text: str,
    hints: Sequence[str],
) -> Set[str]:
    blobs = [
        target or "",
        " ".join(open_obligations or []),
        (module_excerpt or "")[:8000],
        (prior_errors or "")[:4000],
        extra_text or "",
        " ".join(hints),
    ]
    tokens: Set[str] = set()
    for blob in blobs:
        tokens |= tokenize_identifier(blob)
    # Obligation short names as whole tokens boost exact lemma reuse
    for ob in open_obligations or []:
        short = ob.rsplit(".", 1)[-1]
        tokens |= tokenize_identifier(short)
        tokens.add(short.lower())
    print(
        f"[saturday.accepted_select] query_token_count={len(tokens)} "
        f"sample={sorted(tokens)[:20]}"
    )
    return tokens


def _score_decl(
    fq: str,
    *,
    query: Set[str],
    hints: Sequence[str],
    open_obligations: Sequence[str],
) -> float:
    short = fq.rsplit(".", 1)[-1]
    short_l = short.lower()
    fq_l = fq.lower()
    decl_tokens = tokenize_identifier(short)
    score = 0.0

    for ob in open_obligations or []:
        ob_l = ob.lower()
        if short_l == ob_l or short_l in ob_l or ob_l.endswith(short_l):
            score += 12.0
        # Shared multi token stems with the open pin
        ob_tokens = tokenize_identifier(ob)
        overlap_ob = decl_tokens & ob_tokens
        if overlap_ob:
            score += 2.0 * len(overlap_ob)

    overlap = decl_tokens & query
    score += 1.5 * len(overlap)

    hint_hit = False
    for h in hints:
        hl = (h or "").lower()
        if not hl:
            continue
        if hl in short_l or hl in fq_l:
            score += 3.0
            hint_hit = True
            break
    if hint_hit:
        score += 0.5

    # Prefer ProofComplexity surface over Bridge noise on R2 queries and vice versa
    if "bridge" in query and ".bridge." in fq_l:
        score += 1.0
    if any(t in query for t in ("mgg", "cheeger", "expansioninv")) and "mgg" in short_l:
        score += 2.0

    return score


def select_accepted_declarations(
    repo_root: Path,
    *,
    rung_id: str,
    target: str,
    open_obligations: Optional[Sequence[str]] = None,
    module_excerpt: str = "",
    prior_errors: str = "",
    extra_text: str = "",
    cfg: Optional[AcceptedSelectConfig] = None,
) -> AcceptedSelectResult:
    """
    Rank accepted declarations for this wake.

    Pipeline step: after open Frontier obligations are known, before the
    formalize (or prove) LLM call.
    """
    cfg = cfg or AcceptedSelectConfig()
    result = AcceptedSelectResult(enabled=cfg.enabled)
    if not cfg.enabled:
        result.notes = "accepted_select disabled in config"
        print(f"[saturday.accepted_select] {result.notes}")
        return result

    decls_path = Path(cfg.decls_path)
    if not decls_path.is_absolute():
        decls_path = Path(repo_root) / decls_path
    result.decls_path = str(decls_path)

    pool = load_accepted_declaration_names(decls_path)
    result.pool_size = len(pool)
    if not pool:
        result.notes = "empty accepted declarations pool"
        return result

    open_obs = list(open_obligations or [])
    hints = _rung_hints(cfg, rung_id)
    query = _query_tokens(
        target=target,
        open_obligations=open_obs,
        module_excerpt=module_excerpt,
        prior_errors=prior_errors,
        extra_text=extra_text,
        hints=hints,
    )
    result.query_tokens = sorted(query)[:48]

    scored: List[tuple] = []
    hint_hits = 0
    for fq in pool:
        sc = _score_decl(
            fq, query=query, hints=hints, open_obligations=open_obs
        )
        if sc < cfg.min_score:
            continue
        short_l = fq.rsplit(".", 1)[-1].lower()
        if any((h or "").lower() in short_l or (h or "").lower() in fq.lower() for h in hints):
            hint_hits += 1
        scored.append((sc, fq))

    scored.sort(key=lambda x: (-x[0], x[1]))
    top = scored[: max(1, cfg.max_names)]
    result.names = [fq for _, fq in top]
    result.scores = {fq: sc for sc, fq in top}
    result.hint_hits = hint_hits
    result.notes = (
        f"selected {len(result.names)} decls min_score={cfg.min_score} "
        f"max_names={cfg.max_names} hint_hits_in_pool={hint_hits}"
    )
    print(f"[saturday.accepted_select] {result.notes}")
    if result.names:
        preview = ", ".join(n.rsplit(".", 1)[-1] for n in result.names[:8])
        print(f"[saturday.accepted_select] top={preview}")
    return result


def select_from_loop_config(
    repo_root: Path,
    loop_cfg,
    *,
    rung_id: str,
    target: str,
    open_obligations: Optional[Sequence[str]] = None,
    module_excerpt: str = "",
    prior_errors: str = "",
    extra_text: str = "",
) -> AcceptedSelectResult:
    """Convenience: pull AcceptedSelectConfig off SaturdayLoopConfig."""
    cfg = getattr(loop_cfg, "accepted_select", None) or AcceptedSelectConfig()
    print(
        f"[saturday.accepted_select] select_from_loop_config "
        f"enabled={cfg.enabled} rung={rung_id}"
    )
    return select_accepted_declarations(
        repo_root,
        rung_id=rung_id,
        target=target,
        open_obligations=open_obligations,
        module_excerpt=module_excerpt,
        prior_errors=prior_errors,
        extra_text=extra_text,
        cfg=cfg,
    )
