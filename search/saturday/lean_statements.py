"""
Index Lean declaration prose and type formulas for the accepted-tree dashboard.

Scans theory/Theory/**/*.lean once (mtime-cached; not Mathlib), tracks namespace
stacks, and maps fully qualified names to:
  - prose: /-- ... -/ docstring (mathematical English)
  - formula: the type after the final ':' (Lean equation / proposition)
  - signature: full header without the proof body
"""

from __future__ import annotations

import re
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

_DECL_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"((?:[A-Za-z_][\w']*\.)*)([A-Za-z_][\w']*)"
)
_NS_OPEN_RE = re.compile(r"^namespace\s+(\S+)\s*$")
_NS_END_RE = re.compile(r"^end(?:\s+(\S+))?\s*$")
_DOC_RE = re.compile(r"/--(.*?)-/", re.DOTALL)
_ATTR_ONLY_RE = re.compile(r"^@\[.*\]\s*$")

_CACHE: Dict[str, "LeanStatementIndex"] = {}


@dataclass
class LeanStatement:
    """Prose + formula extracted from a Lean source declaration."""

    fq: str
    kind: str
    prose: str
    formula: str
    signature: str
    file: str
    line: int

    def to_dict(self) -> Dict[str, object]:
        return asdict(self)


@dataclass
class LeanStatementIndex:
    """FQ name -> statement payload."""

    by_fq: Dict[str, LeanStatement]
    scanned_files: int
    matched: int
    built_at: float
    theory_root: str

    def get(self, fq: str) -> Optional[LeanStatement]:
        return self.by_fq.get(fq)


def _project_theory_src(repo_root: Path) -> Path:
    return Path(repo_root) / "theory" / "Theory"


def _theory_mtime_key(theory_src: Path) -> str:
    """Cheap invalidation key: count + max mtime of project .lean files."""
    n = 0
    newest = 0.0
    if not theory_src.is_dir():
        return "missing"
    for path in theory_src.rglob("*.lean"):
        n += 1
        try:
            newest = max(newest, path.stat().st_mtime)
        except OSError:
            continue
    return f"{n}:{newest:.3f}"


def _iter_project_lean_files(repo_root: Path) -> List[Path]:
    """Lean sources owned by SATurday (theory/Theory only; not Mathlib)."""
    root = _project_theory_src(repo_root)
    if not root.is_dir():
        print(f"[saturday.lean_statements] project lean root missing: {root}")
        return []
    files = sorted(root.rglob("*.lean"))
    print(f"[saturday.lean_statements] project lean files={len(files)} under {root}")
    return files


def _collapse_ws(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip())


def _extract_formula(header: str) -> str:
    """Pull the proposition / type from a Lean declaration header."""
    h = _collapse_ws(header)
    if ":=" in h:
        h = h.split(":=", 1)[0].strip()
    m = re.search(r"[\)\}\]]\s*:\s*(.+)$", h)
    if m:
        return m.group(1).strip()
    m = re.search(r"\s:\s*(.+)$", h)
    if m:
        return m.group(1).strip()
    return h


def _preceding_doc(lines: List[str], decl_idx: int) -> str:
    """Return /-- ... -/ immediately above decl_idx, skipping blank/attr lines."""
    k = decl_idx - 1
    while k >= 0:
        s = lines[k].strip()
        if s == "" or _ATTR_ONLY_RE.match(s) or (
            s.startswith("--") and not s.startswith("/--")
        ):
            k -= 1
            continue
        break
    if k < 0 or "-/" not in lines[k]:
        return ""
    end_k = k
    while k >= 0 and "/--" not in lines[k]:
        k -= 1
    if k < 0:
        return ""
    chunk = "\n".join(lines[k : end_k + 1])
    m = _DOC_RE.search(chunk)
    if not m:
        return ""
    return _collapse_ws(m.group(1))


def _read_header(lines: List[str], start: int) -> Tuple[str, int]:
    """Collect declaration header lines until := / where / complete type."""
    buf = lines[start].strip()
    j = start
    depth = (
        buf.count("(")
        - buf.count(")")
        + buf.count("{")
        - buf.count("}")
        + buf.count("[")
        - buf.count("]")
    )
    while j + 1 < len(lines):
        if ":=" in buf or re.search(r"\bwhere\b", buf):
            break
        nxt = lines[j + 1].strip()
        if not nxt:
            j += 1
            continue
        if nxt.startswith("--") and not nxt.startswith("/--"):
            j += 1
            continue
        if _DECL_START_RE.match(nxt) and depth <= 0 and ":" in buf:
            break
        if depth <= 0 and ":" in buf and (
            nxt.startswith("by ")
            or nxt == "by"
            or nxt.startswith("| ")
            or nxt.startswith("· ")
        ):
            break
        j += 1
        buf += " " + nxt
        depth = (
            buf.count("(")
            - buf.count(")")
            + buf.count("{")
            - buf.count("}")
            + buf.count("[")
            - buf.count("]")
        )
        if ":=" in buf or re.search(r"\bwhere\b", buf):
            break
        if j - start > 40:
            break
    header = buf.split(":=", 1)[0].strip()
    header = re.split(r"\bwhere\b", header, maxsplit=1)[0].strip()
    return header, j


def _pop_namespace(stack: List[str], end_name: Optional[str]) -> None:
    if not stack:
        return
    if end_name is None:
        stack.pop()
        return
    if end_name in stack:
        while stack and stack[-1] != end_name:
            stack.pop()
        if stack:
            stack.pop()
        return
    dotted = ".".join(stack)
    if dotted.endswith(end_name) or end_name == dotted:
        for _ in end_name.split("."):
            if stack:
                stack.pop()


def scan_lean_statements(repo_root: Path) -> LeanStatementIndex:
    """Walk theory/Theory and index declaration prose/formulas by FQ name."""
    t0 = time.time()
    repo_root = Path(repo_root)
    theory_src = _project_theory_src(repo_root)
    by_fq: Dict[str, LeanStatement] = {}
    scanned = 0
    print(f"[saturday.lean_statements] scan start theory_src={theory_src}")

    for path in _iter_project_lean_files(repo_root):
        scanned += 1
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            print(f"[saturday.lean_statements] skip {path}: {exc}")
            continue
        lines = text.splitlines()
        ns_stack: List[str] = []
        try:
            rel = str(path.relative_to(repo_root))
        except ValueError:
            rel = str(path)

        i = 0
        while i < len(lines):
            s = lines[i].strip()
            m_open = _NS_OPEN_RE.match(s)
            if m_open:
                for part in m_open.group(1).split("."):
                    if part:
                        ns_stack.append(part)
                i += 1
                continue
            m_end = _NS_END_RE.match(s)
            if m_end:
                _pop_namespace(ns_stack, m_end.group(1))
                i += 1
                continue

            m_decl = _DECL_START_RE.match(s)
            if not m_decl:
                i += 1
                continue

            kind = m_decl.group(1)
            prefix = m_decl.group(2) or ""
            name = m_decl.group(3)
            dotted = f"{prefix}{name}"
            prose = _preceding_doc(lines, i)
            header, last = _read_header(lines, i)
            formula = _extract_formula(header)
            ns = ".".join(ns_stack)
            fq = f"{ns}.{dotted}" if ns else dotted
            by_fq[fq] = LeanStatement(
                fq=fq,
                kind=kind,
                prose=prose,
                formula=formula,
                signature=_collapse_ws(header),
                file=rel,
                line=i + 1,
            )
            i = last + 1

        print(
            f"[saturday.lean_statements] file={rel} decls_so_far={len(by_fq)}"
        )

    elapsed = time.time() - t0
    print(
        f"[saturday.lean_statements] scan done files={scanned} "
        f"indexed={len(by_fq)} elapsed_s={elapsed:.2f}"
    )
    return LeanStatementIndex(
        by_fq=by_fq,
        scanned_files=scanned,
        matched=len(by_fq),
        built_at=time.time(),
        theory_root=str(theory_src),
    )


def load_lean_statement_index(
    repo_root: Path,
    *,
    force: bool = False,
) -> LeanStatementIndex:
    """Return a mtime-cached statement index for theory/Theory."""
    repo_root = Path(repo_root)
    theory_src = _project_theory_src(repo_root)
    key = _theory_mtime_key(theory_src)
    cache_key = f"{repo_root}:{key}"
    if not force and cache_key in _CACHE:
        print(f"[saturday.lean_statements] cache hit key={key}")
        return _CACHE[cache_key]
    stale = [k for k in _CACHE if k.startswith(f"{repo_root}:")]
    for k in stale:
        del _CACHE[k]
    print(f"[saturday.lean_statements] cache miss key={key} force={force}")
    idx = scan_lean_statements(repo_root)
    _CACHE[cache_key] = idx
    return idx


def _short_name(fq: str) -> str:
    return fq.rsplit(".", 1)[-1]


def build_short_index(
    index: LeanStatementIndex,
) -> Dict[str, List[LeanStatement]]:
    """Map short Lean name -> candidate statements (usually length 1)."""
    out: Dict[str, List[LeanStatement]] = {}
    for stmt in index.by_fq.values():
        out.setdefault(_short_name(stmt.fq), []).append(stmt)
    return out


def lookup_statement(
    index: LeanStatementIndex,
    fq: str,
    *,
    short_index: Optional[Dict[str, List[LeanStatement]]] = None,
) -> Optional[LeanStatement]:
    """Resolve an accepted FQ name against the index (with light fallbacks)."""
    hit = index.by_fq.get(fq)
    if hit:
        return hit
    short = _short_name(fq)
    bucket = (short_index or build_short_index(index)).get(short) or []
    if not bucket:
        return None
    for stmt in bucket:
        if stmt.fq == fq or fq.endswith(stmt.fq) or stmt.fq.endswith(fq):
            return stmt
    if len(bucket) == 1:
        print(f"[saturday.lean_statements] soft-match fq={fq} -> {bucket[0].fq}")
        return bucket[0]
    best: Optional[LeanStatement] = None
    best_score = -1
    fq_parts = fq.split(".")
    for stmt in bucket:
        sp = stmt.fq.split(".")
        score = 0
        for a, b in zip(reversed(fq_parts), reversed(sp)):
            if a != b:
                break
            score += 1
        if score > best_score:
            best_score = score
            best = stmt
    if best is not None and best_score >= 1:
        return best
    return None


def attach_statements(
    repo_root: Path,
    declarations: List[Dict[str, Any]],
) -> Tuple[int, int]:
    """
    Mutate declaration dicts in place with prose/formula fields.

    Returns (found, missing).
    """
    index = load_lean_statement_index(repo_root)
    short_index = build_short_index(index)
    found = 0
    missing = 0
    for decl in declarations:
        fq = str(decl.get("fq") or "")
        stmt = lookup_statement(index, fq, short_index=short_index)
        if stmt is None:
            missing += 1
            decl["prose"] = ""
            decl["formula"] = ""
            decl["kind"] = ""
            decl["source"] = ""
            continue
        found += 1
        decl["prose"] = stmt.prose
        decl["formula"] = stmt.formula
        decl["kind"] = stmt.kind
        decl["source"] = f"{stmt.file}:{stmt.line}"
        decl["signature"] = stmt.signature
    print(
        f"[saturday.lean_statements] attach found={found} missing={missing} "
        f"of={len(declarations)}"
    )
    return found, missing
