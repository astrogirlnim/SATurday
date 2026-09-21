"""
Parse scripts/accepted_declarations.txt into a rung-relative tree for the dashboard.

Section comments (# R0:, # R2 item 2 cluster N:, # Smoke lemmas, ...) are the
only structured mapping from allowlisted FQ Lean names onto ladder rungs.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional

from search.saturday.status import MAIN_CLIMB, RUNG_TITLES

# Map comment rung tags onto ladder ids used by status / progress.
RUNG_TAG_TO_ID = {
    "smoke": "smoke-setup",
    "r0": "r0-resolution-foundations",
    "r1": "r1-php-haken",
    "r2": "r2-width-machinery",
    "r3": "r3-stronger-systems",
    "r4": "r4-frontier",
    "r5": "r5-cook-reckhow-bridge",
}

# Climb order for the tree (smoke first, then main climb, then R5 bridge).
TREE_RUNG_ORDER = [
    "smoke-setup",
    "r0-resolution-foundations",
    "r1-php-haken",
    "r2-width-machinery",
    "r3-stronger-systems",
    "r4-frontier",
    "r5-cook-reckhow-bridge",
]

_RUNG_HEADER_RE = re.compile(
    r"^#\s*(Smoke\b(?:\s+lemmas?)?|R([0-5]))\b(.*)$",
    re.IGNORECASE,
)
_FILE_PREAMBLE_RE = re.compile(
    r"^#\s*(Accepted declarations|One fully qualified|A declaration may)\b",
    re.IGNORECASE,
)
_PAREN_ONLY_RE = re.compile(r"^#\s*\(.*\)\s*$")


@dataclass
class AcceptedDecl:
    """One allowlisted Lean declaration."""

    fq: str
    short: str
    namespace: str


@dataclass
class AcceptedCluster:
    """Comment-delimited cluster under one rung."""

    title: str
    declarations: List[AcceptedDecl] = field(default_factory=list)

    @property
    def decl_count(self) -> int:
        return len(self.declarations)


@dataclass
class AcceptedRungNode:
    """Rung node in the accepted-declaration tree."""

    rung_id: str
    rung_tag: str
    title: str
    role: str  # setup | main | bridge
    status: str
    clusters: List[AcceptedCluster] = field(default_factory=list)

    @property
    def decl_count(self) -> int:
        return sum(c.decl_count for c in self.clusters)


def _default_decls_path(repo_root: Path) -> Path:
    return Path(repo_root) / "scripts" / "accepted_declarations.txt"


def _role_for(rung_id: str) -> str:
    if rung_id == "smoke-setup":
        return "setup"
    if rung_id == "r5-cook-reckhow-bridge":
        return "bridge"
    if rung_id in MAIN_CLIMB:
        return "main"
    return "other"


def _title_for(rung_id: str) -> str:
    if rung_id == "smoke-setup":
        return "Smoke lemmas (Lean setup)"
    return RUNG_TITLES.get(rung_id, rung_id)


def _split_fq(fq: str) -> AcceptedDecl:
    parts = fq.rsplit(".", 1)
    short = parts[-1] if parts else fq
    namespace = parts[0] if len(parts) == 2 else ""
    return AcceptedDecl(fq=fq, short=short, namespace=namespace)


def _normalize_cluster_title(raw: str) -> str:
    title = raw.strip()
    if title.startswith(":"):
        title = title[1:].strip()
    return title or "(untitled cluster)"


def _parse_rung_header(line: str) -> Optional[tuple[str, str]]:
    """Return (rung_id, cluster_title) when line opens a rung section."""
    m = _RUNG_HEADER_RE.match(line)
    if not m:
        return None
    head = m.group(1)
    digit = m.group(2)
    rest = m.group(3) or ""
    if digit is not None:
        tag = f"r{digit}"
    else:
        tag = "smoke"
    rung_id = RUNG_TAG_TO_ID[tag]
    # Smoke keeps the full header; Rn uses the remainder after the tag.
    if tag == "smoke":
        cluster = _normalize_cluster_title(f"{head}{rest}".strip())
    elif rest.strip():
        cluster = _normalize_cluster_title(rest)
    else:
        cluster = head.strip()
    return rung_id, cluster


def parse_accepted_declarations_file(
    decls_path: Path,
    *,
    verbose: bool = False,
) -> Dict[str, AcceptedRungNode]:
    """
    Walk the allowlist file once and bucket declarations by rung + cluster.

    Non-rung comment lines under an open rung start a new cluster, unless the
    current cluster is still empty (then the note is folded into its title) or
    the line is only a parenthetical footnote.
    """
    print(f"[saturday.accepted_tree] parse start path={decls_path}")
    nodes: Dict[str, AcceptedRungNode] = {}
    current_id: Optional[str] = None
    current_cluster: Optional[AcceptedCluster] = None
    line_no = 0
    decl_total = 0
    cluster_total = 0

    def ensure_rung(rung_id: str) -> AcceptedRungNode:
        if rung_id not in nodes:
            tag = {
                "smoke-setup": "smoke",
                "r0-resolution-foundations": "r0",
                "r1-php-haken": "r1",
                "r2-width-machinery": "r2",
                "r3-stronger-systems": "r3",
                "r4-frontier": "r4",
                "r5-cook-reckhow-bridge": "r5",
            }.get(rung_id, rung_id)
            nodes[rung_id] = AcceptedRungNode(
                rung_id=rung_id,
                rung_tag=tag,
                title=_title_for(rung_id),
                role=_role_for(rung_id),
                status="unknown",
                clusters=[],
            )
            if verbose:
                print(f"[saturday.accepted_tree] created rung node id={rung_id}")
        return nodes[rung_id]

    def open_cluster(rung_id: str, title: str) -> AcceptedCluster:
        nonlocal current_cluster, cluster_total
        node = ensure_rung(rung_id)
        cluster = AcceptedCluster(title=title, declarations=[])
        node.clusters.append(cluster)
        current_cluster = cluster
        cluster_total += 1
        if verbose:
            print(
                f"[saturday.accepted_tree] open cluster rung={rung_id} "
                f"n={cluster_total} title={title[:100]!r}"
            )
        return cluster

    if not decls_path.is_file():
        print(f"[saturday.accepted_tree] missing decls file: {decls_path}")
        return nodes

    for raw in decls_path.read_text(encoding="utf-8").splitlines():
        line_no += 1
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#"):
            if _FILE_PREAMBLE_RE.match(line):
                if verbose:
                    print(f"[saturday.accepted_tree] skip preamble L{line_no}")
                continue
            parsed = _parse_rung_header(line)
            if parsed is not None:
                current_id, cluster_title = parsed
                open_cluster(current_id, cluster_title)
                continue
            if current_id is None:
                if verbose:
                    print(
                        f"[saturday.accepted_tree] orphan comment L{line_no}: "
                        f"{line[:80]!r}"
                    )
                continue
            note = line.lstrip("#").strip()
            if not note:
                continue
            # Fold footnotes / empty-cluster notes instead of hollow nodes.
            if current_cluster is not None and (
                _PAREN_ONLY_RE.match(line) or current_cluster.decl_count == 0
            ):
                current_cluster.title = f"{current_cluster.title} — {note}".strip()
                if verbose:
                    print(
                        f"[saturday.accepted_tree] fold note L{line_no} into "
                        f"cluster={current_cluster.title[:80]!r}"
                    )
                continue
            open_cluster(current_id, note)
            continue

        # Declaration line.
        if current_id is None:
            print(
                f"[saturday.accepted_tree] decl before any section L{line_no}: {line}"
            )
            current_id = "smoke-setup"
            open_cluster(current_id, "unsectioned")
        if current_cluster is None:
            open_cluster(current_id, "unsectioned")
        decl = _split_fq(line)
        current_cluster.declarations.append(decl)
        decl_total += 1

    # Drop hollow clusters that never received a declaration.
    for node in nodes.values():
        before = len(node.clusters)
        node.clusters = [c for c in node.clusters if c.decl_count > 0]
        dropped = before - len(node.clusters)
        if dropped and verbose:
            print(
                f"[saturday.accepted_tree] dropped {dropped} empty clusters "
                f"on {node.rung_id}"
            )

    print(
        f"[saturday.accepted_tree] parse done lines={line_no} "
        f"decls={decl_total} clusters={sum(len(n.clusters) for n in nodes.values())} "
        f"rungs={len(nodes)}"
    )
    return nodes


def build_accepted_declaration_tree(
    repo_root: Path,
    *,
    decls_path: Optional[Path] = None,
    rung_statuses: Optional[Dict[str, str]] = None,
    verbose: bool = False,
    with_statements: bool = True,
) -> Dict[str, Any]:
    """
    Build the JSON tree for /api/accepted-tree and the dashboard Tree tab.

    Empty rungs (R3/R4) are still included so the ladder shape is visible.
    When with_statements is true, each declaration is enriched with Lean docstring
    prose and the proposition / type formula from theory sources.
    """
    repo_root = Path(repo_root)
    path = Path(decls_path) if decls_path else _default_decls_path(repo_root)
    print(
        f"[saturday.accepted_tree] build tree repo={repo_root} "
        f"decls={path} status_keys={list((rung_statuses or {}).keys())} "
        f"with_statements={with_statements}"
    )
    parsed = parse_accepted_declarations_file(path, verbose=verbose)
    statuses = rung_statuses or {}

    rung_payload: List[Dict[str, Any]] = []
    total = 0
    all_decls: List[Dict[str, Any]] = []
    for rung_id in TREE_RUNG_ORDER:
        node = parsed.get(rung_id) or AcceptedRungNode(
            rung_id=rung_id,
            rung_tag={
                "smoke-setup": "smoke",
                "r0-resolution-foundations": "r0",
                "r1-php-haken": "r1",
                "r2-width-machinery": "r2",
                "r3-stronger-systems": "r3",
                "r4-frontier": "r4",
                "r5-cook-reckhow-bridge": "r5",
            }.get(rung_id, rung_id),
            title=_title_for(rung_id),
            role=_role_for(rung_id),
            status=statuses.get(
                rung_id, "proposed" if rung_id != "smoke-setup" else "n/a"
            ),
            clusters=[],
        )
        if rung_id != "smoke-setup":
            node.status = statuses.get(rung_id, node.status or "unknown")
        else:
            node.status = "setup"
        clusters_out: List[Dict[str, Any]] = []
        for cluster in node.clusters:
            decls_out = [asdict(d) for d in cluster.declarations]
            all_decls.extend(decls_out)
            clusters_out.append(
                {
                    "title": cluster.title,
                    "decl_count": cluster.decl_count,
                    "declarations": decls_out,
                }
            )
        count = sum(c["decl_count"] for c in clusters_out)
        total += count
        rung_payload.append(
            {
                "rung_id": node.rung_id,
                "rung_tag": node.rung_tag,
                "title": node.title,
                "role": node.role,
                "status": node.status,
                "decl_count": count,
                "cluster_count": len(clusters_out),
                "clusters": clusters_out,
            }
        )

    for rung_id, node in parsed.items():
        if rung_id in TREE_RUNG_ORDER:
            continue
        print(f"[saturday.accepted_tree] unexpected rung bucket id={rung_id}")
        count = node.decl_count
        total += count
        decls_lists: List[Dict[str, Any]] = []
        clusters_out = []
        for c in node.clusters:
            decls_out = [asdict(d) for d in c.declarations]
            all_decls.extend(decls_out)
            decls_lists.append(decls_out)
            clusters_out.append(
                {
                    "title": c.title,
                    "decl_count": c.decl_count,
                    "declarations": decls_out,
                }
            )
        rung_payload.append(
            {
                "rung_id": node.rung_id,
                "rung_tag": node.rung_tag,
                "title": node.title,
                "role": node.role,
                "status": statuses.get(rung_id, node.status),
                "decl_count": count,
                "cluster_count": len(node.clusters),
                "clusters": clusters_out,
            }
        )

    stmt_found = 0
    stmt_missing = 0
    if with_statements and all_decls:
        from search.saturday.lean_statements import attach_statements

        print(
            f"[saturday.accepted_tree] attaching Lean prose/formula "
            f"to {len(all_decls)} decls"
        )
        stmt_found, stmt_missing = attach_statements(repo_root, all_decls)

    try:
        rel = str(path.relative_to(repo_root))
    except ValueError:
        rel = str(path)

    summary = {
        "decls_path": rel,
        "total_declarations": total,
        "rung_count_with_decls": sum(1 for r in rung_payload if r["decl_count"] > 0),
        "by_rung": {r["rung_id"]: r["decl_count"] for r in rung_payload},
        "statements_found": stmt_found,
        "statements_missing": stmt_missing,
    }
    print(
        f"[saturday.accepted_tree] summary total={total} "
        f"rungs_with_decls={summary['rung_count_with_decls']} "
        f"stmts_found={stmt_found} stmts_missing={stmt_missing} "
        f"by_rung={summary['by_rung']}"
    )
    return {
        "summary": summary,
        "ladder_dag": {
            "main_climb": list(MAIN_CLIMB),
            "bridge": "r5-cook-reckhow-bridge",
            "note": (
                "R0->R1->R2->R3->R4->summit; R5 joins after R1 at the summit edge"
            ),
        },
        "rungs": rung_payload,
    }


def build_accepted_tree_summary(repo_root: Path) -> Dict[str, Any]:
    """Lightweight counts only (safe to embed in the 2s progress poll)."""
    repo_root = Path(repo_root)
    path = _default_decls_path(repo_root)
    print(f"[saturday.accepted_tree] summary-only parse path={path}")
    parsed = parse_accepted_declarations_file(path, verbose=False)
    by_rung = {rid: 0 for rid in TREE_RUNG_ORDER}
    for rid, node in parsed.items():
        by_rung[rid] = node.decl_count
    for rid in TREE_RUNG_ORDER:
        by_rung.setdefault(rid, 0)
    total = sum(by_rung.values())
    try:
        rel = str(path.relative_to(repo_root))
    except ValueError:
        rel = str(path)
    summary = {
        "decls_path": rel,
        "total_declarations": total,
        "rung_count_with_decls": sum(1 for n in by_rung.values() if n > 0),
        "by_rung": by_rung,
        "ladder_dag": {
            "main_climb": list(MAIN_CLIMB),
            "bridge": "r5-cook-reckhow-bridge",
            "note": (
                "R0->R1->R2->R3->R4->summit; R5 joins after R1 at the summit edge"
            ),
        },
    }
    print(f"[saturday.accepted_tree] summary-only total={total}")
    return summary
