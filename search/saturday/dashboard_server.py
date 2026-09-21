"""
Local saturday progress dashboard (stdlib only).

  satday dashboard
  open http://127.0.0.1:8765/

Tabs:
  - Progress: live auto-loop feed, rungs table, kill switch
  - Accepted tree: allowlisted declarations grouped by ladder rung
"""

from __future__ import annotations

import json
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict
from urllib.parse import urlparse

from search.saturday.control import clear_kill, engage_kill, load_control
from search.saturday.progress import (
    build_accepted_tree_snapshot,
    build_progress_snapshot,
)
from search.saturday.ui import announce


DASHBOARD_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"/>
<meta name="viewport" content="width=device-width, initial-scale=1"/>
<title>SATurday progress</title>
<style>
  :root {
    --bg: #0f1419;
    --panel: #1a2332;
    --text: #e7ecf3;
    --muted: #8b9bb4;
    --accent: #3d9cf0;
    --ok: #3ecf8e;
    --warn: #e6b84d;
    --bad: #e85d5d;
    --line: #2a3548;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: "IBM Plex Sans", "Segoe UI", sans-serif;
    background:
      radial-gradient(1200px 600px at 10% -10%, #1b2a44 0%, transparent 55%),
      radial-gradient(900px 500px at 100% 0%, #243018 0%, transparent 50%),
      var(--bg);
    color: var(--text);
    min-height: 100vh;
  }
  header {
    padding: 1.5rem 1.75rem 0.75rem;
    border-bottom: 1px solid var(--line);
  }
  header h1 {
    margin: 0;
    font-family: "IBM Plex Serif", Georgia, serif;
    font-weight: 600;
    font-size: 1.75rem;
    letter-spacing: 0.02em;
  }
  header p { margin: 0.4rem 0 0; color: var(--muted); max-width: 52rem; }
  .tabs {
    display: flex; gap: 0.4rem; margin-top: 1rem; flex-wrap: wrap;
  }
  .tabs button {
    background: transparent; color: var(--muted);
    border: 1px solid var(--line); border-radius: 8px;
    padding: 0.45rem 0.85rem; font-weight: 600; cursor: pointer;
  }
  .tabs button.active {
    background: var(--accent); color: #061018; border-color: var(--accent);
  }
  main { padding: 1.25rem 1.75rem 2.5rem; display: grid; gap: 1rem; }
  .panel { display: none; }
  .panel.active { display: grid; gap: 1rem; }
  .row { display: grid; gap: 1rem; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr)); }
  .card {
    background: color-mix(in srgb, var(--panel) 92%, black);
    border: 1px solid var(--line);
    border-radius: 10px;
    padding: 1rem 1.1rem;
  }
  .card h2 { margin: 0 0 0.6rem; font-size: 0.85rem; color: var(--muted); text-transform: uppercase; letter-spacing: 0.08em; }
  .big { font-size: 2rem; font-weight: 650; }
  .bar {
    height: 10px; background: #243044; border-radius: 999px; overflow: hidden; margin-top: 0.55rem;
  }
  .bar > span { display: block; height: 100%; background: linear-gradient(90deg, var(--accent), var(--ok)); }
  table { width: 100%; border-collapse: collapse; font-size: 0.92rem; }
  th, td { text-align: left; padding: 0.55rem 0.4rem; border-bottom: 1px solid var(--line); vertical-align: top; }
  th { color: var(--muted); font-weight: 550; font-size: 0.78rem; text-transform: uppercase; letter-spacing: 0.06em; }
  .pill {
    display: inline-block; padding: 0.12rem 0.45rem; border-radius: 999px;
    font-size: 0.75rem; border: 1px solid var(--line);
  }
  .ok { color: var(--ok); } .warn { color: var(--warn); } .bad { color: var(--bad); }
  .controls { display: flex; flex-wrap: wrap; gap: 0.6rem; align-items: center; }
  button, .btn {
    background: var(--accent); color: #061018; border: 0; border-radius: 8px;
    padding: 0.55rem 0.9rem; font-weight: 650; cursor: pointer;
  }
  button.danger { background: var(--bad); color: white; }
  button.ghost { background: transparent; color: var(--text); border: 1px solid var(--line); }
  input[type=text], input[type=search] {
    flex: 1; min-width: 220px; background: #101826; color: var(--text);
    border: 1px solid var(--line); border-radius: 8px; padding: 0.55rem 0.7rem;
  }
  .mono { font-family: "IBM Plex Mono", ui-monospace, monospace; font-size: 0.82rem; }
  .muted { color: var(--muted); }
  footer { padding: 0 1.75rem 1.5rem; color: var(--muted); font-size: 0.85rem; }

  /* Accepted declaration tree */
  .tree-toolbar { display: flex; flex-wrap: wrap; gap: 0.6rem; align-items: center; }
  .tree-meta { display: flex; flex-wrap: wrap; gap: 0.75rem; margin-top: 0.7rem; }
  .tree-meta .stat {
    background: #101826; border: 1px solid var(--line); border-radius: 8px;
    padding: 0.45rem 0.7rem; font-size: 0.85rem;
  }
  .dag-note {
    margin-top: 0.75rem; padding: 0.65rem 0.8rem;
    border-left: 3px solid var(--accent); background: #101826; font-size: 0.9rem;
  }
  details.rung-node, details.cluster-node {
    border: 1px solid var(--line); border-radius: 8px; margin: 0.45rem 0;
    background: #121a26;
  }
  details.rung-node > summary, details.cluster-node > summary {
    cursor: pointer; list-style: none; padding: 0.65rem 0.85rem;
    display: flex; flex-wrap: wrap; gap: 0.5rem; align-items: center;
  }
  details.rung-node > summary::-webkit-details-marker,
  details.cluster-node > summary::-webkit-details-marker { display: none; }
  details.rung-node > summary::before,
  details.cluster-node > summary::before {
    content: "+"; color: var(--muted); font-family: ui-monospace, monospace;
    width: 1rem; display: inline-block;
  }
  details[open].rung-node > summary::before,
  details[open].cluster-node > summary::before { content: "-"; }
  details.rung-node.role-bridge { border-color: #3a4a2a; }
  details.rung-node.role-setup { border-color: #2a3548; opacity: 0.95; }
  details.rung-node.role-main { border-left: 3px solid var(--accent); }
  .rung-body, .cluster-body { padding: 0 0.85rem 0.85rem 1.4rem; }
  .branch {
    margin-left: 0.35rem; padding-left: 0.85rem;
    border-left: 1px solid var(--line);
  }
  ul.decl-list {
    list-style: none; margin: 0.35rem 0 0; padding: 0;
    max-height: 320px; overflow: auto;
  }
  ul.decl-list li {
    padding: 0.28rem 0.2rem; border-bottom: 1px solid #1c2636;
    display: flex; flex-wrap: wrap; gap: 0.45rem; align-items: baseline;
  }
  ul.decl-list li .ns { color: var(--muted); font-size: 0.75rem; }
  .count-badge {
    margin-left: auto; font-family: ui-monospace, monospace;
    color: var(--muted); font-size: 0.8rem;
  }
  .empty-rung { color: var(--muted); font-style: italic; padding: 0.4rem 0; }
  .section-label {
    margin: 1rem 0 0.35rem; font-size: 0.78rem; letter-spacing: 0.08em;
    text-transform: uppercase; color: var(--muted);
  }
</style>
</head>
<body>
<header>
  <h1>SATurday</h1>
  <p>Live auto-loop feed, accepted-declaration ladder tree, critical Frontier pins, and kill switch.</p>
  <div class="tabs" role="tablist">
    <button type="button" class="active" data-tab="progress" id="tabProgress">Progress</button>
    <button type="button" data-tab="tree" id="tabTree">Accepted tree</button>
  </div>
</header>
<main>
  <div id="panel-progress" class="panel active">
    <section class="card" id="liveCard">
      <h2>Loop now</h2>
      <div id="liveSummary" class="mono"></div>
      <div class="row" style="margin-top:0.8rem" id="liveStats"></div>
      <div id="liveFeed" class="mono" style="margin-top:0.9rem;max-height:280px;overflow:auto;line-height:1.45"></div>
    </section>
    <section class="row" id="summary"></section>
    <section class="card">
      <h2>Kill switch</h2>
      <div class="controls">
        <input id="reason" type="text" placeholder="Reason for kill (optional)"/>
        <button class="danger" id="killBtn">Kill auto loop</button>
        <button class="ghost" id="unkillBtn">Clear kill</button>
        <span id="killState" class="mono"></span>
      </div>
      <p class="muted" style="margin:0.7rem 0 0">Auto checks this each wake. Equivalent CLI: <span class="mono">satday kill</span> / <span class="mono">satday unkill</span></p>
    </section>
    <section class="card">
      <h2>Rungs</h2>
      <div style="overflow-x:auto">
        <table>
          <thead>
            <tr>
              <th>Rung</th><th>Status</th><th>Pins</th><th>Open critical</th><th>Reflect</th>
            </tr>
          </thead>
          <tbody id="rungs"></tbody>
        </table>
      </div>
    </section>
    <section class="card">
      <h2>Recent sessions</h2>
      <div id="sessions" class="mono"></div>
    </section>
  </div>

  <div id="panel-tree" class="panel">
    <section class="card">
      <h2>Accepted declarations by rung</h2>
      <p class="muted" style="margin:0 0 0.75rem">
        Source: <span class="mono" id="treePath">scripts/accepted_declarations.txt</span>.
        Only merge_certified allowlist entries. R3/R4 show with zero decls so the ladder shape stays visible.
      </p>
      <div class="tree-toolbar">
        <input id="treeFilter" type="search" placeholder="Filter clusters or declaration names"/>
        <button class="ghost" type="button" id="expandRungs">Expand rungs</button>
        <button class="ghost" type="button" id="collapseAll">Collapse all</button>
        <button class="ghost" type="button" id="reloadTree">Reload tree</button>
      </div>
      <div class="tree-meta" id="treeMeta"></div>
      <div class="dag-note" id="dagNote"></div>
    </section>
    <section class="card">
      <h2>Ladder tree</h2>
      <div id="treeRoot"></div>
    </section>
  </div>
</main>
<footer>
  Progress refreshes every 2s from <span class="mono">/api/progress</span>.
  Tree loads from <span class="mono">/api/accepted-tree</span>.
  Driver: <span class="mono">satday auto --remote</span>.
</footer>
<script>
function esc(s) {
  return String(s || '').replace(/[&<>"'`]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;','`':'&#96;'}[c]));
}
function statusClass(st) {
  if (st === 'certified' || st === 'setup') return 'ok';
  if (st === 'active' || st === 'prose_accepted') return 'warn';
  return 'muted';
}

let treeCache = null;
let treeLoadedAt = 0;

function setTab(name) {
  console.log('[saturday.dashboard.ui] setTab', name);
  document.querySelectorAll('.tabs button').forEach(b => {
    b.classList.toggle('active', b.dataset.tab === name);
  });
  document.querySelectorAll('.panel').forEach(p => {
    p.classList.toggle('active', p.id === 'panel-' + name);
  });
  if (name === 'tree') {
    ensureTree(false);
  }
}

document.querySelectorAll('.tabs button').forEach(btn => {
  btn.addEventListener('click', () => setTab(btn.dataset.tab));
});

async function loadProgress() {
  console.log('[saturday.dashboard.ui] fetch /api/progress');
  const res = await fetch('/api/progress');
  const data = await res.json();
  const live = data.live || {};
  const stats = live.stats || {};
  const models = live.models || {};
  const runCls = live.running && !live.stale ? 'ok' : (live.stale ? 'warn' : 'bad');
  document.getElementById('liveSummary').innerHTML = `
    <div><span class="${runCls}">${live.running ? (live.stale ? 'STALE heartbeat' : 'AUTO RUNNING') : 'AUTO NOT RUNNING'}</span>
      · wake <strong>${live.wake || 0}</strong>
      · phase <strong>${esc(live.phase || 'unknown')}</strong>
      · pid ${esc(live.pid || '—')}
      · updated ${esc(live.updated_at || '—')}${live.age_seconds != null ? ' (' + live.age_seconds + 's ago)' : ''}</div>
    <div style="margin-top:0.35rem">${esc(live.detail || '')}</div>
    <div class="muted" style="margin-top:0.35rem">models formalize=${esc(models.formalize || '—')} prove=${esc(models.prove || '—')}</div>
  `;
  const ats = data.accepted_tree_summary || {};
  const byRung = ats.by_rung || {};
  document.getElementById('liveStats').innerHTML = `
    <div class="card"><h2>This auto run</h2>
      <div>accepted <span class="ok">${stats.accepted || 0}</span></div>
      <div>reverted <span class="bad">${stats.reverted || 0}</span></div>
      <div>rejected <span class="warn">${stats.rejected || 0}</span></div>
      <div>wakes ${stats.wakes || live.wake || 0}</div>
    </div>
    <div class="card"><h2>Workstreams</h2>
      ${Object.keys(live.workstreams || {}).length
        ? Object.entries(live.workstreams).map(([k,v]) =>
            `<div><strong>${esc(k)}</strong>: ${esc(v.phase)} — ${esc(v.detail)}</div>`).join('')
        : '<div class="muted">No workstream heartbeat yet</div>'}
    </div>
    <div class="card"><h2>Accepted decls</h2>
      <div class="big">${ats.total_declarations != null ? ats.total_declarations : '—'}</div>
      <div class="muted">allowlisted FQ names</div>
      <div class="mono muted" style="margin-top:0.35rem">R0=${byRung['r0-resolution-foundations']||0}
        R1=${byRung['r1-php-haken']||0}
        R2=${byRung['r2-width-machinery']||0}
        R5=${byRung['r5-cook-reckhow-bridge']||0}</div>
    </div>
  `;
  const events = live.events || [];
  document.getElementById('liveFeed').innerHTML = events.length
    ? events.slice(0, 40).map(e =>
        `<div>[${esc(e.ts)}] ${e.workstream ? '['+esc(e.workstream)+'] ' : ''}${esc(e.detail || e.phase || '')}</div>`
      ).join('')
    : '<div class="muted">No live events yet. If auto is running, restart it so it writes search/logs/saturday_live.json</div>';

  const sum = document.getElementById('summary');
  sum.innerHTML = `
    <div class="card"><h2>Rung certification</h2><div class="big">${data.rung_completion_pct}%</div>
      <div class="muted">${data.certified_count} / ${data.rung_count} certified</div>
      <div class="bar"><span style="width:${data.rung_completion_pct}%"></span></div></div>
    <div class="card"><h2>Critical pins</h2><div class="big">${data.critical_pin_pct}%</div>
      <div class="muted">${data.critical_total - data.critical_open} closed / ${data.critical_total} tracked</div>
      <div class="bar"><span style="width:${data.critical_pin_pct}%"></span></div></div>
    <div class="card"><h2>Toward P vs NP</h2><div style="font-size:1rem;line-height:1.45">${esc(data.toward_p_vs_np || '')}</div></div>
  `;
  const killed = data.control && data.control.killed;
  const ks = document.getElementById('killState');
  ks.className = 'mono ' + (killed ? 'bad' : 'ok');
  ks.textContent = killed
    ? ('KILLED: ' + (data.control.reason || data.control.source || 'yes'))
    : 'Running allowed';
  const body = document.getElementById('rungs');
  body.innerHTML = (data.rungs || []).map(r => {
    const st = r.status === 'certified' ? 'ok' : (r.status === 'active' || r.status === 'prose_accepted' ? 'warn' : 'muted');
    const pins = (r.open_critical_pins || []).join(', ') || (r.status === 'certified' ? '(none)' : '—');
    const ref = r.reflect || {};
    const declN = (byRung[r.rung_id] != null) ? byRung[r.rung_id] : '—';
    return `<tr>
      <td><strong>${esc(r.title)}</strong><div class="mono muted">${esc(r.rung_id)}</div>
        <div class="muted">pin progress ${r.pin_progress_pct}% · accepted decls ${declN}</div></td>
      <td><span class="pill ${st}">${esc(r.status)}</span>${r.paused ? ' <span class="pill bad">paused</span>' : ''}
        ${r.force_action ? ` <span class="pill warn">force:${esc(r.force_action)}</span>` : ''}</td>
      <td class="mono">${r.pin_progress_pct}%</td>
      <td class="mono">${esc(pins)}</td>
      <td class="mono muted">noProg=${ref.wakes_without_obligation_progress || 0}
        dup=${ref.consecutive_near_duplicates || 0}
        err=${ref.consecutive_same_error || 0}</td>
    </tr>`;
  }).join('');
  const sess = document.getElementById('sessions');
  sess.innerHTML = (data.recent_sessions || []).slice().reverse().map(s =>
    `<div>${esc(s.ts || s.timestamp || '')} · ${esc(s.workstream || '')} ${esc(s.rung)} / ${esc(s.action_type)} -> ${esc(s.result)} · ${esc((s.notes || '').slice(0,120))}</div>`
  ).join('') || '<div class="muted">No sessions yet</div>';
}

function filterMatches(text, q) {
  if (!q) return true;
  return String(text || '').toLowerCase().includes(q);
}

function renderTree(data, filterQ) {
  console.log('[saturday.dashboard.ui] renderTree filter=', filterQ || '(none)');
  const q = (filterQ || '').trim().toLowerCase();
  const summary = data.summary || {};
  const dag = data.ladder_dag || {};
  document.getElementById('treePath').textContent = summary.decls_path || 'scripts/accepted_declarations.txt';
  document.getElementById('treeMeta').innerHTML = `
    <div class="stat"><strong>${summary.total_declarations || 0}</strong> declarations</div>
    <div class="stat"><strong>${summary.rung_count_with_decls || 0}</strong> rungs with decls</div>
    <div class="stat mono">loaded ${new Date(treeLoadedAt).toLocaleTimeString()}</div>
  `;
  document.getElementById('dagNote').textContent =
    (dag.note || '') + ' Main climb: ' + (dag.main_climb || []).join(' -> ') +
    '. Bridge: ' + (dag.bridge || 'r5');

  const rungs = data.rungs || [];
  const setup = rungs.filter(r => r.role === 'setup');
  const main = rungs.filter(r => r.role === 'main');
  const bridge = rungs.filter(r => r.role === 'bridge');
  const other = rungs.filter(r => !['setup','main','bridge'].includes(r.role));

  function renderDecl(d) {
    return `<li>
      <span class="mono">${esc(d.short)}</span>
      <span class="ns mono">${esc(d.namespace)}</span>
    </li>`;
  }

  function renderCluster(c) {
    const decls = (c.declarations || []).filter(d =>
      filterMatches(d.fq, q) || filterMatches(d.short, q) || filterMatches(c.title, q)
    );
    if (q && !decls.length && !filterMatches(c.title, q)) return '';
    const showDecls = q ? decls : (c.declarations || []);
    if (q && !showDecls.length) return '';
    return `<details class="cluster-node">
      <summary>
        <span>${esc(c.title)}</span>
        <span class="count-badge">${showDecls.length} decl${showDecls.length===1?'':'s'}</span>
      </summary>
      <div class="cluster-body">
        <ul class="decl-list">${showDecls.map(renderDecl).join('')}</ul>
      </div>
    </details>`;
  }

  function renderRung(r) {
    const clustersHtml = (r.clusters || []).map(renderCluster).filter(Boolean).join('');
    const rungHit = filterMatches(r.title, q) || filterMatches(r.rung_id, q) || filterMatches(r.status, q);
    if (q && !clustersHtml && !rungHit && r.decl_count > 0) return '';
    if (q && r.decl_count === 0 && !rungHit) return '';
    const body = r.decl_count === 0
      ? `<div class="empty-rung">No accepted declarations yet (rung status: ${esc(r.status)}).</div>`
      : `<div class="branch">${clustersHtml || '<div class="empty-rung">No clusters match filter.</div>'}</div>`;
    return `<details class="rung-node role-${esc(r.role)}" data-rung="${esc(r.rung_id)}" ${q ? 'open' : ''}>
      <summary>
        <strong>${esc(r.title)}</strong>
        <span class="pill ${statusClass(r.status)}">${esc(r.status)}</span>
        <span class="pill muted">${esc(r.role)}</span>
        <span class="count-badge">${r.decl_count} decls · ${r.cluster_count} clusters</span>
      </summary>
      <div class="rung-body">${body}</div>
    </details>`;
  }

  function block(label, items) {
    if (!items.length) return '';
    const html = items.map(renderRung).filter(Boolean).join('');
    if (!html) return '';
    return `<div class="section-label">${esc(label)}</div>${html}`;
  }

  document.getElementById('treeRoot').innerHTML =
    block('Setup', setup) +
    block('Main climb (R0 to R4)', main) +
    block('Side bridge (joins at summit)', bridge) +
    block('Other', other);
}

async function ensureTree(force) {
  const age = Date.now() - treeLoadedAt;
  if (!force && treeCache && age < 30000) {
    console.log('[saturday.dashboard.ui] reuse tree cache age_ms=', age);
    renderTree(treeCache, document.getElementById('treeFilter').value);
    return;
  }
  console.log('[saturday.dashboard.ui] fetch /api/accepted-tree force=', force);
  const res = await fetch('/api/accepted-tree');
  treeCache = await res.json();
  treeLoadedAt = Date.now();
  console.log('[saturday.dashboard.ui] tree loaded total=',
    (treeCache.summary && treeCache.summary.total_declarations) || 0);
  renderTree(treeCache, document.getElementById('treeFilter').value);
}

document.getElementById('treeFilter').addEventListener('input', (e) => {
  if (treeCache) renderTree(treeCache, e.target.value);
});
document.getElementById('expandRungs').onclick = () => {
  document.querySelectorAll('#treeRoot details.rung-node').forEach(d => { d.open = true; });
};
document.getElementById('collapseAll').onclick = () => {
  document.querySelectorAll('#treeRoot details').forEach(d => { d.open = false; });
};
document.getElementById('reloadTree').onclick = () => ensureTree(true);

document.getElementById('killBtn').onclick = async () => {
  const reason = document.getElementById('reason').value || 'dashboard kill';
  console.log('[saturday.dashboard.ui] kill', reason);
  await fetch('/api/kill', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({reason})});
  loadProgress();
};
document.getElementById('unkillBtn').onclick = async () => {
  console.log('[saturday.dashboard.ui] unkill');
  await fetch('/api/unkill', {method:'POST'});
  loadProgress();
};

loadProgress();
setInterval(loadProgress, 2000);
</script>
</body>
</html>
"""


class _DashboardHandler(BaseHTTPRequestHandler):
    repo_root: Path = Path(".")

    def log_message(self, fmt: str, *args: Any) -> None:
        print(f"[saturday.dashboard] {self.address_string()} {fmt % args}")

    def _send(self, code: int, body: bytes, content_type: str) -> None:
        self.send_response(code)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, code: int, payload: Dict[str, Any]) -> None:
        raw = json.dumps(payload, indent=2).encode("utf-8")
        self._send(code, raw, "application/json; charset=utf-8")

    def do_GET(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        print(f"[saturday.dashboard] GET path={parsed.path}")
        if parsed.path in {"/", "/index.html"}:
            self._send(200, DASHBOARD_HTML.encode("utf-8"), "text/html; charset=utf-8")
            return
        if parsed.path == "/api/progress":
            snap = build_progress_snapshot(self.repo_root)
            self._json(200, snap)
            return
        if parsed.path == "/api/accepted-tree":
            print("[saturday.dashboard] building accepted-tree snapshot")
            tree = build_accepted_tree_snapshot(self.repo_root)
            print(
                f"[saturday.dashboard] accepted-tree total="
                f"{tree.get('summary', {}).get('total_declarations')}"
            )
            self._json(200, tree)
            return
        if parsed.path == "/api/control":
            self._json(200, load_control(self.repo_root).to_dict())
            return
        self._json(404, {"error": "not found", "path": parsed.path})

    def do_POST(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
        print(f"[saturday.dashboard] POST path={parsed.path}")
        length = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(length) if length else b"{}"
        try:
            payload = json.loads(raw.decode("utf-8") or "{}")
        except json.JSONDecodeError:
            payload = {}
        if parsed.path == "/api/kill":
            reason = str(payload.get("reason") or "dashboard kill")
            state = engage_kill(self.repo_root, reason, source="dashboard")
            announce(f"Dashboard kill switch engaged: {reason}")
            self._json(200, state.to_dict())
            return
        if parsed.path == "/api/unkill":
            state = clear_kill(self.repo_root)
            announce("Dashboard cleared kill switch")
            self._json(200, state.to_dict())
            return
        self._json(404, {"error": "not found", "path": parsed.path})


def run_dashboard(
    repo_root: Path,
    host: str = "127.0.0.1",
    port: int = 8765,
) -> None:
    """Block forever serving the dashboard."""
    handler = _DashboardHandler
    handler.repo_root = Path(repo_root)
    server = ThreadingHTTPServer((host, port), handler)
    url = f"http://{host}:{port}/"
    announce(f"Dashboard listening at {url}")
    print(f"[saturday.dashboard] serving {url} repo={repo_root}")
    print(
        "[saturday.dashboard] routes: / /api/progress /api/accepted-tree "
        "/api/control /api/kill /api/unkill"
    )
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        announce("Dashboard stopped")
        server.shutdown()
