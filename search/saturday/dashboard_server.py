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
<title>SATurday</title>
<link rel="preconnect" href="https://fonts.googleapis.com"/>
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin/>
<link href="https://fonts.googleapis.com/css2?family=DM+Sans:ital,opsz,wght@0,9..40,400;0,9..40,500;0,9..40,600;0,9..40,700;1,9..40,400&family=Fraunces:opsz,wght@9..144,500;9..144,600;9..144,700&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet"/>
<style>
  :root {
    --bg: #08090b;
    --bg-2: #0e1013;
    --panel: #12151a;
    --panel-2: #171b22;
    --text: #f3f1ea;
    --muted: #8b9188;
    --line: #2a2f28;
    --line-hot: #3d4638;
    --sage: #c7d9a8;
    --sage-dim: #9baf7e;
    --cyan: #5ce1e6;
    --magenta: #ff4ecd;
    --ok: #7dff9a;
    --warn: #ffd36a;
    --bad: #ff6b7a;
    --phosphor: #9dffb0;
    --serif: "Fraunces", Georgia, serif;
    --sans: "DM Sans", "Segoe UI", sans-serif;
    --mono: "JetBrains Mono", ui-monospace, monospace;
  }
  * { box-sizing: border-box; }
  html { scroll-behavior: smooth; }
  body {
    margin: 0;
    font-family: var(--sans);
    color: var(--text);
    min-height: 100vh;
    background:
      radial-gradient(900px 480px at 12% -8%, rgba(255, 77, 205, 0.08), transparent 55%),
      radial-gradient(800px 520px at 92% 0%, rgba(92, 225, 230, 0.07), transparent 50%),
      radial-gradient(700px 400px at 50% 100%, rgba(199, 217, 168, 0.05), transparent 55%),
      var(--bg);
    background-attachment: fixed;
  }
  body::before {
    content: "";
    position: fixed;
    inset: 0;
    pointer-events: none;
    z-index: 0;
    opacity: 0.22;
    background-image:
      linear-gradient(rgba(92, 225, 230, 0.045) 1px, transparent 1px),
      linear-gradient(90deg, rgba(255, 77, 205, 0.035) 1px, transparent 1px);
    background-size: 48px 48px;
    mask-image: radial-gradient(ellipse at center, black 35%, transparent 85%);
  }
  body::after {
    content: "";
    position: fixed;
    inset: 0;
    pointer-events: none;
    z-index: 0;
    opacity: 0.04;
    background: repeating-linear-gradient(
      0deg,
      transparent,
      transparent 2px,
      rgba(0, 0, 0, 0.35) 2px,
      rgba(0, 0, 0, 0.35) 3px
    );
  }
  .shell { position: relative; z-index: 1; }

  /* Top nav — portfolio magazine bar */
  .topbar {
    display: flex; align-items: center; justify-content: space-between;
    gap: 1rem; flex-wrap: wrap;
    padding: 1rem 1.75rem;
    border-bottom: 1px solid var(--line);
    background: rgba(8, 9, 11, 0.82);
    backdrop-filter: blur(10px);
    position: sticky; top: 0; z-index: 20;
  }
  .brand {
    font-family: var(--mono); font-size: 0.72rem; letter-spacing: 0.14em;
    text-transform: uppercase; color: var(--text); text-decoration: none;
  }
  .brand span { color: var(--sage); }
  .tabs { display: flex; gap: 0.15rem; flex-wrap: wrap; }
  .tabs button {
    font-family: var(--mono); font-size: 0.7rem; letter-spacing: 0.12em;
    text-transform: uppercase; background: transparent; color: var(--muted);
    border: 0; border-bottom: 1px solid transparent;
    padding: 0.55rem 0.75rem; cursor: pointer; font-weight: 500;
  }
  .tabs button:hover { color: var(--text); }
  .tabs button.active {
    color: var(--sage); border-bottom-color: var(--sage);
  }
  .topbar-meta {
    font-family: var(--mono); font-size: 0.68rem; letter-spacing: 0.1em;
    text-transform: uppercase; color: var(--muted);
  }
  .topbar-meta .dot { color: var(--cyan); margin: 0 0.35rem; }

  .page-intro {
    padding: 1.15rem 1.75rem 0.35rem;
    border-bottom: 1px solid var(--line);
  }
  .page-intro h1 {
    margin: 0;
    font-family: var(--serif);
    font-weight: 600;
    font-size: 1.65rem;
    letter-spacing: -0.01em;
  }
  .page-intro p {
    margin: 0.35rem 0 0;
    color: var(--muted);
    max-width: 40rem;
    font-size: 0.95rem;
    line-height: 1.45;
  }
  .card-blurb {
    margin: -0.35rem 0 0.75rem;
    color: var(--muted);
    font-size: 0.88rem;
    line-height: 1.4;
  }

  main { padding: 1.35rem 1.75rem 2.5rem; display: grid; gap: 1.1rem; }
  .panel { display: none; }
  .panel.active { display: grid; gap: 1.1rem; }
  .row { display: grid; gap: 1rem; grid-template-columns: repeat(auto-fit, minmax(220px, 1fr)); }

  .card {
    background: color-mix(in srgb, var(--panel) 88%, black);
    border: 1px solid var(--line);
    border-radius: 14px;
    padding: 1.05rem 1.15rem;
    position: relative;
    overflow: hidden;
  }
  .card::before {
    content: "";
    position: absolute; top: 0; left: 0; right: 0; height: 1px;
    background: linear-gradient(90deg, transparent, rgba(199,217,168,0.45), rgba(92,225,230,0.35), transparent);
    opacity: 0.7;
  }
  .card h2, .sec-label {
    margin: 0 0 0.7rem;
    font-family: var(--mono);
    font-size: 0.7rem;
    color: var(--muted);
    text-transform: uppercase;
    letter-spacing: 0.14em;
    font-weight: 500;
  }
  .sec-label .num { color: var(--cyan); margin-right: 0.35rem; }
  .big {
    font-family: var(--serif);
    font-size: 2.35rem;
    font-weight: 600;
    letter-spacing: -0.02em;
    color: var(--sage);
  }
  .bar {
    height: 6px; background: #1a1f18; border-radius: 999px; overflow: hidden; margin-top: 0.65rem;
  }
  .bar > span {
    display: block; height: 100%;
    background: linear-gradient(90deg, var(--sage), var(--cyan));
  }
  table { width: 100%; border-collapse: collapse; font-size: 0.92rem; }
  th, td { text-align: left; padding: 0.7rem 0.45rem; border-bottom: 1px solid var(--line); vertical-align: top; }
  th {
    color: var(--muted); font-weight: 500; font-size: 0.68rem;
    text-transform: uppercase; letter-spacing: 0.12em; font-family: var(--mono);
  }
  .pill {
    display: inline-block; padding: 0.14rem 0.5rem; border-radius: 999px;
    font-size: 0.72rem; border: 1px solid var(--line);
    font-family: var(--mono); letter-spacing: 0.04em;
  }
  .pill.ok { color: var(--ok); border-color: color-mix(in srgb, var(--ok) 45%, var(--line)); }
  .pill.warn { color: var(--warn); border-color: color-mix(in srgb, var(--warn) 40%, var(--line)); }
  .pill.bad { color: var(--bad); border-color: color-mix(in srgb, var(--bad) 40%, var(--line)); }
  .pill.muted { color: var(--muted); }
  .ok { color: var(--ok); } .warn { color: var(--warn); } .bad { color: var(--bad); }
  .controls { display: flex; flex-wrap: wrap; gap: 0.6rem; align-items: center; }
  button, .btn {
    font-family: var(--mono); font-size: 0.72rem; letter-spacing: 0.08em;
    text-transform: uppercase; font-weight: 600;
    background: var(--sage); color: #10140c; border: 1px solid var(--sage);
    border-radius: 4px; padding: 0.6rem 0.95rem; cursor: pointer;
  }
  button:hover { filter: brightness(1.05); }
  button.danger {
    background: transparent; color: var(--bad); border-color: color-mix(in srgb, var(--bad) 55%, var(--line));
  }
  button.ghost {
    background: transparent; color: var(--text); border: 1px solid var(--line-hot);
  }
  button.ghost:hover { border-color: var(--sage); color: var(--sage); }
  input[type=text], input[type=search] {
    flex: 1; min-width: 220px;
    background: #0b0d10; color: var(--text);
    border: 1px solid var(--line); border-radius: 4px;
    padding: 0.65rem 0.8rem; font-family: var(--mono); font-size: 0.82rem;
  }
  input[type=text]:focus, input[type=search]:focus {
    outline: none; border-color: var(--cyan);
    box-shadow: 0 0 0 1px rgba(92, 225, 230, 0.25);
  }
  .mono { font-family: var(--mono); font-size: 0.82rem; }
  .muted { color: var(--muted); }
  .term {
    background: #070809;
    border: 1px solid var(--line);
    border-radius: 8px;
    padding: 0.85rem 0.95rem;
    max-height: 280px; overflow: auto;
    font-family: var(--mono); font-size: 0.8rem;
    line-height: 1.55; color: var(--phosphor);
  }
  .term .muted { color: #5f6a5c; }
  footer {
    padding: 0 1.75rem 2rem; color: var(--muted);
    font-family: var(--mono); font-size: 0.7rem; letter-spacing: 0.06em;
  }

  /* Tree */
  .tree-toolbar { display: flex; flex-wrap: wrap; gap: 0.6rem; align-items: center; }
  .tree-meta { display: flex; flex-wrap: wrap; gap: 0.65rem; margin-top: 0.85rem; }
  .tree-meta .stat {
    background: #0b0d10; border: 1px solid var(--line); border-radius: 8px;
    padding: 0.5rem 0.75rem; font-size: 0.82rem;
  }
  .tree-meta .stat strong {
    font-family: var(--serif); font-size: 1.15rem; color: var(--sage); font-weight: 600;
  }
  .dag-note {
    margin-top: 0.85rem; padding: 0.75rem 0.9rem;
    border-left: 2px solid var(--magenta);
    background: rgba(255, 77, 205, 0.04);
    font-size: 0.9rem; color: var(--muted);
  }
  details.rung-node, details.cluster-node, details.decl-node {
    border: 1px solid var(--line); border-radius: 12px; margin: 0.55rem 0;
    background: var(--panel);
    transition: border-color 0.15s ease;
  }
  details.rung-node:hover, details.cluster-node:hover, details.decl-node:hover {
    border-color: var(--line-hot);
  }
  details.rung-node > summary,
  details.cluster-node > summary,
  details.decl-node > summary {
    cursor: pointer; list-style: none; padding: 0.8rem 1rem;
    display: flex; flex-wrap: wrap; gap: 0.55rem; align-items: center;
  }
  details.rung-node > summary::-webkit-details-marker,
  details.cluster-node > summary::-webkit-details-marker,
  details.decl-node > summary::-webkit-details-marker { display: none; }
  details.rung-node > summary::before,
  details.cluster-node > summary::before,
  details.decl-node > summary::before {
    content: "⊢";
    font-family: var(--mono); color: var(--muted); width: 1rem;
    display: inline-block; font-size: 0.85rem;
  }
  details[open].rung-node > summary::before,
  details[open].cluster-node > summary::before,
  details[open].decl-node > summary::before {
    content: "⊨"; color: var(--sage);
  }
  details.rung-node.role-bridge { border-color: color-mix(in srgb, var(--cyan) 35%, var(--line)); }
  details.rung-node.role-setup { border-color: var(--line); }
  details.rung-node.role-main { border-left: 2px solid var(--sage); }
  details.cluster-node { background: var(--bg-2); margin-left: 0.35rem; }
  details.decl-node { background: #0b0d10; border-color: #22272a; margin: 0.55rem 0; }
  details.decl-node.has-prose { border-left: 2px solid var(--ok); }
  details.decl-node.formula-only { border-left: 2px solid var(--cyan); }
  .rung-body, .cluster-body, .decl-body { padding: 0 1rem 1rem 1.35rem; }
  .branch {
    margin-left: 0.15rem; padding-left: 0.8rem;
    border-left: 1px solid var(--line);
  }
  .decl-summary-title {
    font-family: var(--serif); font-weight: 600; font-size: 1.05rem;
  }
  .decl-summary-preview {
    flex: 1 1 100%; color: var(--muted); font-size: 0.88rem;
    line-height: 1.45; margin-top: 0.1rem;
  }
  .prose-block {
    margin: 0.35rem 0 0.75rem;
    padding: 0.85rem 0.95rem;
    background: rgba(199, 217, 168, 0.05);
    border: 1px solid color-mix(in srgb, var(--sage) 28%, var(--line));
    border-radius: 10px;
    font-family: var(--serif);
    font-size: 1.05rem;
    line-height: 1.55;
    color: var(--text);
  }
  .prose-label, .formula-label {
    display: block; font-size: 0.68rem; letter-spacing: 0.14em;
    text-transform: uppercase; color: var(--muted); margin-bottom: 0.4rem;
    font-family: var(--mono);
  }
  .formula-block {
    margin: 0;
    padding: 0.75rem 0.9rem;
    background: #060708;
    border: 1px solid var(--line);
    border-radius: 8px;
    font-family: var(--mono);
    font-size: 0.86rem;
    line-height: 1.55;
    color: var(--cyan);
    overflow-x: auto;
    white-space: pre-wrap;
    word-break: break-word;
    text-shadow: 0 0 18px rgba(92, 225, 230, 0.18);
  }
  .decl-meta {
    margin-top: 0.7rem; display: flex; flex-wrap: wrap; gap: 0.55rem;
    align-items: center; font-size: 0.75rem; color: var(--muted);
  }
  .count-badge {
    margin-left: auto; font-family: var(--mono);
    color: var(--muted); font-size: 0.72rem; letter-spacing: 0.04em;
  }
  .empty-rung { color: var(--muted); font-style: italic; padding: 0.4rem 0; }
  .section-label {
    margin: 1.35rem 0 0.5rem; font-size: 0.7rem; letter-spacing: 0.16em;
    text-transform: uppercase; color: var(--sage-dim); font-family: var(--mono);
  }
</style>
</head>
<body>
<div class="shell">
<header class="topbar">
  <a class="brand" href="/">SATurday</a>
  <div class="tabs" role="tablist">
    <button type="button" class="active" data-tab="progress" id="tabProgress">Progress</button>
    <button type="button" data-tab="tree" id="tabTree">Accepted tree</button>
  </div>
  <div class="topbar-meta">local<span class="dot">·</span>Lean 4</div>
</header>

<section class="page-intro">
  <h1>Research dashboard</h1>
  <p>Watch the auto loop, check rung status, and browse accepted Lean declarations.</p>
</section>

<main>
  <div id="panel-progress" class="panel active">
    <section class="card" id="liveCard">
      <h2 class="sec-label">Auto loop</h2>
      <p class="card-blurb">What the current <span class="mono">satday auto</span> run is doing.</p>
      <div id="liveSummary" class="mono"></div>
      <div class="row" style="margin-top:0.9rem" id="liveStats"></div>
      <div id="liveFeed" class="term" style="margin-top:0.95rem"></div>
    </section>
    <section class="row" id="summary"></section>
    <section class="card">
      <h2 class="sec-label">Kill switch</h2>
      <p class="card-blurb">Stops the next wake. Same as <span class="mono">satday kill</span>.</p>
      <div class="controls">
        <input id="reason" type="text" placeholder="Reason (optional)"/>
        <button class="danger" id="killBtn">Kill auto loop</button>
        <button class="ghost" id="unkillBtn">Clear kill</button>
        <span id="killState" class="mono"></span>
      </div>
    </section>
    <section class="card">
      <h2 class="sec-label">Rungs</h2>
      <p class="card-blurb">Ladder status, pin progress, and reflect counters.</p>
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
      <h2 class="sec-label">Recent sessions</h2>
      <p class="card-blurb">Latest saturday cycles from the session log.</p>
      <div id="sessions" class="term"></div>
    </section>
  </div>

  <div id="panel-tree" class="panel">
    <section class="card">
      <h2 class="sec-label">Accepted declarations</h2>
      <p class="card-blurb">
        Allowlist from <span class="mono" id="treePath">scripts/accepted_declarations.txt</span>.
        Expand a rung, then a cluster, then a name for prose and the Lean formula.
      </p>
      <div class="tree-toolbar">
        <input id="treeFilter" type="search" placeholder="Filter names, prose, or formulas"/>
        <button class="ghost" type="button" id="expandRungs">Expand rungs</button>
        <button class="ghost" type="button" id="collapseAll">Collapse</button>
        <button class="ghost" type="button" id="reloadTree">Reload</button>
      </div>
      <div class="tree-meta" id="treeMeta"></div>
      <div class="dag-note" id="dagNote"></div>
    </section>
    <section class="card">
      <h2 class="sec-label">Ladder tree</h2>
      <p class="card-blurb">Setup, main climb (R0–R4), and the R5 bridge.</p>
      <div id="treeRoot"></div>
    </section>
  </div>
</main>
<footer>
  Refreshes from <span class="mono">/api/progress</span> · tree from <span class="mono">/api/accepted-tree</span>
</footer>
</div>
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
let progressInFlight = false;

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
  if (progressInFlight) {
    console.log('[saturday.dashboard.ui] skip poll; previous still in flight');
    return;
  }
  progressInFlight = true;
  console.log('[saturday.dashboard.ui] fetch /api/progress');
  const liveEl = document.getElementById('liveSummary');
  if (liveEl && !liveEl.dataset.filled) {
    liveEl.innerHTML = '<div class="muted">Loading auto-loop progress…</div>';
  }
  try {
    const res = await fetch('/api/progress');
    if (!res.ok) throw new Error('HTTP ' + res.status);
    const data = await res.json();
    renderProgress(data);
    if (liveEl) liveEl.dataset.filled = '1';
  } catch (err) {
    console.error('[saturday.dashboard.ui] loadProgress failed', err);
    if (liveEl) {
      liveEl.innerHTML = '<div class="bad">Progress fetch failed: '
        + esc(String(err && err.message ? err.message : err))
        + '. Is the dashboard process healthy?</div>';
    }
  } finally {
    progressInFlight = false;
  }
}

function renderProgress(data) {
  console.log('[saturday.dashboard.ui] renderProgress');
  const live = data.live || {};
  const stats = live.stats || {};
  const models = live.models || {};
  const runCls = live.running && !live.stale ? 'ok' : (live.stale ? 'warn' : 'bad');
  const runLabel = !live.running
    ? 'AUTO NOT RUNNING'
    : (live.stale
      ? (live.proc_alive ? 'AUTO RUNNING (quiet heartbeat)' : 'STALE heartbeat')
      : 'AUTO RUNNING');
  document.getElementById('liveSummary').innerHTML = `
    <div><span class="${runCls}">${runLabel}</span>
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
    <div class="card"><h2>This run</h2>
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
      <div class="muted">names on the allowlist</div>
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
    : '<div class="muted">No live events yet</div>';

  const sum = document.getElementById('summary');
  sum.innerHTML = `
    <div class="card"><h2>Certified rungs</h2><div class="big">${data.rung_completion_pct}%</div>
      <div class="muted">${data.certified_count} / ${data.rung_count} certified</div>
      <div class="bar"><span style="width:${data.rung_completion_pct}%"></span></div></div>
    <div class="card"><h2>Critical pins</h2><div class="big">${data.critical_pin_pct}%</div>
      <div class="muted">${data.critical_total - data.critical_open} closed / ${data.critical_total} open tracked</div>
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

function previewText(d) {
  if (d.prose) return d.prose;
  if (d.formula) return d.formula;
  return d.fq || '';
}

function declMatches(d, cTitle, q) {
  if (!q) return true;
  return filterMatches(d.fq, q)
    || filterMatches(d.short, q)
    || filterMatches(d.prose, q)
    || filterMatches(d.formula, q)
    || filterMatches(d.signature, q)
    || filterMatches(cTitle, q);
}

function renderDecl(d) {
  const prose = d.prose || '';
  const formula = d.formula || '';
  const kind = d.kind || 'decl';
  const cls = prose ? 'has-prose' : (formula ? 'formula-only' : '');
  const preview = previewText(d);
  const previewShort = preview.length > 160 ? preview.slice(0, 157) + '…' : preview;
  const proseHtml = prose
    ? `<div class="prose-block"><span class="prose-label">Prose</span>${esc(prose)}</div>`
    : `<div class="muted" style="margin:0.35rem 0 0.7rem">No docstring</div>`;
  const formulaHtml = formula
    ? `<div><span class="formula-label">Formula</span><pre class="formula-block">${esc(formula)}</pre></div>`
    : '';
  return `<details class="decl-node ${cls}">
    <summary>
      <span class="decl-summary-title">${esc(d.short)}</span>
      <span class="pill muted">${esc(kind)}</span>
      <span class="decl-summary-preview">${esc(previewShort)}</span>
    </summary>
    <div class="decl-body">
      ${proseHtml}
      ${formulaHtml}
      <div class="decl-meta">
        <span class="mono">${esc(d.fq)}</span>
        ${d.source ? `<span class="mono">${esc(d.source)}</span>` : ''}
      </div>
    </div>
  </details>`;
}

function renderTree(data, filterQ) {
  console.log('[saturday.dashboard.ui] renderTree filter=', filterQ || '(none)');
  const q = (filterQ || '').trim().toLowerCase();
  const summary = data.summary || {};
  const dag = data.ladder_dag || {};
  document.getElementById('treePath').textContent = summary.decls_path || 'scripts/accepted_declarations.txt';
  const stmtFound = summary.statements_found != null ? summary.statements_found : '—';
  const stmtMissing = summary.statements_missing != null ? summary.statements_missing : '—';
  document.getElementById('treeMeta').innerHTML = `
    <div class="stat"><strong>${summary.total_declarations || 0}</strong> declarations</div>
    <div class="stat"><strong>${summary.rung_count_with_decls || 0}</strong> rungs with decls</div>
    <div class="stat"><strong>${stmtFound}</strong> with Lean statements
      ${stmtMissing && stmtMissing !== 0 ? `· <span class="warn">${stmtMissing} missing</span>` : ''}</div>
  `;
  document.getElementById('dagNote').textContent =
    'R0 → R1 → R2 → R3 → R4 → summit. R5 is the Cook–Reckhow bridge.';

  const rungs = data.rungs || [];
  const setup = rungs.filter(r => r.role === 'setup');
  const main = rungs.filter(r => r.role === 'main');
  const bridge = rungs.filter(r => r.role === 'bridge');
  const other = rungs.filter(r => !['setup','main','bridge'].includes(r.role));

  function renderCluster(c) {
    const decls = (c.declarations || []).filter(d => declMatches(d, c.title, q));
    if (q && !decls.length && !filterMatches(c.title, q)) return '';
    const showDecls = q ? decls : (c.declarations || []);
    if (q && !showDecls.length) return '';
    return `<details class="cluster-node" ${q ? 'open' : ''}>
      <summary>
        <span>${esc(c.title)}</span>
        <span class="count-badge">${showDecls.length} decl${showDecls.length===1?'':'s'}</span>
      </summary>
      <div class="cluster-body">
        <div class="branch">${showDecls.map(renderDecl).join('')}</div>
      </div>
    </details>`;
  }

  function renderRung(r) {
    const clustersHtml = (r.clusters || []).map(renderCluster).filter(Boolean).join('');
    const rungHit = filterMatches(r.title, q) || filterMatches(r.rung_id, q) || filterMatches(r.status, q);
    if (q && !clustersHtml && !rungHit && r.decl_count > 0) return '';
    if (q && r.decl_count === 0 && !rungHit) return '';
    const body = r.decl_count === 0
      ? `<div class="empty-rung">No accepted decls yet (${esc(r.status)}).</div>`
      : `<div class="branch">${clustersHtml || '<div class="empty-rung">No matches</div>'}</div>`;
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
    block('Main climb', main) +
    block('Side bridge', bridge) +
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
setInterval(loadProgress, 4000);
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
