"""
Local saturday progress dashboard (stdlib only).

  satday dashboard
  open http://127.0.0.1:8765/
"""

from __future__ import annotations

import json
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Dict, Optional
from urllib.parse import parse_qs, urlparse

from search.saturday.control import clear_kill, engage_kill, load_control
from search.saturday.progress import build_progress_snapshot
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
  main { padding: 1.25rem 1.75rem 2.5rem; display: grid; gap: 1rem; }
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
  input[type=text] {
    flex: 1; min-width: 220px; background: #101826; color: var(--text);
    border: 1px solid var(--line); border-radius: 8px; padding: 0.55rem 0.7rem;
  }
  .mono { font-family: "IBM Plex Mono", ui-monospace, monospace; font-size: 0.82rem; }
  .muted { color: var(--muted); }
  footer { padding: 0 1.75rem 1.5rem; color: var(--muted); font-size: 0.85rem; }
</style>
</head>
<body>
<header>
  <h1>SATurday</h1>
  <p>Live ladder progress, critical Frontier pins, reflection plateau counters, and kill switch.</p>
</header>
<main>
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
</main>
<footer>
  Refreshing every 5s from <span class="mono">/api/progress</span>. Preferred research driver: <span class="mono">satday auto --remote</span>.
</footer>
<script>
async function load() {
  const res = await fetch('/api/progress');
  const data = await res.json();
  const sum = document.getElementById('summary');
  sum.innerHTML = `
    <div class="card"><h2>Rung certification</h2><div class="big">${data.rung_completion_pct}%</div>
      <div class="muted">${data.certified_count} / ${data.rung_count} certified</div>
      <div class="bar"><span style="width:${data.rung_completion_pct}%"></span></div></div>
    <div class="card"><h2>Critical pins</h2><div class="big">${data.critical_pin_pct}%</div>
      <div class="muted">${data.critical_total - data.critical_open} closed / ${data.critical_total} tracked</div>
      <div class="bar"><span style="width:${data.critical_pin_pct}%"></span></div></div>
    <div class="card"><h2>Toward P vs NP</h2><div style="font-size:1rem;line-height:1.45">${data.toward_p_vs_np || ''}</div></div>
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
    return `<tr>
      <td><strong>${r.title}</strong><div class="mono muted">${r.rung_id}</div>
        <div class="muted">pin progress ${r.pin_progress_pct}%</div></td>
      <td><span class="pill ${st}">${r.status}</span>${r.paused ? ' <span class="pill bad">paused</span>' : ''}
        ${r.force_action ? ` <span class="pill warn">force:${r.force_action}</span>` : ''}</td>
      <td class="mono">${r.pin_progress_pct}%</td>
      <td class="mono">${pins}</td>
      <td class="mono muted">noProg=${ref.wakes_without_obligation_progress || 0}
        dup=${ref.consecutive_near_duplicates || 0}
        err=${ref.consecutive_same_error || 0}</td>
    </tr>`;
  }).join('');
  const sess = document.getElementById('sessions');
  sess.innerHTML = (data.recent_sessions || []).slice().reverse().map(s =>
    `<div>${s.ts || s.timestamp || ''} · ${s.workstream || ''} ${s.rung} / ${s.action_type} -> ${s.result}</div>`
  ).join('') || '<div class="muted">No sessions yet</div>';
}
document.getElementById('killBtn').onclick = async () => {
  const reason = document.getElementById('reason').value || 'dashboard kill';
  await fetch('/api/kill', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({reason})});
  load();
};
document.getElementById('unkillBtn').onclick = async () => {
  await fetch('/api/unkill', {method:'POST'});
  load();
};
load();
setInterval(load, 5000);
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
        if parsed.path in {"/", "/index.html"}:
            self._send(200, DASHBOARD_HTML.encode("utf-8"), "text/html; charset=utf-8")
            return
        if parsed.path == "/api/progress":
            snap = build_progress_snapshot(self.repo_root)
            self._json(200, snap)
            return
        if parsed.path == "/api/control":
            self._json(200, load_control(self.repo_root).to_dict())
            return
        self._json(404, {"error": "not found", "path": parsed.path})

    def do_POST(self) -> None:  # noqa: N802
        parsed = urlparse(self.path)
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
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        announce("Dashboard stopped")
        server.shutdown()
