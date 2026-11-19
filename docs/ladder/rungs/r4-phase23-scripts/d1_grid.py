"""Parallel grid driver: for each (graph,q,p,s,t,mode) and m in range, run d1_search.py under a timeout; append results to a log.
usage: d1_grid.py LOG TIMEOUT MMIN MMAX JOBS spec... ; spec = graph:q:p:s:t:mode"""
import subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor
log, to, a, b, jobs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
here = os.path.dirname(os.path.abspath(__file__))
def run(job):
    spec, m = job; g, q, p, s, t, mode = spec.split(':')
    try:
        r = subprocess.run(['python3', os.path.join(here, 'd1_search.py'), g, q, p, s, t, mode, str(m)], capture_output=True, text=True, timeout=to)
        out = r.stdout.strip() or r.stderr.strip()[-300:]
    except subprocess.TimeoutExpired: out = f'{g} q={q} p={p} s={s} t={t} {mode} m={m}: TIMEOUT {to}s'
    with open(log, 'a') as f: f.write(out + '\n')
    return out
jobs_l = [(sp, m) for sp in sys.argv[6:] for m in range(a, b + 1)]
with ThreadPoolExecutor(jobs) as ex:
    for o in ex.map(run, jobs_l): print(o.split('\n')[0], flush=True)
