#!/usr/bin/env python3
"""Typecheck every module of src/ individually, leaves of the import graph first, with a time limit.

A module that exceeds the limit is killed and recorded as SLOW; everything that (transitively) imports it is
skipped (its interface cannot be built).  Dependencies are always checked before their dependents, so
each run checks exactly one module against cached interfaces.

  scripts/profile-tree.py [--limit SECONDS] [--agda CMD] [--out DIR] [--jobs N]

Writes DIR/tree.tsv (module, depth, status, seconds) and DIR/<Module>.txt (Agda `--profile=modules` output).
Resumable: modules already `ok` in tree.tsv are not re-run.  Delete tree.tsv / _build for a cold run.
"""
import argparse, os, re, signal, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import threading

ap = argparse.ArgumentParser()
ap.add_argument('--limit', type=int, default=120)
ap.add_argument('--agda', default='agda')
ap.add_argument('--out', default='profile')
ap.add_argument('--jobs', type=int, default=1)
a = ap.parse_args()
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(root)

mods = {}
for d, _, fs in os.walk('src'):
    for f in fs:
        if f.endswith('.agda'):
            p = os.path.join(d, f)
            mods[os.path.relpath(p, 'src')[:-5].replace('/', '.')] = p
imp = re.compile(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.\'-]+)', re.M)
deps = {}
for m, p in mods.items():
    txt = re.sub(r'--.*', '', open(p, encoding='utf-8').read())
    deps[m] = {x for x in imp.findall(txt) if x in mods}
depth = {}
def dp(m):
    if m not in depth:
        depth[m] = 0 if not deps[m] else 1 + max(dp(x) for x in deps[m])
    return depth[m]
for m in mods: dp(m)

os.makedirs(a.out, exist_ok=True)
tsv = os.path.join(a.out, 'tree.tsv')
status = {}
if os.path.exists(tsv):
    for l in open(tsv):
        m, d, s, t = l.rstrip('\n').split('\t')
        if s in ('ok', 'holes'): status[m] = (s, float(t))
lock = threading.Lock()

def run(m):
    # holes still produce an interface, so dependents of a `holes` module may proceed
    if any(status.get(x, ('x',))[0] not in ('ok', 'holes') for x in deps[m]):
        return ('skipped', 0.0)
    out = os.path.join(a.out, m + '.txt')
    t0 = time.time()
    with open(out, 'w') as fh:
        pr = subprocess.Popen([a.agda, '--profile=modules', mods[m], '+RTS', '-s', '-RTS'],
                              stdout=fh, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = pr.wait(timeout=a.limit)
        except subprocess.TimeoutExpired:
            os.killpg(pr.pid, signal.SIGKILL); pr.wait()
            return ('SLOW', time.time() - t0)
    dt = time.time() - t0
    text = open(out, encoding='utf-8', errors='replace').read()
    if rc == 0: return ('ok', dt)
    return ('holes' if 'Unsolved' in text and '/error' not in text.lower() and 'Error' not in text.split('Unsolved')[0] else 'error', dt)

def record(m, st):
    with lock:
        status[m] = st
        with open(tsv, 'w') as f:
            for k in sorted(status, key=lambda k: (depth[k], k)):
                f.write(f'{k}\t{depth[k]}\t{status[k][0]}\t{status[k][1]:.1f}\n')
        print(f'depth {depth[m]:2d}  {st[0]:8s} {st[1]:7.1f}s  {m}', flush=True)

# a module with unsolved holes (status holes) still produces an interface, so dependents may proceed
_run = run
def run(m):
    bad = [x for x in deps[m] if status.get(x, ('x',))[0] not in ('ok', 'holes')]
    if bad: return ('skipped', 0.0)
    return _run_checked(m)
def _run_checked(m):
    saved = deps[m]
    deps[m] = set()      # dependencies already vetted above
    try: return _run(m)
    finally: deps[m] = saved

for level in range(max(depth.values()) + 1):
    todo = [m for m in sorted(mods) if depth[m] == level and status.get(m, ('',))[0] not in ('ok', 'holes')]
    with ThreadPoolExecutor(a.jobs) as ex:
        for m, st in zip(todo, ex.map(run, todo)):
            record(m, st)

slow = [m for m in status if status[m][0] == 'SLOW']
print(f'\n{len(mods)} modules; ok/holes: {sum(s[0] in ("ok","holes") for s in status.values())}; '
      f'SLOW (> {a.limit}s): {len(slow)}; skipped: {sum(s[0]=="skipped" for s in status.values())}; '
      f'error: {sum(s[0]=="error" for s in status.values())}')
for m in sorted(slow, key=lambda k: depth[k]): print('SLOW', depth[m], m)
