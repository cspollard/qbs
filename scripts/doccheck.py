#!/usr/bin/env python3
"""Check that the docs still match the code.
 1. docs/*.md: every ```agda block whose first line is `-- from: path` is a verbatim (whitespace-normalised) excerpt of path.
 2. scripts/modindex.py --check (every module has a header; docs/Modules.md is current).
Exit 1 with a list of problems."""
import os, re, subprocess, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
norm = lambda t: re.sub(r'\s+', ' ', t).strip()
bad = []

# 1. excerpts
for f in sorted(os.listdir(os.path.join(ROOT, 'docs'))):
    if not f.endswith('.md'): continue
    text = open(os.path.join(ROOT, 'docs', f)).read()
    for blk in re.findall(r'```agda\n(.*?)```', text, re.S):
        lines = [l.strip() for l in blk.strip('\n').split('\n')]
        if lines and lines[0].startswith('-- from:'):
            path = lines[0][len('-- from:'):].strip()
            src = norm(open(os.path.join(ROOT, path)).read()) if os.path.exists(os.path.join(ROOT, path)) else None
            if src is None: bad.append(f'{f}: missing file {path}')
            elif norm('\n'.join(lines[1:])) not in src: bad.append(f'{f}: stale excerpt of {path}: {lines[1][:60]}')

# 2. headers / module index
r = subprocess.run([sys.executable, os.path.join(ROOT, 'scripts', 'modindex.py'), '--check'], capture_output=True, text=True)
if r.returncode: bad.append(r.stdout.strip())

# 3. no `rewrite` (plans/04-equality.md): use cong, subst, or `with ... in eq`
for d, _, fs in os.walk(os.path.join(ROOT, 'src')):
    for f in fs:
        if not f.endswith('.agda'): continue
        p = os.path.join(d, f)
        for i, l in enumerate(open(p), 1):
            if re.search(r'\brewrite\b', re.sub(r'--.*', '', l)): bad.append(f'{os.path.relpath(p, ROOT)}:{i}: uses `rewrite`')

if bad:
    print('\n'.join(bad)); sys.exit(1)
print('docs OK')
