#!/usr/bin/env python3
"""Check that the docs still match the code.
 1. docs/Interface.md: every `### `QBS.X.Y`...` heading names existing modules, and every backticked name that
    starts a bullet (` - `name` —`) occurs as a word in one of the modules of the nearest heading(s).
 2. docs/*.md: every ```agda block whose first line is `-- from: path` is a verbatim (whitespace-normalised) excerpt of path.
 3. scripts/modindex.py --check (every module has a header; docs/Modules.md is current).
Exit 1 with a list of problems."""
import os, re, subprocess, sys
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
norm = lambda t: re.sub(r'\s+', ' ', t).strip()
bad = []

def modfile(m): return os.path.join(ROOT, 'src', *m.split('.')) + '.agda'

# 1. Interface.md
cur = []
for ln in open(os.path.join(ROOT, 'docs', 'Interface.md')):
    if ln.startswith('### '):
        cur = re.findall(r'`(QBS\.[A-Za-z.]+)`', ln)
        if not cur and re.search(r'`(?:Borel|Analysis|Model|Continuous)', ln): cur = []
        for m in cur:
            if not os.path.exists(modfile(m)): bad.append(f'Interface.md: no module {m}')
        continue
    m = re.match(r'- `([^`]+)`', ln)
    if m and cur:
        names = m.group(1).split()
        name = names[-1] if names[0] == 'module' else names[0]
        name = name.strip()
        txt = ' '.join(open(modfile(x)).read() for x in cur if os.path.exists(modfile(x)))
        # names mentioned with a module prefix in the line, e.g. "`QBS.Exponential`: `name`"
        extra = re.findall(r'`(QBS\.[A-Za-z.]+)`', ln)
        for x in extra:
            if os.path.exists(modfile(x)): txt += open(modfile(x)).read()
        if not re.search(r'(?<![\w])' + re.escape(name) + r'(?![\w])', txt) and \
           not re.search(re.escape(name), txt):
            bad.append(f'Interface.md: `{name}` not found in {", ".join(cur)}')
    # secondary names on the line: `a`, `b` before the dash
    if m and cur:
        for n in re.findall(r'`([^`\s]+)`', ln.split(' — ')[0])[1:]:
            txt = ' '.join(open(modfile(x)).read() for x in cur + re.findall(r'`(QBS\.[A-Za-z.]+)`', ln) if os.path.exists(modfile(x)))
            if n not in txt and not n.startswith('QBS.'): bad.append(f'Interface.md: `{n}` not found in {", ".join(cur)}')

# 2. excerpts
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

# 3. headers / module index
r = subprocess.run([sys.executable, os.path.join(ROOT, 'scripts', 'modindex.py'), '--check'], capture_output=True, text=True)
if r.returncode: bad.append(r.stdout.strip())

# 4. no `rewrite` (plans/04-equality.md): use cong, subst, or `with ... in eq`
for d, _, fs in os.walk(os.path.join(ROOT, 'src')):
    for f in fs:
        if not f.endswith('.agda'): continue
        p = os.path.join(d, f)
        for i, l in enumerate(open(p), 1):
            if re.search(r'\brewrite\b', re.sub(r'--.*', '', l)): bad.append(f'{os.path.relpath(p, ROOT)}:{i}: uses `rewrite`')

if bad:
    print('\n'.join(bad)); sys.exit(1)
print('docs OK')
