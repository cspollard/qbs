#!/usr/bin/env python3
"""Flag unwieldy declarations in src/QBS/**/*.agda: long bodies, many characters, or very wide lines.

A declaration is a group of consecutive lines starting at a line whose indentation is at most that of the
previous declaration's first line and whose first token differs from the previous declaration's name (so a
signature and its clauses form one declaration; a record literal with at least five fields is measured by its
largest field).  `abstract`, `private`, `module ... where` and similar
container lines are looked through.  Blank lines and `--` comment lines do not count.

A `record` is also flagged as a whole when it has too many fields or lines (a giant interface record is hard to
instantiate, read and extend: factor it into sub-records or parameterised pieces).

Usage: scripts/longdecls.py [--lines N] [--chars N] [--width N] [--fields N] [--rlines N] [--top K] [--check] [--baseline FILE] [PATH...]
  thresholds (defaults 18 lines / 1000 characters / 130 columns): a declaration is flagged when it exceeds any
  --fields N / --rlines N   record thresholds (default 12 fields / 60 lines)
  --top K      only print the K worst (by score) declarations
  --check      exit 1 if a flagged declaration is not listed in the baseline (see below)
  --baseline   file with one `module.name` per line: known offenders that --check tolerates
               (default scripts/longdecls.baseline; lines starting with # are comments)
"""
import os, re, sys, argparse

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
SRC = os.path.join(ROOT, 'src')
CONTAINERS = ('abstract', 'private', 'instance', 'module', 'record', 'data', 'open', 'import', 'where', 'field', 'pattern')

def strip_comments(text):
    """Blank out {- -} block comments (nested) while keeping line structure."""
    out, depth, i = [], 0, 0
    while i < len(text):
        two = text[i:i + 2]
        if two == '{-' and text[i:i + 3] != '{-#':
            depth += 1; out.append('  '); i += 2
        elif two == '-}' and depth:
            depth -= 1; out.append('  '); i += 2
        else:
            out.append(text[i] if depth == 0 or text[i] == '\n' else ' '); i += 1
    return ''.join(out)

def first_token(s):
    m = re.match(r'\s*(\S+)', s)
    return m.group(1) if m else ''

def decls(path):
    text = strip_comments(open(path).read())
    cur = None   # [name, indent, start_line, lines, chars, maxwidth, fields]
    out = []
    def flush():
        if cur and cur[3] > 0:
            # a record literal `{ f = … ; g = … }` is measured by its largest field, not by its total length
            fs = [f for f in cur[6] if f]
            if len(fs) >= 5: cur[3], cur[4] = max(f[0] for f in fs), max(f[1] for f in fs)
            out.append(tuple(cur[:6]))
    for n, raw in enumerate(text.split('\n'), 1):
        line = re.sub(r'\s--(\s.*)?$', '', raw.rstrip()) if re.search(r'\s--(\s|$)', raw) else raw.rstrip()
        if not line.strip() or line.lstrip().startswith('--') or line.lstrip().startswith('{-#'): continue
        ind = len(line) - len(line.lstrip())
        tok = first_token(line)
        continues = cur is not None and (ind > cur[1] or tok == cur[0])
        if cur is not None and cur[0] is None and ind > cur[1]:
            continues = False            # first child of a container starts a new declaration
        if not continues:
            flush()
            cur = [None if tok in CONTAINERS else tok, ind, n, 0, 0, 0, []]
            if tok in CONTAINERS and not re.search(r'\bwhere\b.*\S|=', line.split('where', 1)[-1] if 'where' in line else ''):
                cur[0] = None
        cur[3] += 1; cur[4] += len(line.strip()); cur[5] = max(cur[5], len(line.strip()))
        if tok in (';', '{'): cur[6].append([0, 0])
        if cur[6]: cur[6][-1][0] += 1; cur[6][-1][1] += len(line.strip())
    flush()
    return [d for d in out if d[0] and d[0] != '...']   # `...` clauses continue the preceding declaration

def records(path):
    """Yield (name, start_line, lines, fields) for each `record NAME` declaration.  `fields` counts the field
    declarations (`x y : T` entries at the indentation of the first line after a `field` keyword); `lines` counts
    the code lines of the header and of the `field` blocks (definitions and lemmas derived from the fields are
    not part of what an instance must supply, so they do not count)."""
    rows = []
    text = strip_comments(open(path).read()).split('\n')
    i = 0
    while i < len(text):
        m = re.match(r'(\s*)record\s+(\S+)', text[i])
        if not m or not re.search(r'\bwhere\b|\S\s*$', text[i]):
            i += 1; continue
        ind, name, start = len(m.group(1)), m.group(2), i + 1
        lines = fields = 0
        fcol = None
        infield, afterfield = True, False   # the header counts
        j = i
        while j < len(text):
            raw = text[j].rstrip()
            code = re.sub(r'\s--(\s.*)?$', '', raw)
            s = code.strip()
            if s and not s.startswith('--') and not s.startswith('{-#'):
                cur = len(code) - len(code.lstrip())
                if j > i and cur <= ind: break
                if s == 'field': infield, fcol, afterfield = True, None, True
                elif afterfield: fcol, afterfield = cur, False
                elif fcol is not None and cur < fcol: infield = False
                if infield: lines += 1
                if infield and fcol is not None and cur == fcol and re.search(r'\s:\s|\s:$', code): fields += 1
                if s.startswith('field ') and ':' in s: fields += 1
            j += 1
        rows.append((name, start, lines, fields))
        i = j if j > i else i + 1
    return rows

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lines', type=int, default=18); ap.add_argument('--chars', type=int, default=1000)
    ap.add_argument('--width', type=int, default=130); ap.add_argument('--top', type=int, default=0)
    ap.add_argument('--fields', type=int, default=12); ap.add_argument('--rlines', type=int, default=60)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--baseline', default=os.path.join(ROOT, 'scripts', 'longdecls.baseline'))
    ap.add_argument('paths', nargs='*')
    a = ap.parse_args()
    files = []
    for p in a.paths or [os.path.join(SRC, 'QBS')]:
        if os.path.isdir(p):
            for d, _, fs in os.walk(p): files += [os.path.join(d, f) for f in fs if f.endswith('.agda')]
        else: files.append(p)
    rows = []
    for f in sorted(files):
        mod = os.path.relpath(f, SRC)[:-5].replace(os.sep, '.')
        for name, ind, start, lines, chars, width in decls(f):
            if lines > a.lines or chars > a.chars or width > a.width:
                score = max(lines / a.lines, chars / a.chars, width / a.width)
                rows.append((score, mod, name, start, lines, chars, width, None))
        for name, start, lines, fields in records(f):
            if fields > a.fields or lines > a.rlines:
                score = max(fields / a.fields, lines / a.rlines)
                rows.append((score, mod, name, start, lines, 0, 0, f'record with {fields} fields'))
    rows.sort(reverse=True)
    base = set()
    if a.check and os.path.exists(a.baseline):
        base = {l.strip() for l in open(a.baseline) if l.strip() and not l.startswith('#')}
    shown = rows[:a.top] if a.top else rows
    bad = 0
    for score, mod, name, start, lines, chars, width, rec in shown:
        known = f'{mod}.{name}' in base
        bad += not known
        detail = f'{lines} lines, {rec}' if rec else f'{lines} lines, {chars} chars, widest {width}'
        print(f'{score:5.1f}  {mod}.{name}  (line {start}: {detail})' + ('  [baseline]' if known else ''))
    print(f'{len(rows)} flagged declaration(s)', file=sys.stderr)
    if a.check and bad: sys.exit(1)

if __name__ == '__main__':
    main()
