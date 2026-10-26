#!/usr/bin/env python3
"""Prepare the overlay that `make progress` checks.

Agda forbids `--allow-unsolved-metas` together with `--safe`, and a module with open holes cannot be
imported at all unless that flag is on; but a non-`--safe` module cannot be imported from a `--safe` one.
So the sources keep `--safe`, and `make progress` checks a copy of `src/` (in OUT/src) in which

  * every file that has holes (`scripts/holes.py`) gets `--allow-unsolved-metas` instead of `--safe`, and
  * every file that (transitively) imports such a file just loses `--safe`.

Usage: progress-overlay.py SRC OUT      (also writes OUT/qbs.agda-lib).  Files are rewritten only when their
content changes, so Agda and make keep their caches between runs."""
import os
import re
import subprocess
import sys

src, out = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))

files = sorted(os.path.join(d, f) for d, _, fs in os.walk(src) for f in fs if f.endswith(".agda"))
mod = lambda p: os.path.relpath(p, src)[: -len(".agda")].replace(os.sep, ".")
by_mod = {mod(p): p for p in files}

imports = {}
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)", re.M)
for p in files:
    with open(p, encoding="utf-8") as f:
        imports[p] = [by_mod[m] for m in IMPORT.findall(f.read()) if m in by_mod]

holey = set()
res = subprocess.run([sys.executable, os.path.join(here, "holes.py")] + files, capture_output=True, text=True, check=True)
for line in res.stdout.splitlines():
    holey.add(line.rsplit(" ", 1)[0])

unsafe = set(holey)
changed = True
while changed:
    changed = False
    for p in files:
        if p not in unsafe and any(q in unsafe for q in imports[p]):
            unsafe.add(p)
            changed = True


def write_if_changed(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            if f.read() == text:
                return
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


keep = set()
for p in files:
    with open(p, encoding="utf-8") as f:
        text = f.read()
    if p in unsafe:
        flag = "--allow-unsolved-metas" if p in holey else ""
        new = re.sub(r"(\{-# OPTIONS\b[^#]*?)--safe\s*", lambda m: m.group(1) + (flag + " " if flag else ""), text, count=1)
        new = re.sub(r"\{-# OPTIONS\s*#-\}\n?", "", new, count=1)
        if new == text:
            sys.exit("no `--safe` OPTIONS pragma in %s" % p)
        text = new
    dst = os.path.join(out, p)
    keep.add(os.path.abspath(dst))
    write_if_changed(dst, text)

for d, _, fs in os.walk(os.path.join(out, src)):
    for f in fs:
        if f.endswith(".agda") and os.path.abspath(os.path.join(d, f)) not in keep:
            os.remove(os.path.join(d, f))

with open("qbs.agda-lib", encoding="utf-8") as f:
    write_if_changed(os.path.join(out, "qbs.agda-lib"), f.read())

print("progress overlay: %d files, %d with holes, %d without --safe" % (len(files), len(holey), len(unsafe)))
