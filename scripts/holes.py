#!/usr/bin/env python3
"""Count the interaction holes (`?`) in Agda files, ignoring comments and string literals.

Used by `make progress`: with --allow-unsolved-metas Agda prints nothing about holes, so they are
counted from the source instead.  Usage: holes.py FILE...  (prints `FILE COUNT` for files with holes)."""
import re
import sys

# a hole is a standalone `?` token (not part of an operator such as `_<?_` or `_≟?_`)
HOLE = re.compile(r"(?<![^\s(){};,\[\]])\?(?![^\s(){};,\[\]])")


def strip(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if depth == 0 and two == "--" and (i == 0 or src[i - 1].isspace()):
            while i < n and src[i] != "\n":
                i += 1
        elif two == "{-":
            depth += 1
            i += 2
        elif depth > 0 and two == "-}":
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif src[i] == '"':
            i += 1
            while i < n and src[i] != '"':
                i += 2 if src[i] == "\\" else 1
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


for path in sys.argv[1:]:
    with open(path, encoding="utf-8") as f:
        n = len(HOLE.findall(strip(f.read())))
    if n:
        print(path, n)
