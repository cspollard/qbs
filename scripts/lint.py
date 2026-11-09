# IMPORTANT
# THIS FILE DOES NOT YET DO WHAT IT SHOULD

import argparse
import json
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass
from typing import List, Optional, Tuple

MAX_WIDTH = 80
INDENT = "  "

@dataclass
class OperatorInfo:
  name: str
  start: int
  end: int
  fixity: Optional[str] = None
  precedence: Optional[int] = None


class AgdaBridge:
  """Interacts with `agda --interaction-json` to query semantic metadata."""

  def __init__(self, agda_bin: str = "agda"):
    self.agda_bin = agda_bin
    self.process = subprocess.Popen(
        [self.agda_bin, "--interaction-json"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        bufsize=1,
    )

  def send(self, cmd: str) -> None:
    if self.process.stdin:
      self.process.stdin.write(cmd + "\n")
      self.process.stdin.flush()

  def load_file(self, file_path: str) -> List[dict]:
    escaped = file_path.replace('"', '\\"')
    cmd = (
        f'IOTCM "{escaped}" NonInteractive Direct (Cmd_load'
        f' "{escaped}" [])'
    )
    self.send(cmd)

    responses = []
    while True:
      line = self.process.stdout.readline()
      if not line:
        break
      line = line.strip()
      if not line:
        continue
      if line.startswith("JSON>"):
        line = line[len("JSON>") :].strip()
      try:
        data = json.loads(line)
        responses.append(data)
        if data.get("kind") == "DisplayInfo":
          info_kind = data.get("info", {}).get("kind")
          if info_kind in ("AllGoalsWarnings", "Error"):
            break
      except json.JSONDecodeError:
        continue
    return responses

  def get_operator_tokens(
      self, file_path: str, source_text: str
  ) -> List[OperatorInfo]:
    events = self.load_file(file_path)
    operators: List[OperatorInfo] = []

    for ev in events:
      if ev.get("kind") != "HighlightingInfo":
        continue
      payload = ev.get("info", {}).get("payload", [])
      for item in payload:
        aspects = item.get("aspects", [])
        if "operator" in aspects:
          # Agda offsets are 1-based [start, end)
          start = item.get("range", [0, 0])[0] - 1
          end = item.get("range", [0, 0])[1] - 1
          if 0 <= start < end <= len(source_text):
            op_text = source_text[start:end]
            operators.append(OperatorInfo(name=op_text, start=start, end=end))
    return operators

  def close(self) -> None:
    self.process.terminate()
    self.process.wait()


def visual_width(text: str) -> int:
  return sum(
      2 if unicodedata.east_asian_width(c) in ("W", "F") else 1 for c in text
  )


COMMENT_RE = re.compile(r"^(\s*)--( *)(.*?)\s*$")
BULLET_RE = re.compile(r"^([*+•-]|\d+[.)])\s")


def set_width(width: int) -> None:
  global MAX_WIDTH
  MAX_WIDTH = width


def is_comment_line(line: str) -> bool:
  return line.strip().startswith("--")


def is_verbatim_comment(body: str) -> bool:
  """Comment bodies that must not be refilled: horizontal rules, `from:`
  excerpt markers, and lines with aligned columns.  A double space after
  sentence punctuation is prose; any other run of 2+ spaces is alignment."""
  return (
      bool(re.match(r"^-+$", body))
      or body.startswith("from:")
      or bool(re.search(r"[^.?!:;)] {2,}|\S {3,}", body))
  )


Word = Tuple[str, bool]  # (text, followed by a double space in the source)


def split_words(body: str) -> List[Word]:
  """Words of `body`, remembering sentence-style double spaces."""
  return [
      (m.group(1), len(m.group(2)) >= 2)
      for m in re.finditer(r"(\S+)( *)", body)
  ]


def fill_words(
    first: str, cont: str, words: List[Word], width: int
) -> List[str]:
  """Greedy fill; `first`/`cont` prefix the first/later lines.  A double
  space after a word ending in `.`, `?` or `!` is kept inside a line."""
  out: List[str] = []
  cur, sep = first + words[0][0], words[0][1]
  for text, dbl in words[1:]:
    gap = "  " if sep and cur[-1] in ".?!" else " "
    cand = cur + gap + text
    if visual_width(cand) <= width:
      cur = cand
    else:
      out.append(cur)
      cur = cont + text
    sep = dbl
  out.append(cur)
  return out


def reflow_comment_block(
    lines: List[str], width: Optional[int] = None
) -> List[str]:
  """Refill a run of consecutive `--` lines (same leading whitespace) to
  `width` columns.  Paragraphs (split at blank `--` lines), bullet items,
  differently indented lines, rules and aligned lines are never merged."""
  w_max: int = MAX_WIDTH if width is None else width
  out: List[str] = []
  # Pending paragraph: (first prefix, continuation prefix, words).
  cur: Optional[Tuple[str, str, List[Word]]] = None

  def flush() -> None:
    nonlocal cur
    if cur is not None:
      first, cont, words = cur
      out.extend(fill_words(first, cont, words, w_max))
      cur = None

  for line in lines:
    m = COMMENT_RE.match(line)
    if not m:
      flush()
      out.append(line)
      continue
    lead, sp, body = m.groups()
    # Deep indentation (8+) marks a table row or its continuation: keep as is.
    if not body or len(sp) >= 8 or is_verbatim_comment(body):
      flush()
      out.append(line.rstrip())
      continue
    base = f"{lead}--"
    bm = BULLET_RE.match(body + " ")
    if bm:
      flush()
      marker = bm.group(1)
      first = f"{base}{sp}{marker} "
      cont = f"{base}{sp}{' ' * (len(marker) + 1)}"
      cur = (first, cont, split_words(body[len(marker):]))
      if not cur[2]:
        out.append(line.rstrip())
        cur = None
      continue
    if cur is not None and cur[1] == f"{base}{sp}":
      cur[2].extend(split_words(body))
    else:
      flush()
      cur = (f"{base}{sp}", f"{base}{sp}", split_words(body))
  flush()
  return out


def format_record(line: str) -> List[str]:
  pat = r"^(\s*)([a-zA-Z0-9_\'-]+)\s*=\s*record\s*\{\s*(.*?)\s*\}\s*$"
  m = re.match(pat, line)
  if not m or (visual_width(line) <= MAX_WIDTH and ";" not in m.group(3)):
    return [line]
  base, name, body = m.group(1), m.group(2), m.group(3)
  fields = [f.strip() for f in body.split(";") if f.strip()]
  if not fields:
    return [line]
  return (
      [f"{base}{name} =", f"{base}{INDENT}record", f"{base}{INDENT}{{ {fields[0]}"]
      + [f"{base}{INDENT}; {f}" for f in fields[1:]]
      + [f"{base}{INDENT}}}"]
  )


def format_sig(sig_lines: List[str]) -> List[str]:
  full = " ".join(line.strip() for line in sig_lines)
  if ":" not in full or (len(sig_lines) == 1 and visual_width(full) <= MAX_WIDTH):
    return sig_lines
  name, type_body = (s.strip() for s in full.split(":", 1))

  parts, cur, depth, i = [], [], 0, 0
  while i < len(type_body):
    ch = type_body[i]
    if ch in "({[":
      depth += 1
      cur.append(ch)
    elif ch in ")}]":
      depth = max(0, depth - 1)
      cur.append(ch)
    elif depth == 0 and type_body[i : i + 3] == "\\to":
      parts.append(("part", "".join(cur).strip()))
      parts.append(("arrow", "\\to"))
      cur, i = [], i + 2
    elif depth == 0 and ch == "→":
      parts.append(("part", "".join(cur).strip()))
      parts.append(("arrow", "→"))
      cur = []
    else:
      cur.append(ch)
    i += 1
  if cur:
    parts.append(("part", "".join(cur).strip()))

  out = [name, f"{INDENT}: {parts[0][1]}"]
  j = 1
  while j < len(parts):
    kind, val = parts[j]
    if kind == "arrow":
      nxt = parts[j + 1][1] if j + 1 < len(parts) else ""
      out.append(f"{INDENT}{val} {nxt}")
      j += 1
    elif kind == "part":
      out.append(f"{INDENT}{val}")
    j += 1
  return out


def lint_with_agda(file_path: str, agda_bin: str = "agda") -> str:
  with open(file_path, "r", encoding="utf-8") as f:
    src = f.read()

  # 1. Query Agda compiler for exact operator boundaries
  bridge = AgdaBridge(agda_bin=agda_bin)
  try:
    ops = bridge.get_operator_tokens(file_path, src)
  finally:
    bridge.close()

  # Set of discovered operator names from Agda's scope-checker
  known_ops = {op.name for op in ops}

  raw_lines = src.splitlines()
  result_lines: List[str] = []
  i, n = 0, len(raw_lines)

  while i < n:
    line = raw_lines[i]
    stripped = line.strip()

    # Pragmas and holes
    if stripped.startswith("{-#") or stripped.startswith("{!"):
      result_lines.append(line)
      i += 1
      continue

    # Comment reflowing
    if stripped.startswith("--"):
      lead = line[: len(line) - len(line.lstrip())]
      j = i
      while (
          j < n
          and is_comment_line(raw_lines[j])
          and raw_lines[j].startswith(lead)
          and not raw_lines[j][len(lead) :].startswith((" ", "\t"))
      ):
        j += 1
      result_lines.extend(reflow_comment_block(raw_lines[i:j]))
      i = j
      continue

    # Records
    if "= record" in line:
      rec = format_record(line)
      if rec != [line]:
        result_lines.extend(rec)
        i += 1
        continue

    # Type signatures
    if re.match(r"^([a-zA-Z0-9_\'-]+)\s*:(.*)$", line) and not line.startswith(" "):
      sig_block = [line]
      while (
          i + 1 < n
          and raw_lines[i + 1].startswith(" ")
          and ("=" not in raw_lines[i + 1])
      ):
        i += 1
        sig_block.append(raw_lines[i])
      result_lines.extend(format_sig(sig_block))
      i += 1
      continue

    # Operator line breaks driven by Agda-resolved operators
    if visual_width(line) > MAX_WIDTH and known_ops:
      escaped = [re.escape(op) for op in sorted(known_ops, key=len, reverse=True)]
      pat = r"\s+(" + "|".join(escaped) + r")\s+"
      parts = re.split(pat, line)
      if len(parts) > 1:
        base_ind = re.match(r"^(\s*)", line).group(1)
        result_lines.append(parts[0])
        for k in range(1, len(parts), 2):
          op_sym = parts[k]
          operand = parts[k + 1].strip() if k + 1 < len(parts) else ""
          result_lines.append(f"{base_ind}{INDENT}{op_sym} {operand}")
        i += 1
        continue

    result_lines.append(line)
    i += 1

  return "\n".join(result_lines) + ("\n" if src.endswith("\n") else "")


def main(argv: Optional[List[str]] = None) -> int:
  parser = argparse.ArgumentParser(
      description="Reformat Agda files (prints the result unless --write)."
  )
  parser.add_argument("files", nargs="+", help="Agda files to lint")
  parser.add_argument(
      "-w", "--write", action="store_true", help="rewrite files in place"
  )
  parser.add_argument(
      "-c",
      "--check",
      action="store_true",
      help="exit 1 if any file would change; write nothing",
  )
  parser.add_argument("--agda", default="agda", help="agda executable")
  parser.add_argument(
      "--width", type=int, default=MAX_WIDTH, help="line width (default 80)"
  )
  args = parser.parse_args(argv)
  set_width(args.width)

  changed = False
  for path in args.files:
    with open(path, encoding="utf-8") as f:
      original = f.read()
    result = lint_with_agda(path, args.agda)
    if result != original:
      changed = True
    if args.check:
      if result != original:
        print(f"would reformat {path}", file=sys.stderr)
    elif args.write:
      if result != original:
        with open(path, "w", encoding="utf-8") as f:
          f.write(result)
        print(f"reformatted {path}", file=sys.stderr)
    else:
      sys.stdout.write(result)
  return 1 if (args.check and changed) else 0


if __name__ == "__main__":
  sys.exit(main())
