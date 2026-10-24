#!/bin/sh
# Typecheck the qbs library (src/QBS).
#   sh qbs/check.sh              strict: every module must produce no Agda output (so no unsolved
#                                         holes `?`), and there are no postulates.
#   sh qbs/check.sh --clean      deletes the interfaces (_build/) first, for a from-scratch check
#                                         (otherwise Agda reuses them; combine with --progress as needed).
#   sh qbs/check.sh --progress   unsolved holes are tolerated (skeleton modules live at their final
#                                         paths); any other error or a postulate still fails, and the files
#                                         with holes are listed with their hole counts.
# Needs Agda 2.7.0.1 with the libraries `standard-library` (v2.3) and `agda-categories`
# (v0.2.0 + 232 commits, c2e7c13e) registered in ~/.agda/libraries (qbs.agda-lib depends on them).
# Run from anywhere; it runs in qbs/, where Agda finds qbs.agda-lib.
set -u
cd "$(dirname "$0")"
progress=0
for a in "$@"; do
  case "$a" in
    --progress) progress=1 ;;
    --clean) rm -rf _build ;;
  esac
done
fails=0
holes=0
for f in $(find src -name '*.agda' | sort); do
  out=$(agda "$f" 2>&1 | grep -v Checking)
  [ -z "$out" ] && continue
  if [ "$progress" -eq 1 ]; then
    # unsolved holes are expected; anything else is an error
    other=$(echo "$out" | grep -v -E '^(Unsolved (interaction )?metas|  /.*\.agda:[0-9,-]+$|$)')
    n=$(echo "$out" | grep -c -E '^  /.*\.agda:[0-9,-]+$')
    if [ -z "$other" ]; then
      echo "holes: $f ($n)"; holes=$((holes + n)); continue
    fi
    out=$other
  fi
  echo "== $f"; echo "$out" | head -8; fails=$((fails + 1))
done
if grep -rlE 'postulate|\{!' src --include='*.agda'; then
  echo "postulate or hole found"; fails=$((fails + 1))
fi
echo "files: $(find src -name '*.agda' | wc -l), holes: $holes, failures: $fails"
[ "$fails" -eq 0 ]
