# Typecheck the qbs library (src/QBS).
#   make               same as `make check`
#   make check         strict: every module must produce no Agda output (so no unsolved holes `?`),
#                      and there are no postulates.
#   make progress      unsolved holes are tolerated (skeleton modules live at their final paths, with
#                      `--safe` in their headers).  Agda forbids --allow-unsolved-metas together with --safe,
#                      so this checks an overlay copy of src/ in _build/progress (scripts/progress-overlay.py:
#                      files with holes get --allow-unsolved-metas, their importers lose --safe).  Any other
#                      error or a postulate still fails; files with holes are listed with their counts
#                      (scripts/holes.py counts the `?` tokens, since Agda prints nothing for them).
#   make clean         delete the Agda interfaces (_build/) and the logs, for a from-scratch check.
#   make profile       typecheck from scratch with `--profile=modules` (one mode per run in Agda 2.7) and write
#                      per-module/per-definition timings to profile/ (see TODO.md, "Compile time").
#   make profile-tree  cold pass in dependency order (leaves first), each module limited to LIMIT=120 s;
#                      slow modules are killed and their dependents skipped (JOBS=N for parallel levels).
#   make profile-MODULE as above for one module, e.g. `make profile-QBS.Analysis.Riesz`; the
#                      interfaces of its dependencies are reused.
#   make -j N ...      runs N modules at once.  Modules whose interfaces are missing are checked by
#                      their dependents' agda runs too, so run `make all-interfaces` once first if
#                      parallel runs race on a cold _build.
# Needs Agda 2.7.0.1 with the libraries `standard-library` (v2.3) and `agda-categories`
# (v0.2.0 + 232 commits, c2e7c13e) registered in ~/.agda/libraries (qbs.agda-lib depends on them).
# Agda finds qbs.agda-lib in this directory.

AGDA    ?= agda
HOLES   ?= scripts/holes.py
PROGDIR := _build/progress
SRC     := src
LOGDIR  := _build/logs
PROFDIR := profile
FILES   := $(sort $(shell find $(SRC) -name '*.agda'))
MODULES := $(FILES:$(SRC)/%.agda=%)
LOGS    := $(FILES:$(SRC)/%.agda=$(LOGDIR)/%.log)

.PHONY: check progress report clean all-interfaces profile profile-tree
.DELETE_ON_ERROR:

# `check` is strict.  `progress` prepares the overlay and runs the same report inside it.
check:
	@$(MAKE) --no-print-directory report MODE=strict
progress:
	@python3 scripts/progress-overlay.py $(SRC) $(PROGDIR)
	@$(MAKE) --no-print-directory -C $(PROGDIR) -f $(CURDIR)/Makefile report MODE=progress SRC=src HOLES=$(CURDIR)/scripts/holes.py

# One log per module: the Agda output minus the "Checking" lines.  Any source change re-runs every
# module (Agda itself reuses unchanged interfaces, so this is cheap).
$(LOGDIR)/%.log: $(SRC)/%.agda $(FILES)
	@mkdir -p $(dir $@)
	@echo "agda $<"
	@$(AGDA) $< 2>&1 | grep -v Checking > $@ || true

all-interfaces:
	@for f in $(FILES); do $(AGDA) $$f >/dev/null 2>&1 || true; done

# Read the logs and apply the strict/progress policy.
report: $(LOGS)
	@fails=0; holes=0; \
	for f in $(FILES); do \
	  log=$(LOGDIR)/$${f#$(SRC)/}; log=$${log%.agda}.log; \
	  if [ "$(MODE)" = progress ]; then \
	    n=$$(python3 $(HOLES) $$f | awk '{print $$2}'); \
	    if [ -n "$$n" ]; then echo "holes: $$f ($$n)"; holes=$$((holes + n)); fi; \
	  fi; \
	  [ -s $$log ] || continue; \
	  echo "== $$f"; head -8 $$log; fails=$$((fails + 1)); \
	done; \
	if grep -rlE 'postulate|\{!' $(SRC) --include='*.agda'; then \
	  echo "postulate or hole found"; fails=$$((fails + 1)); fi; \
	echo "files: $(words $(FILES)), holes: $$holes, failures: $$fails"; \
	[ $$fails -eq 0 ]

clean:
	rm -rf _build $(PROFDIR)

# Profiling.  Agda 2.7 allows one --profile mode at a time (modules | definitions | internal).
# `make profile` is the cold per-module baseline (mode `modules`, plus `+RTS -s` GC/memory totals);
# `make profile-QBS.X.Y` re-checks one module (its interface is deleted first, dependencies are
# reused) once per mode and writes profile/QBS/X/Y.{modules,definitions,internal}.txt.
PROFMODES := modules definitions internal

# Dependency-ordered, time-limited pass: every module individually, leaves of the import graph first,
# killed after LIMIT seconds (then SLOW; its dependents are skipped).  Resumable; see the script.
LIMIT ?= 120
profile-tree:
	python3 scripts/profile-tree.py --limit $(LIMIT) --agda $(AGDA) --out $(PROFDIR) --jobs $(or $(JOBS),1)

profile: clean
	@mkdir -p $(PROFDIR)
	@for f in $(FILES); do \
	  m=$${f#$(SRC)/}; m=$${m%.agda}; mkdir -p $(PROFDIR)/$$(dirname $$m); \
	  echo "profile $$m"; \
	  /usr/bin/time -p $(AGDA) --profile=modules $$f +RTS -s -RTS \
	    > $(PROFDIR)/$$m.modules.txt 2>&1 || echo "FAILED: $$m"; \
	done
	@echo "slowest first: grep -H '^real' -r $(PROFDIR) | sort -k2 -n -r | head"

profile-%:
	@p=$$(echo '$*' | tr . /); mkdir -p $(PROFDIR)/$$(dirname $$p); \
	for mode in $(PROFMODES); do \
	  find _build -path "*/$$p.agdai" -delete; \
	  echo "== $$mode"; \
	  /usr/bin/time -p $(AGDA) --profile=$$mode $(SRC)/$$p.agda +RTS -s -RTS 2>&1 \
	    | tee $(PROFDIR)/$$p.$$mode.txt; \
	done
