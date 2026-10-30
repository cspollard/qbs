# Plan 1: documentation for navigating the high-level interface

## Goal
A reader (human or model) should be able to state and prove a new statistical result, e.g. "the sample mean of
n iid draws is unbiased", after reading only a short guide, without opening the roughly 17k lines in 120 modules.

## Where we are
`README.md` (468 lines) describes each layer well, but it has these weaknesses for navigation:
- It is organised as a history of the construction (fair coin, then Riesz, then uniform, then conditioning, ...).
  There is no task-oriented entry point such as "I want to write a program and compute an expectation".
- The abstract interface is described module by module in prose. Types are not shown.
  `StatisticalInterface` has 34 fields; there is no cheat sheet of the ones a user needs.
- There is no list of the public names a user imports (`∫`, `law`, `score`, `normalize`, `condition`, ...) with
  their types and the module they live in.
- Two states of the project are described inconsistently: README "The s-finite monad (in progress)" and
  TODO.md's "Audit" section describe holes that have since been filled.
  (`make check` now passes with 0 holes.)
- It is unclear which layer a user should target: abstract `IsStatisticalQBSLike`, the discrete model, or the
  continuous model. Which examples work at which level is not stated.
- `Docs/` and `docs/` are the same directory on macOS and would collide on Linux.
  Settle on one (see Step 0).

## Steps

0. **Housekeeping.** Pick `docs/` (lowercase, matching the request) and move `Docs/*` into it with `git mv`.
   Mark `TODO.md`'s audit section as historical, and update the README "in progress" section.
   Cost: under an hour.

1. **`docs/Guide.md`: task-oriented tour (about 150 lines).** Sections:
   - "Write a probabilistic program": a minimal example from `Example/Program.agda`, with imports.
   - "Compute an expectation": the integral and where it is defined for each model.
   - "Condition on data": `score`, `condition`, `normalize`, with the Bayes example.
   - "Which model do I use?": a decision table (abstract / discrete / continuous / s-finite), what each supports,
     and which hypotheses (`lem`, `funext`) each needs. Link to `Docs/Classical.md`.
   Each snippet should be copied from a module that typechecks. Step 5 enforces this.

2. **`docs/Interface.md`: the public API (about 200 lines).** For each of `Probability`, `Statistical`,
   `Model.*`, `Continuous.SFiniteStat`, `Analysis.Lebesgue`, and `Example.*`:
   the 5–15 names a user needs, each with its type signature and a one-line meaning.
   Include a "field groups" breakdown of `StatisticalInterface`'s 34 fields: weights, measures, scoring,
   sums and scaling, normalisation. Mark which fields are the laws and which are the operations.
   Generate the signature list with a script from the Agda sources, not by hand (see Step 5).

3. **`docs/Architecture.md`: module dependency map.** A layered diagram of module dependencies and a short
   "if you change X, these rebuild" table. Include approximate compile times (the README already records some)
   and the hypothesis chain from `Docs/Classical.md` §5.

4. **Module header convention.** Every `src/QBS/**/*.agda` gets a header comment of at most 6 lines:
   one-sentence purpose, main exports, hypotheses used (`lem`/`funext`), and the paper it follows (if any).
   About 120 files. Many already have comments; audit with a script and fill the gaps.

5. **Keep docs honest.**
   - `scripts/signatures.py`: extracts top-level signatures for named exports and writes the tables in
     `Interface.md` between marker comments.
   - Guide snippets are included from real files (a marked region in `Example/*.agda`) so CI breaks when they drift.
   - Add a doc-lint to `make check`: every module has a header, every listed name still exists.

6. **Test of the docs.** Hand a fresh session only `Guide.md` and `Interface.md`, and ask it to state (not
   prove) a new theorem, such as "expected value of Bernoulli(p) is p", in Agda against the real names.
   Whatever it needs to look up elsewhere is a docs bug. Repeat after Plan 2 and 3 land.

## Effort and order
Steps 0 and 1: about a day. Steps 2 and 4: about two days. Step 5: about a day. Steps 3 and 6: half a day each.
Do Steps 0–2 and 6 before Plan 2 (they directly de-risk it) and the rest in parallel with Plan 2.

## Done when
A fresh session can write the *statement* of the Plan 2 results using only `docs/`, and CI fails when a
documented name disappears.

## Risks and open points
- Signature extraction from Agda is fragile (multi-line types, `private` blocks). Prefer `agda --html` or the
  `agda-mcp` module summary over regexes, and decide after a spike.
- I judged the current docs from the README, TODO, and a few module headers only. Step 6 is the real test.
