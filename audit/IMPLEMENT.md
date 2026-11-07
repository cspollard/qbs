# Implementing the audit

This is the brief for the agents that carry out the audit's recommendations. They run one at a time, each in its own
git worktree. The orchestrator verifies and merges each agent's branch before starting the next.

Read [SUMMARY.md](SUMMARY.md) first: it gives the cross-cutting themes that every agent should keep in mind.

## Order and rationale

| # | Agent | Why here |
|---|---|---|
| 0 | `global-cleanup` | The exact duplicates span domains. If domain agents fixed them, each would pick its own shared home and they would conflict. Removing them first gives later agents one place to import from. |
| 1 | `lower-reals` | Everything else imports Ω, cuts and `RationalLemmas`, so its layout should settle first. |
| 2 | `abstract` | Provides the bind/Kleisli vocabulary and the generic strong-monad lemmas, which `discrete`, `continuous-core` and `inference` will use. |
| 3 | `discrete` | Depends only on 1 and 2. It is a small domain and a good test of the brief. |
| 4 | `measure-construction` | Provides the Dynkin-class combinator, `_≈ₘ_`, and `push-id`/`push-∘`, which the continuous domains use. |
| 5 | `analysis-real` | Retires the certificate packs in favour of `Deriv*`. This must come before `continuous-distributions`, which moves its moment proofs onto `Deriv*`. |
| 6 | `continuous-core` | Uses 2 (strength lemmas) and 4. Provides the s-finite monad and product layer that 7–10 import. |
| 7 | `continuous-lebesgue` | Owns "ν is Lebesgue measure" and the Fatou-first convergence layer. Distributions builds on both. |
| 8 | `continuous-distributions` | Owns the shared `withDensity` recipe and the location–scale law. |
| 9 | `continuous-signed-info` | Adopts `withDensity` from 8 for reweighting and exponential tilting, and bundles `FinTs`. |
| 10 | `inference` | Sits on top of everything. It states Bayes once at the abstract layer and adopts the vocabulary of 2 and 8. |
| 11 | `reader-guide` | A final documentation pass. It joins the per-domain roadmap entries into one reader's map in `Guide.md`/`Interface.md` and checks that the README points into it. |

Within each domain agent, the work goes in tiers, with one or more commits per tier and in this order:

- **A. Documentation:** headers, roadmap entries, and the "plan N" references.
- **B. Dead code and exact duplicates.**
- **C. Retire superseded proof routes.**
- **D. Generic constructions.**
- **E. Renames and module merges.**

Documentation comes first because it carries no risk, and it is the audit's main aim. Renames and merges come last
in each domain because they change imports. Because only one agent runs at a time, renames cannot cause merge
conflicts, so they do not need to wait until the end of the whole programme. If an agent runs short of budget, it
stops at a tier boundary and reports what is left.

## Common brief (applies to every agent)

### Setup

- You are working in a fresh git worktree of `/Users/cspollard/Programming/qbs`, on your own branch. Before checking
  anything, seed the build cache from the main checkout:
  `cp -cR /Users/cspollard/Programming/qbs/_build .`
- Read these files:
  - `docs/Contributing.md`, especially "For LLM agents".
  - `audit/SUMMARY.md`, this file, and your domain's report `audit/<domain>.md`.
  - `plans/Simplify.md`, an earlier simplification audit. Do not redo items it marks done, and do not retry items it
    closed. For example, defining `QBSCat` as a `SubCategory` made `SFiniteStat` take more than 19 minutes.

### Scope

- Work only on your domain's modules, as listed in `audit/README.md` under "Domains". There are two exceptions:
  - You may edit modules outside your domain when the edit only follows a rename, removal or move that you made (for
    example, changing an import or a lemma name).
  - You may also migrate modules outside your domain when your domain's report says to, for example when
    `analysis-real` retires a certificate pack that other modules still use.
- Shared documents (`docs/Interface.md`, `docs/Guide.md`, `docs/Modules.md`) may be edited, but only in your domain's
  sections, plus new entries for your domain.
- The audit reports came from reading, not from running Agda. Before acting on any finding, confirm it against the
  code. Duplicates must really be the same statement, and anything called derivable must really derive. If a finding
  is wrong, skip it and record why.
- Keep the mathematics. Never weaken or change the statement of a result. Only these changes are allowed:
  - rename a result;
  - generalise it so that every old use still follows directly;
  - delete a superseded route once nothing imports it, or once its importers have been moved to the kept route.
- Never add postulates, change `OPTIONS` or the agda-lib flags, use `rewrite`, or touch `train.py` or
  `plr_reference.py`.

### Defaults (until the maintainer decides otherwise)

- **Renames are allowed.** Update every importer, and do not leave re-export stub modules behind. List each
  old → new name in your report and in the `Modules.md` regeneration (`python3 scripts/modindex.py`).
- **Superseded routes:** delete them when the kept route proves the same statement. Record the deletion in the domain
  report's status section, so the history is findable through git.
- **Kleisli:** use a local, named bind or composition (`bind k t = μ ∘ M k ∘ t`, or `_>>=ᵖ_`) defined once in the
  abstract layer. Do not import `Categories.Category.Construction.Kleisli` unless it makes a proof shorter.
- **Categorical language:** follow the "Categorical language: consensus" section of SUMMARY.md. Name standard
  structures in headers and docs. Use agda-categories or stdlib bundles where they already fit. Do not build
  colimit, semimodule or `Categories.Monad` encodings that the reports advise against.

### Checking (run from the CLI)

Use this command, with the module path relative to `src/`:

```bash
/usr/bin/time -l perl -e 'alarm 900; exec @ARGV' agda +RTS -M3G -RTS src/QBS/Path/Module.agda
```

Look at the exit status and the output: there must be no `Unsolved` and no `error`. A run that is killed by the
900-second alarm counts as a failure.

What to check:

- **Every module you edited.**
- **When a module's interface changes** (a name is removed, renamed, moved or retyped): `grep -rn` for every use, then
  check each module that used it.
- **When only proofs change:** the module itself is enough.
- **Final verification pass**, after your last commit: re-check every module you edited, plus every module that
  mentions a name you added, moved, renamed or removed (`grep -rlw`), in one CLI loop. Report the counts (checked,
  exit 0, failed) and list any failure. The orchestrator relies on this pass and does not re-run it, so do not skip it.

Compile time and memory:

- Time each module whose proof you changed, before and after, with its own `.agdai` deleted and its dependencies
  built. Report both numbers.
- No module may go over 30 s or 2 GB unless it already did, and none may get more than 25% slower.
- When merging `*Alg`/`*Aux` modules, keep them separate wherever they isolate ring-solver calls. Merge only if the
  merged module stays within these limits.

Before each commit, run `make doccheck` and `make longcheck`. The longcheck baseline is 35 flagged; do not add to it.
After changing a header or adding, removing or renaming a module, run `python3 scripts/modindex.py`.

Never run a cold `make check` or `make progress`. Check module by module.

### Recording and reporting

- Append a section `## Implementation status (<date>)` to `audit/<domain>.md`. Give one line per recommendation:
  done, partly done, skipped (with the reason), or wrong (with the evidence).
- Commit on your branch in logical commits, one or more per tier. End each message with
  `Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com>`. Do not push and do not merge.
- In your final reply, list:
  - the commits;
  - for each module checked, its exit status, time and memory, with before/after times where proofs changed;
  - the renames;
  - what you skipped;
  - anything you could not verify.

  Say so if you broke any rule.

## Agent 0: global-cleanup

This agent works across all domains on exact duplicates and dead code only. It does no renames of existing modules
and no documentation rewrites. The orchestrator has confirmed each duplicate below with grep, but you must still
confirm that the statements are identical before merging them.

1. **Classical decision toolkit.** `dec`, `dec-true`, `dec-false`, `from-true` and `dec-iff` are defined in:
   - `Model/BoolSemiring`;
   - `Model/ViterbiSemiring`;
   - `Analysis/CutSum`;
   - `Analysis/CoinIntegral`.

   Move them to one new module (for example `QBS.Classical.Decide`), parametrised the way the copies are, and import
   it everywhere.
2. **Small constants and helpers:**
   - `two`, in 7 modules;
   - `negExp-cong`, in 6;
   - `bd1`, `hm` and `half≤1`;
   - `fact`, in `BetaIntegral` and `HalfLineMomentFact`;
   - the exponential inequalities `negExp t + t·negExp t ≤ 1 ≤ negExp t + t`, in about 5 places.

   Give each one home: the lowest existing module that already has the imports it needs, such as `Half` or `Exp`.
   Prefer that over a new module.
3. **Strength helpers.** `fixH`/`fixH₂` are defined in `Continuous/Strong`, `SFiniteStrong` and `SFiniteCommute`, and
   `mapM-id` in `Continuous/FinProdPair` and `CoinCoordsJoint`. Keep one copy of each.
4. **Dead record.** Delete the unused generic record and pushforward code from `QBS.Borel.Measure`, and move `Disjoint`
   to `QBS.Borel.Core`. Update its 12 importers, which all use `using (Disjoint)`. Delete `Borel/Measure.agda` if
   nothing is left in it.
5. **Signed duplicates** (`continuous-signed-info` §4):
   - `Int-mul`: `RandomVectorDefs` re-wraps the one in `RandomVectorAlg`.
   - `Ex-law` in `RandomVectorLawAux` duplicates `SignedTransport.Ex-map`.

   Keep one of each.
6. **Misplaced ℚ lemma.** Move `CoinIntegral.smallprod`, a pure ℚ inequality, to `RationalLemmas`.

For each item, record the outcome in a new section `## Global cleanup status (<date>)` in `audit/SUMMARY.md`, not in
the domain files.

## Per-domain focus

Each agent's prompt gives its domain. These sections set the priorities and say how that domain's work fits with the
other agents'. Your domain report has the details. Where this file and the report disagree, this file wins.

### 1. lower-reals

- **A:** Write the three-layer overview (the text is in the report, §3) in `Omega.agda`'s header and as a "Number
  foundations" entry in `Interface.md`. Say that Ω is an ω-cpo with + and × Scott-continuous. Replace the "plan 03"
  headers. Explain why `RationalLemmas` exists as an adapter layer.
- **B:**
  - Name or inline the `ring₁..₇` lemmas.
  - Merge `add-sub`, `sub-add` and `ring₅`.
  - Link `hpC` and `tp` with one lemma instead of re-proving them at each use.
- **E:** Merge `Min`, `CutSplit` and `UnboundedLowerReals` into their neighbours if the timings allow.
- **Leave alone:**
  - `ExtNat` unification;
  - the ω-cpo record extraction (a header remark is enough for now);
  - moving `Cone`/`Threshold`, which the `measure-construction` agent decides.

### 2. abstract

- **A:** Write an "Abstract layer overview" covering the `IsQBSLike` stack, and better headers for `Instance`,
  `IsQBSLike` and `Core`.
- **B:**
  - Use `ProbMonad` wherever `CommutativeMonad braided` is spelled out.
  - Use one shared `braided`.
  - Move the strong-monad point lemmas (`σ-unit`, `τ-unit`, `σ-point`, `τ-point`, `ψ`, `ψ-point`) from `Fubini` into
    a generic module that agents 3, 6 and 10 can reuse.
- **D:** Define the shared bind/composition vocabulary (see Defaults) and use it in `Statistical*` and `Fubini`. State
  in its header that later agents should use it.
- **Check:** whether `sum-nat` and `sum-join` follow from `bind-sumK`.

### 3. discrete

- **A:** One entry point, `Model.Discrete` plus an overview example, and a reading order for `Example/`.
- **B:** Agent 0 has already shared the `dec*` toolkit. Remove the hand-proved `Lift Bool` semiring if stdlib gives it.
- **E:**
  - Split `StatInstance` (565 lines) as the report proposes.
  - Fold the three-line `*Model` wrappers into one module.
  - Document `WeightClass` as a sub-monad (closed under `η`, `map` and `bind`).

### 4. measure-construction

- **A:**
  - Write the measure-construction roadmap entry (the text is in the report, §3.1).
  - Fix the `fairCoin` pointer.
  - Rewrite the `CoinIntegral` header.
  - Add glossary comments for `L`, `Minor`, `Lmem`, `Sf` and `Pt`.
  - Add `Interface.md` lines for Riesz, Uniqueness, Tensor, JFubini and Regular.
- **B:**
  - Agent 0 has already deleted the `Borel.Measure` record.
  - Inline `CoinSets`.
  - Fold `Mixture` into `Cone` or `MixtureN`.
  - Check whether `Indicators.PS` is `psum` plus `∑ᶠ-⨆`.
- **D:**
  - A `DynkinClass` record for the three π–λ applications.
  - `push-id`/`push-∘` as plain lemmas.
  - A setoid `_≈ₘ_` on `Measure`, used where it shortens chains.
  - Decide whether `Cone`/`Threshold` move into this domain.
- **E:**
  - Rename the generic `Coin*` modules (for example to `Daniell/*`).
  - Split `CoinIntegral` into Add, Scale and Sup modules.
  - Consider renaming `Analysis.Measure`.
- **Leave alone:** do not merge `Fun` and `Meas`. That is a long-term aim and needs the maintainer.

### 5. analysis-real

- **A:**
  - Say in `Signed`'s header that it is the Grothendieck ring completion, delivered as a stdlib `CommutativeRing`.
  - Split the dense `Deriv` entry in `Interface.md` into a preface plus one line per rule.
- **C:** Retire the hand-written certificate packs that `Deriv*` supersedes: `PolyExpCert.Ex.pack`, `GaussCert.pack`,
  `GaussCertM1.pack1`, and most of `ExpRate`/`ExpRateExt`. Move their importers to `Deriv*` first; these include
  modules in the Continuous domains. If moving an importer turns out to be too large, mark the pack legacy in its
  header and leave it.
- **B and D:**
  - Rebase the Σ machinery of `SgLinAlg` and `ExpFamAlg` on stdlib (`Data.Vec.Functional`,
    `Algebra.Properties.CommutativeMonoid.Sum`).
  - Prove the universal property of `Signed` once, and use it for E-linearity.
  - Factor out the "constant is finite" boilerplate (`Cp`, `Cx`, `Fin-half`).
- **E:**
  - Merge `GaussTail` into `GaussExp`, and `ExpRateSigned` into `AffineAlg`.
  - Consolidate `SF` and `Bdd`.
  - Rename `GeometricNorm`, `GeometricMoment2` and `SignedOmega`.

### 6. continuous-core

- **A:** Add `Interface.md` and `Guide.md` entries for the s-finite monad, strength and commutativity, `Product`,
  `FinProd`, `Independence`, `IID`, `Exchangeable` and `CoinCoordsJoint`.
- **B:**
  - Use stdlib lemmas for the near-copies `fst-law`/`snd-law`/`marg₁`, `tl`/`tlμ`/`tlp`, and `rw-alg`/`sc-alg`.
  - Unify `SFiniteNorm` and `SFiniteDecomp`.
  - Reduce the global-element/pre-measure lemma pairs in `SFiniteStatBridge`.
- **D:**
  - Share the weight-independent part of `Monad.JoinWit` and `SFiniteMonad.JoinWit`.
  - Write a generic double-strength module over any `CommutativeMonad`, using agent 2's strength lemmas, and
    instantiate it at both monads.
- **Readability:** convert the `trans`/`sym` chains in `Monad.TM` and `Strong` to `begin … ∎`. Move `Strong`'s plumbing
  below the commutativity theorem.
- **E:** Merge `IndepAlg` and `IndepRing`. Consider moving the `Digit*`, `FirstBit*`, `FairCoin`, `CoinIndep`,
  `NatCancel` and `ExtNatModel` modules out of the core.

### 7. continuous-lebesgue

- **A:**
  - Add `Interface.md` entries for Fatou, `dct`, `mct-conv`, `uniqWQ`/`uniqRQ`, `leb-Iv`, `cov`/`covF`, `ftc-dy` and
    shift/scale invariance.
  - Replace the "plan 03/05" headers.
  - Say plainly that change of variables covers only increasing bijections of [0,∞].
- **D:**
  - Prove "ν is Lebesgue measure" once, with the `χInf`-null clause in `leb-unique`. Derive the scale, shift,
    real-line shift and change-of-variables modules from it.
  - Present `push-eq` as the headline change of variables.
  - Derive `mct-conv` and `dct` from `fatou`/`rev-fatou`.
- **B and E:**
  - Inline `ConvEps` if `DominatedSigned` is its only user.
  - Merge `FatouAux` into `Fatou`.
  - Merge `LebesgueDyadicNat` into `LebesgueDyadicAlg`, `LebesgueShiftCut` into `LebesgueShiftAlg`, and `TopMulPos`
    into `InfAlg`.
  - Move the pure ℕ/ℚ lemmas down to `RationalLemmas` and its neighbours.
  - Halve the left/right duplication in `UniquenessRQ`.
  - Rename `UniquenessR`, `RQArith` and `NullInf`.

### 8. continuous-distributions

- **A:** Add a "distribution recipe" entry to `Interface.md`: a density times a base measure, then normalisation, then
  moments.
- **C:** Keep one proof that ∫xⁿe⁻ˣ = n!, the `DerivMoment`/`DerivBridge` route, and retire the self-similarity routes:
  `HalfLineMean`, `HalfLineMoment2`, `HalfLineMomentN`/`Fact`, and `ExpRateMoment` once it is ported to `Deriv`.
  Derive `UniformMean` and `UniformMoment` from `UniformMomentN`. Merge the two tail-FTC glues
  (`TailFTCLipHalf.glue` and `DerivBridge.glue-D`).
- **D:**
  - Make a generic `withDensity` recipe, and define `expDist` as `densDist negExpH`.
  - State the location–scale (affine pushforward) law once. Derive Exp(λ) from rate 1, and N(μ, σ²) from N(0, 1).
  - Use agent 7's Lebesgue uniqueness where it applies.
  - Write the header so that agents 9 and 10 can adopt the result.

### 9. continuous-signed-info

- **A:**
  - Add `Interface.md` and `Guide.md` entries for exponential families, random vectors and sample estimators.
  - In `SignedExpect`'s header, say that signed integration is the Jordan-decomposition integral.
  - Rename `SignedTests` to remove its clash with `SignedTest`.
- **B:**
  - Fold `FinTest` into `SignedTest`.
  - Add a bundled `FinTs` for `∀ j → FinT (T j)`, and a shared `L²` alias.
  - Derive `SignedSq` from `SignedMul`.
- **D:** Express reweighting and exponential tilting (`reweightPre`, `ProdReweight`, `ExpFamilyPostAux`,
  `Entropy.densPre`) through agent 8's `withDensity`.
- **E:** Merge the roughly 20 `*Alg`/`*Aux` helpers where their timings allow, starting with the
  `via-cross`/`via-sums` transport repeated in `SgSample`, `SignedVar` and `RandomVector`.

### 10. inference

- **A:**
  - Add a read-first table to `Interface.md`.
  - Rewrite the "plan NN item MM" headers so that the theorem comes first.
  - Split the flat directory into `Bayes`, `Frequentist`, `Expectation` and `Distributions` (this is part of tier E).
- **B:**
  - Write an `Inference.Prelude lem₁` for the repeated `open` preamble.
  - Fold the single-parent helpers: `WeakLawAlg`/`Cheb`, `CondIIDConst`/`CoinStep`, `GaussVectorAlg`, and
    `ExpDistMean`/`Var`/`ExpRateOne`.
  - Merge `PolyDomination` with `PolyDominationOdd`.
- **D:**
  - State Bayes' rule once at the abstract layer, as a reweight/normalise/sequential-update package. First check
    whether `IsStatisticalQBSLike` already exposes reweighting.
  - Instantiate it for `Example.Bayes`, `CoinPosterior`, `Inference.ExpFamily` and `Continuous.ExpFamilyPost`.
  - Use agent 2's bind vocabulary, and agent 8's location–scale law for the Gaussian and exponential families.

### 11. reader-guide

This agent does documentation only and edits no Agda.

- **Reader's map.** Join the per-domain roadmap entries into one reader's map at the top of `Guide.md`. Give the
  layers, the headline theorem of each layer, and where it lives.
- **Interface.md.** Check that it reads in layer order.
- **Links.** Check that the README links to the map.
- **Leftovers.** Check that no module header still refers to "plan N" without saying what the plan covers.
- **SUMMARY.md.** Update its status.

## Launch template (for the orchestrator)

Run each agent with `model: sonnet`, `effort: low`, `isolation: worktree`, in the foreground or the background, and
one at a time. Use this prompt:

> You are implementing the audit recommendations for the `<domain>` domain of the Agda library at
> /Users/cspollard/Programming/qbs (quasi-Borel spaces and probability). You are in your own git worktree. Read
> `audit/IMPLEMENT.md` and follow its "Common brief" exactly, together with the section for agent `<n>. <domain>`.
> Your domain's audit report is `audit/<domain>.md`. Work tier by tier (A to E), commit on your branch after each
> tier, and stop at a tier boundary if you are running short of budget. Do not push or merge. End with the report
> described under "Recording and reporting".

After each agent, the orchestrator does the following before starting the next:

1. Read the agent's report. Its final verification pass, `make doccheck` and `make longcheck` are the agent's job. The
   orchestrator does not re-run them; it sends the agent back if any of them is missing or failed.
2. Merge into `main`. Push only with the maintainer's approval.
3. Delete the worktree and its branch.
