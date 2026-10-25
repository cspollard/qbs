# TODO: qbs

Open work for the library (see `README.md` for what exists). Library layout: `qbs.agda-lib`, sources in `src/QBS/`, `Makefile`.

Open items are ordered easiest first; finished items are at the end. Skeleton modules (with holes) live at their final paths; `make progress` accepts them, strict `Makefile` does not (there is none at present).

- [~] CI for `qbs`: `make` typechecks every module (Agda 2.7.0.1, stdlib v2.3, agda-categories c2e7c13e; fails on output, postulates, holes) and `.github/workflows/qbs.yml` runs it (manual trigger; the workflow has NOT been run yet: verify it, then switch the trigger to push/pull_request on `qbs/**`).
- [ ] s-finite measure monad for the continuous model (`StatisticalInterface` over `QBSCat cantorSource`). Hardest. Done so far: unbounded integration (`Analysis/Unbounded`: `FunInf`, `Iinf`, `Iinf-bounded/mono/add/sup/scale`), threshold measurability (`Analysis/Meas`, `Analysis/MeasFun`: `Fun` = bounded `Meas`), the integral API `Analysis/Lebesgue` (`J`), Tonelli for `bind` (`Analysis/Tonelli`: `Meas-J`, `J-bind`). Design decided: a measure on `X` is `[α, m, w]` (probe, probability measure, `Meas` density), i.e. a probability measure on `X × W` with weighted integral `J m (w · f∘α)`; the monad reuses `Continuous/Monad` for the measure part and needs unbounded Fubini (termwise from the bounded `fubini`), the weight object `W` with `Meas` as its randomness, `scaled-laws` (needs inverses of finite positive masses, classical), and `sumM` (countable mixtures on `ℕ × R ≅ R`). Done since: `Analysis/JParam`, `JFubini`, `MixtureN`, `Continuous/Weights`, `SFinite`, `SFiniteMonad` (monad `TM`), `SFiniteStrong`. Remaining (old list, partly superseded): (1) measures of unbounded mass (`Measure` is sub-probability: `I-sub`; generalise to an `s-finite` class, e.g. countable sums of sub-probability measures via `Analysis/Series`); (2) closure of `FunInf` under `+`, scaling by `A`-valued constants, products and precomposition with measurable maps (so that `ν ↦ ∫ν f` is `FunInf` and `join` on `M (M X)` is defined); (3) `join` with its monad laws; (4) normalisation. Literature (Staton 2017; Hirata–Minamide–Sato ITP 2023; Affeldt–Cohen–Saito CPP 2023) gets these from a host measure-theory library.

- [ ] (future) Constructive foundations: `lem` enters only through `Classical` in `Analysis/LowerReals` (`near-sup`, hence `complement`, `cancel`, `Arch.cancel≤`, `way-below`); everything else is generic in `OmegaSemiring`. Removing it needs located reals (Cauchy/Dedekind) and a `Fun` without the `complF` constructor, which touches `Fun-scale`, `Mask` and the Riesz pipeline.
- [ ] (future) Negative reals: a signed layer on `[0,∞]` (differences of finite values; `E[X] = ∫X⁺ − ∫X⁻`, variance) or genuine Dedekind reals from ℚ (about 1.5–3k lines); measures keep `[0,∞]` values. Real-valued random variables need only threshold sets `{x | q < h x}` Borel, as in `Analysis/Threshold`.
- [x] Unbounded integration: DONE (`Analysis/Unbounded`, `Analysis/Min`, `Analysis/LowerRealsMin`, `Analysis/UnboundedLowerReals`; dyadic truncation `tr k a = 2⁻ᵏ·min(a,2ᵏ)`, `FunInf h` = all truncations are `Fun`, so `Iinf` is representation-independent; the five skeleton goals `Iinf`, `Iinf-bounded`, `Iinf-mono`, `Iinf-add`, `Iinf-sup`). The skeleton's inductive `FunInf` was replaced by this predicate, which avoids proving independence of the chosen supremum representation.
- [x] Uniform CDF: DONE (`Continuous/UniformCDF.agda`: `cdfTest`, `cdf : ∫ uniformSub (cdfTest t) ≈ t` for `t ≤ 1`). Route (decided, documented in the README): first-bit decomposition of the fair coin (`Analysis/Mixture`, `Continuous/FirstBit`), expansion self-similarity, and the abstract `Analysis/SelfSimilar` lemma; this replaced the dyadic-induction plan because it needs no dyadic numerals, no null set `{000…}` and no strictness facts. Not done: higher moments.
- [x] Riesz (probability case): DONE (`Analysis/Riesz.agda`: `setFun`, `functional-setFun`, `setFun-functional`; `Functional.functional-prob`). Not done: sub-probability measures (needs `μ-⊤ ≤ 1` in `BorelMeasure` and the pipeline's uses of `μ-⊤ ≈ 1` generalised to `mass`: `CoinSimple.∫-sconst`, `Ind`, `L-one`). Decision: the `lem` alias of `DaniellB` was removed (see README, performance note) because mixed spellings made `Riesz.agda` take 70 minutes.
- [x] Bayes' rule, discrete: DONE (`Example/Bayes.agda`: `posteriorU`, `evidence`, `bayes-numerator`, `posterior` (normalised by an inverse `n` of the evidence), `bayes : ∫ posterior f ≈ n · ∫ prior (w·f)`; generic in a `NormalizableSemiring`).
- [x] `Example/Probability.agda`: DONE (`Calculation`: `both-true : ∫ both (test isTrue) ≈ half * half`, `both-mass`, generic in a complete semiring with `half + half ≈ 1`; `Additive lem₁` instantiates it at the additive `[0,∞]`). Decision: the algebra is generic because at the concrete semiring Agda unfolds the lower cuts and fails to solve constraints.
- [x] Hard conditioning, continuous (measure level): DONE (`Analysis/Restrict.agda`: `Fun-χ·`, `restrictM`, `mass-restrict`, `restrict-split`). Not done: packaging `restrictM` as a morphism/`Pre` of the continuous monad (like `scoreH`).
- [x] Hard conditioning, discrete: DONE (`Example/HardConditioning.agda`: `condition` keeps the runs where a Boolean observation holds, `∫-condition`, `condition-split` = total expectation; the rejected mass becomes the defect).
- [x] Sub-probability monad for the continuous model: DONE (`Measure` is now sub-probability with `IsProb`; `MeasureClass` parametrises `Continuous/Monad`, `Strong`; `Continuous/SubProb.agda`: `ContinuousSub`, `scoreH`, `failPre`; `SubModel.agda`: `softUniform`). Not done: normalisation / the statistical interface for it (needs unbounded integration, see the s-finite item); hard rejection via Borel guards; `E[u] = ½` and the mass of `softUniform` are proved (`Continuous/UniformMean.agda`, `SubModel.agda`); CDF and higher moments are not.
- [x] Fair-coin measure on Cantor space as a `Measure` on all `Fun h`: DONE (`Continuous/FairCoin.agda`: `fairCoin`, `fairCoin-cyl`; pipeline documented in the README section "The fair-coin measure"; parameter `lem₁` only). Corollary (a) evens/odds independence DONE (`Analysis/Interleave.agda`, `Continuous/CoinIndep.agda`: `fairCoin-indep`). Remaining: (b) DONE: the uniform distribution on `𝕀` (`Analysis/BinaryExpansion.agda`, `Continuous/Uniform.agda`: `uniform`; mean ½ in `Continuous/UniformMean.agda`; CDF: skeleton `Continuous/UniformCDF.agda`); (c) Lemma hygiene: `Analysis/CoinIntegral.agda` avoids `with` on large goals (it made Agda take > 10 minutes); keep helper lemmas small with explicit implicit arguments.
- [x] Additive real-valued normalisable semiring (`[0,∞]`, `+`, `×`) for the discrete model: DONE (`Analysis/CutSum.agda`, `Model/AdditiveSemiring.agda`, `Model/AdditiveModel.agda`). `Example/Program.agda` is now level-polymorphic (`Flip` takes the outcome type), preparing a numeric example. Remaining: `Example/Probability.agda` instantiating `Programs` at `additiveComplete` with `B = Lift ℓ₁ Bool` and `half`/`hh` from `lowerRealsArch` (`both-true : ∫ both (test isTrue) ≈ half * half`, `both-mass : ∫ both (test (λ _ → 1#)) ≈ 1#`); a draft is in the session scratchpad `…/scratchpad/Probability.agda.draft`, and its only failure is two unsolved metas at the `+-cong` steps after `∫-both` (give those steps explicit intermediate terms or implicit arguments).
- [x] `bind` linear in the kernel argument: DONE (`sumK`, `sumK-point`, `bind-sumK` in `StatisticalInterface`; proved in `Model/StatInstance.agda`, hence also for the Boolean and Viterbi models). A continuous statistical instance would need them too.

## Compile time: audit, profiling and improvement strategy

Cold build is ~17 minutes (measured below; single modules used to take 10–70 minutes before the fixes in the README "Performance note" and the `Meas`/`J` pitfalls). This section records what the Agda
literature and this repository suggest is responsible, and a plan to confirm it with measurements before
changing anything.

### Expectation (hypotheses, ranked; none measured yet)

Agda's documentation (`tools/performance`) gives only the profiling tools (`--profile=modules|definitions|internal`,
`+RTS -s`, interactive highlighting) and no list of causes; the rest is from the Agda mailing list and issues
(e.g. #5801 on the syntactic-equality shortcut, which is applied recursively and so can make unification of two
large, nearly identical terms very slow; advice to split large modules; GC tuning with `-s`/`-A`). Combined with the
repo history:

1. **Conversion of large terms that differ only in spelling** (most likely dominant). Records such as
   `OmegaSemiring`, `Measure`, `QBS` are huge dependent records; when two spellings of one argument are compared
   (`DaniellB.lem lem₁ B` vs `lemOf lem₁`) Agda eta-expands and compares field by field (70 min → 4 s in `Riesz.agda`).
   Same mechanism: `Functor.F₀ TF (Functor.F₀ TF X)` vs `TQ (TQ X)`; `J`, `mapM`, `joinPre` needing `abstract`.
   Suspects now: any module that opens a parameterised module (`module Foo (lem : …)`, `Param A lem`, `Unbounded A
   Arch Min`) at several different argument spellings; `Continuous/SFinite*`, `Tonelli`, `JFubini`, `Series`, `CutSum`.
2. **Unfolding of concrete `LowerReals` cuts.** The notes say Agda "unfolds the lower cuts and fails to solve
   constraints" at the concrete semiring; generic-in-`OmegaSemiring` modules avoid it. Expect time in
   `Typing.CheckRHS`/`Conversion` for modules instantiating `LowerRealsOmega lem` (`Lebesgue`, `Unbounded*`, `Meas*`).
3. **Unsolved-metas / implicit-argument inference through deep module parameters.** Every module re-takes `lem`
   (≈25 modules have `(lem : ∀ P → P ⊎ (P → ⊥))` as a parameter) and each use re-applies it to every exported
   name, so terms carry long argument spines; `open M lem using (…)` per module repeats this.
4. **`with` on large goals** (the abstraction `with` generalises over all occurrences in a big goal; `CoinIntegral`
   once took > 10 min). Heaviest remaining users by count: `CutSum` (31), `Series` (20), `Clopen` (19), `Regular` (18), `Pieces` (15).
5. **Instance/interface overhead and import fan-out.** 117 modules, ≈1800 imports, 16k lines; each `agda FILE`
   in `check.sh`-style loops reloads the stdlib/agda-categories interfaces (seconds each). agda-categories imports
   (`Categories.Functor`, `Category.Core`, monads) are heavy and pulled in by ≈20 modules.
6. **Deserialisation/GC.** Large interfaces for modules with big normalised types; default GHC heap settings may
   make GC a visible fraction (to check with `+RTS -s`).

### Baseline (measured 2026-10-25, Agda 2.7.0.1, cold `_build`, `make profile-tree`)

Whole library: 117 modules, 998 s summed (~17 min cold); one module exceeds the 120 s limit
(`Continuous.SFiniteCommute`, killed, depth 13). Cost is concentrated: the 10 slowest modules are
`SFiniteCommute` (>120 s), `SFiniteMonad` 112 s, `SFiniteStrong` 104 s, `JParam` 76 s, `JSum` 57 s,
`Continuous.ProbInstance` 57 s, `Model.StatInstance` 53 s, `Lebesgue` 53 s, `Tonelli` 52 s, `Model.ProbInstance` 40 s;
every other module is under 25 s and most under 5 s. Hence the "hours" were mostly earlier pathologies that the
README's fixes removed; what remains is a few heavy definitions. `--profile=definitions` on the lowest slow modules:

| module (depth) | total | dominant definition |
|---|---|---|
| `Analysis.LowerInverse` (2) | 24 s | `InvClassical._._.q≤rs` 13.7 s |
| `Model.ProbInstance` (5) | 37 s | `discreteProb` 34.3 s (everything else < 25 ms) |
| `Model.StatInstance` (6) | 48 s | `discreteStat` 42.9 s |
| `Analysis.Lebesgue` (7) | 51 s | `J-add` 17.5 s, `J-scale` 11.9 s, `J-cong` 6.5 s, `J-irrel` 5.8 s |

So the profile supports "a handful of single definitions" (instance records `discreteProb`/`discreteStat` built from many
fields at once, i.e. hypothesis 1/3: large record conversion and long argument spines) over "flat/with/import cost" (4, 5, 6).
Not yet done: definition-level profiles above depth 7, and `SFiniteCommute` (never finishes in 120 s).

### Measurement plan (leaf-first)

1. `make profile-tree` (`scripts/profile-tree.py`): check every module individually, leaves of the import graph
   first, 120 s limit each; a module over the limit is killed and its dependents skipped. Output: `profile/tree.tsv`
   (module, depth, status, seconds) and per-module `--profile=modules` + `+RTS -s` files. Resumable.
2. Work the SLOW/expensive modules lowest-depth first, since improving a low module also speeds everything above it
   and keeps the tree checkable. For each: `make profile-QBS.<Module>` (modes `modules`, `definitions`, `internal`; Agda 2.7
   allows one per run), find the dominant definitions, then confirm per definition: replace the body by `?` (time
   collapses ⇒ RHS elaboration), `-v tc.conv:20 -v tc.constr:20` for what is being compared, `-v tc.with:40` for `with`.
3. After each improvement re-run `make profile-tree` (resumable: delete that module's row from `tree.tsv` and its
   dependents') and update the table above. Where a profile disagrees with the hypotheses, reorder them.
4. Raw `profile/` output is not committed (see `.gitignore`); commit only `profile/summary.md` with the table.

Next targets in order: `LowerInverse.q≤rs`, `Model.ProbInstance.discreteProb`, `Model.StatInstance.discreteStat`
(likely the same remedy: build the instance field by field from small `abstract`/named pieces, explicit implicit
arguments, one spelling of `lem`), then `Lebesgue.J-add/J-scale`, then the s-finite stack (`JParam`, `JSum`, `Tonelli`,
`SFinite*`).

### Improvement experiments (one at a time, each re-profiled; keep a change only if the module gets ≥ 20 % faster
and the full build does not regress)

- **Normalise spellings** (hypothesis 1): one canonical name per parameterised-module argument
  (`private lem = lemOf lem₁`-style aliases, a single `open M lem public` re-export module per layer); make
  data-like records `no-eta-equality` and defined by copatterns where only identity of arguments matters; make
  proof-only witnesses and expensive definitions `abstract` (keep `*-def` unfolding lemmas), as done for `J`.
- **Avoid unfolding** (2): keep modules generic in `OmegaSemiring` and instantiate only at the leaves; add
  `{-# OPTIONS --lossy-unification #-}` only after profiling (it speeds up higher-order unification at the cost of
  completeness; test it per module with `{-# OPTIONS #-}` pragma, not globally).
- **Shrink parameter lists** (3): bundle `lem` and the semiring structure into one record parameter / `module _ {{…}}`
  instance-free record passed once, so argument spines stay short.
- **Replace `with`** (4) in the top offenders by helper lemmas with explicit implicit arguments or `rewrite` on small
  types; the README's "keep helper lemmas small with explicit implicit arguments" rule applies.
- **Split large modules** at natural seams (the biggest: `StatInstance` 513, `CutSum` 457, `Series` 455, `CoinIntegral`
  439, `Unbounded` 423, `LowerReals` 423); verify with the profile that the split reduces the max per-module time
  and that `Serialization` time does not grow.
- **Tooling/GC** (5, 6): run Agda with `+RTS -A256M -M…` (add an `AGDA_RTS` variable to the `Makefile`) and measure; check
  `-j` builds with the Makefile (parallel modules, after `make all-interfaces`) and mention the achievable speed-up
  in CI; cache `_build` and the library interfaces in the CI workflow (`actions/cache`) so only changed modules rebuild.
- **Guard regressions.** Add a CI step that runs `make profile-QBS.…` for the five slowest modules and fails if one exceeds
  a recorded budget (initially 2× the baseline); record budgets in `profile/summary.md`.

Success criterion (revised after the baseline): every module under 120 s (`make profile-tree` reports no SLOW),
no single definition above ~10 s, cold build under 10 minutes on the baseline machine.
