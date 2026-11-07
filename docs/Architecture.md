# Architecture

How the layers depend on each other, where the hypotheses come in, and what is slow to compile.
One line per module: [Modules.md](Modules.md) (generated). The public names: [Interface.md](Interface.md).

## Layers (arrows: "imports")

```
 Inference/  Bayesian, Frequentist, Sampler, Gaussian, exponential, coin examples, Bayes risk
    │        (imports Example.Bayes, Continuous/*, Analysis/*)
    ├───────────────────────────────┐
    ▼                               ▼
 Example/   programs, Bayes,     Continuous/  (R = Cantor space)
    │       conditioning, Recipes   │   Monad, Strong, SubProb, SFinite*, Uniform*, FairCoin, Product,
    │       (Recipes also imports   │   Dominated, Signed* (signed layer), SignedVar, Entropy, KLDiv,
    │       Continuous)             │   InfoProduct, Gauss*, Exp*, Log*
    ▼                               ▼
 Model/  (discrete, R = ℕ)       Analysis/  Daniell integral, Riesz, unbounded J, Tonelli/Fubini,
    │   Measures A K, Pre, ∫        │        Series, Meas, Signed*, Exp, BoundedRing, Estimator
    │   StatInstance                ▼
    │                            Borel/    σ-algebra on 2^ℕ, π–λ, merge/lead, Cells, Borel.Source
    ▼                               ▼
 Abstract: Core, Category, Limits, Colimits, Complete, Exponential, Probes,
           Probability, Statistical, IsQBSLike, IsStatisticalQBSLike, Instance
```

- **Abstract layer.** `QBSCat S` for a `RandomSource S` is complete, cocomplete and cartesian closed
  (no hypotheses). `ProbabilityInterface` and `StatisticalInterface` describe the measure monads abstractly;
  `Instance` packages them as `IsQBSLike` / `IsStatisticalQBSLike`.
- **Discrete model.** Measures are weighted countable families over a complete semiring. Everything is generic in
  the semiring; the Boolean, Viterbi and additive `[0,∞]` semirings are instances (`ℕ∞` is `Analysis.ExtNat`, an
  `OmegaSemiring`).
- **Continuous model.** A measure is a probe `R → X` plus a Daniell functional on Cantor space. Built bottom-up:
  `Borel` (σ-algebra) → `Analysis` (premeasure on clopen sets, extension to Borel sets, integral, Riesz) → `Continuous`
  (monad, strength, commutativity by Fubini, uniform distribution, s-finite monad).
- **Signed layer.** The `[0,∞]` core is kept. Signed values are differences of finite values (`Analysis.Signed`,
  `SignedOmega`); `Continuous/SignedTest` has signed tests, `SignedExpect` expectations against any s-finite measure,
  and `SignedInf` the one-sided type for `(−∞, ∞]`. `SignedTransport`, `SignedLimits`, `SignedFubini` and `SignedLog`
  build on `SignedExpect`. Replacing `[0,∞]` by `[−∞,∞]` throughout was rejected (see plan 03, "Signed layer").
- **Information quantities.** `Continuous/SignedVar` (variance), `Entropy`, `KLDiv` and `InfoProduct` sit on the signed
  layer and the density machinery (`SFiniteReweight`). They state results for a density against a base measure.
- **Inference.** `Inference/` holds generic statements (`Frequentist`, `Bayesian`), the bridge from samplers to the
  continuous model (`Sampler`, `ExpectationResp`), distributions with their moments (`Gauss*`, `Exp*`, `HalfNormal`),
  and worked examples (`CoinBias`, `CoinPosterior`, `BernoulliCompare`, `CoinBayesRisk`).
- **Examples.** `Example/*` use the discrete model plus the generic `Bayes`; `Example.Recipes` also has the continuous
  set-up (`UniformSetup`).

## Dependency of the main results

| Result | Module | Depends on |
|---|---|---|
| fair-coin measure | `Continuous.FairCoin` | `Analysis.CoinIntegral`, `Regular`, `Uniqueness`, `Borel.PiLambda` |
| uniform `U[0,1]`, mean ½, CDF | `Continuous.Uniform`, `UniformMean`, `UniformCDF` | fair coin, `Analysis.BinaryExpansion`, `SelfSimilar` |
| unbounded integral `J` | `Analysis.Lebesgue` | `Analysis.Unbounded`, `Meas`, `MeasFun` |
| Fubini / Tonelli | `Analysis.Tensor`, `Tonelli`, `JFubini` | `Analysis.Param` |
| probability monad (continuous) | `Continuous.Monad`, `Strong`, `ProbInstance` | `Analysis.*`, `Continuous.Sample` |
| s-finite monad `TM`, `continuousStat` | `Continuous.SFinite…SFiniteStat` | `J`, `Tonelli`, `JFubini`, `Series`, `MixtureN` |
| Bayes' rule (discrete) | `Example.Bayes` | `Model.Monad`, `Model.WeightClasses` |
| signed expectation, independence | `Continuous.SignedExpect`, `SignedFubini` | `SignedTest`, `SignedInf`, `Analysis.Signed`, `Continuous.Product`, `IntegrableFinite` |
| dominated convergence, differentiation | `Continuous.Dominated`, `DominatedSigned`, `SignedLimits` | `Fatou`, `SignedExpect` |
| uniqueness of measures (half-line, real line) | `Continuous.UniquenessWQ`, `UniquenessRQ`, `LebesgueInterval` | `Borel.Cells`, `Continuous.DigitCode`, `Analysis.UniquenessWeighted` |
| Gaussian N(μ, s²) and its variance | `Inference.GaussReal`, `GaussShift`, `GaussVar` | `Continuous.RealLine`, `RealShift`, `ChangeOfVariables`, `SignedVar` |
| unbiased sample mean and variance | `Inference.Frequentist`, `Sampler`, `UniformExperiment` | `Analysis.Estimator`, `BoundedRing`, `Continuous.CoinCoords` |
| variance, entropy, KL, Gibbs' inequality | `Continuous.SignedVar`, `Entropy`, `KLDiv` | `SignedExpect`, `SignedLog`, `XLog` |
| additivity of KL and entropy over products | `Continuous.InfoProduct` | `KLDiv`, `Product`, `InfoProductAux` |

## Hypotheses

The code is `--safe --without-K` with no postulates. Non-constructive principles are module parameters:
`lem : (P : Set) → P ⊎ ¬P`, `lem₁` (at `Set₁`). (There is no `funext` anywhere in `src`: points of Cantor space are compared pointwise.) The `hyp` column of [Modules.md](Modules.md) says which
modules mention them directly. The abstract layer and `Example.Bayes` mention none. [Classical.md](Classical.md) says
why each is needed and which are inherent. Constructive alternatives: [ConstructiveLit.md](ConstructiveLit.md).

## What rebuilds when you change X

Agda rebuilds the importers of a changed module. Even a comment-only edit changed the checked file and triggered a
long re-check of dependents here (observed when adding header comments to `Core`), so batch comment edits. In rough order of blast radius:
`Core` (everything) > `Probability`/`Statistical` (all models) > `Analysis.LowerReals` and `Omega` (the whole
continuous stack) > `Continuous.SFinite` (s-finite files) > leaf `Example/*`, `Continuous.Uniform*`.

## Compile time

There is no recent timing of a whole cold `make check`. What is on record:

- The last measured baseline is from 2026-10-25 (`make profile-tree`, see `TODO.md`, "Compile time"): 117 modules,
  about 17 minutes of summed cold time. The library now has about 320 modules, so a cold `make check` takes
  considerably longer; `make -j N` helps, and warm rebuilds only recheck what changed.
- Recent modules are checked one at a time and stay small. The per-module cold times in plan 03 are mostly 3 to
  15 seconds and 0.5 to 1.7 GB, for example `SignedExpect` 8.7 s, `SignedFubini` 10.6 s, `SignedLog` 7.0 s, `Entropy` 7.9 s,
  `KLDiv` 8.3 s, `InfoProduct` 12.3 s, `GaussVar` 11.3 s. The slowest of that batch are `GaussVarAux` (28 s) and
  `GaussVarPt` and `SignedVar` (12 to 13 s). Plan 03 also records `Continuous/Strong` at 21 s after a check-cost pass.
- `SignedVarAlg` went from 82 s to 9.6 s by solving the ring identities over an abstract commutative semiring and
  relating the test operations to the ring terms by `refl` lemmas (plan 03, "check-cost pass").

Causes that came up repeatedly: unfolded lower cuts (state algebra generically over an abstract semiring and bridge at
the end), `with` on large goals or on cut terms (it hung Agda for more than five minutes), implicit arguments that Agda
could have inferred, `J`/`mapM`/`joinPre` not being `abstract`, records inside parameterised modules, and `con`
literals in ring solves. The earlier fixes are told in [History.md](History.md) and `TODO.md`.
Tools: `make progress` (tolerates holes), `make profile`, `make profile-MODULE`.
Plan the generic-then-instantiate pattern for new statistical results.

Keep declarations short: `make longcheck` (`scripts/longdecls.py`) flags any declaration over 18 lines, 1000 characters
or 130 columns (a record literal is measured by its largest field); `scripts/longdecls.baseline` lists the known long ones
and a new one fails the check. Split by naming the pieces: lemmas with signatures stated in the notation of the
interface (see `Laws` in `Model/StatInstance`), one lemma per constructor case of an induction (`Fun-mask`), and a
named lemma for a witness step instead of a long `where` block (`pick` in `Analysis/LowerInverse`). Check the compile time
of the module before and after (`agda --profile=definitions F`, deleting its `.agdai` first).

## Where to add things

| New… | Put it in | Pattern to copy |
|---|---|---|
| distribution on `[0,1]` | `Continuous/` | `Uniform.agda` (a `Pre` from a probe and a measure) + `UniformMean.agda` |
| expectation/variance lemma, generic | `Analysis/` (abstract semiring) or `Continuous/Signed*` | `Continuous/SignedVarRing.agda`, `Example/Probability.agda` (generic, instantiate last) |
| signed quantity (centred moment, log-likelihood) | `Continuous/` on `SignedExpect` | `Continuous/SignedVar.agda` |
| distribution with moments on the real line | `Inference/` | `Inference/GaussShift.agda`, `Inference/ExpMomentN.agda` |
| information quantity | `Continuous/` | `Continuous/KLDiv.agda` (density against a base measure) |
| statistical model or estimator | `Inference/` | `Inference/Frequentist.agda`, `Inference/Sampler.agda` |
| discrete example | `Example/` | `Example/Bayes.agda` |
| model-level theorem | abstract layer, over `StatisticalInterface` | `StatisticalLemmas.agda` |
