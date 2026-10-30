# Architecture

How the layers depend on each other, where the hypotheses come in, and what is slow to compile.
One line per module: [Modules.md](Modules.md) (generated). The public names: [Interface.md](Interface.md).

## Layers (arrows: "imports")

```
 Example/          programs, Bayes, conditioning (discrete); Probability (real weights)
    │
    ├────────────────────────────────┐
    ▼                                ▼
 Model/  (discrete, R = ℕ)      Continuous/  (R = Cantor space)
    │   Measures A K, Pre, ∫         │   Monad, Strong, SubProb, SFinite*, Uniform*, FairCoin
    │   StatInstance (discreteStat)  │   continuousStat = SFiniteStat
    │                                ▼
    │                            Analysis/  Daniell integral, Riesz, unbounded J, Tonelli/Fubini, Series, Meas
    │                                ▼
    │                            Borel/    σ-algebra on 2^ℕ, π–λ, merge/lead, Borel.Source (cantorSource)
    ▼                                │
 Abstract: Core, Category, Limits, Colimits, Complete, Exponential, Probes,
           Probability, Statistical, IsQBSLike, IsStatisticalQBSLike, Instance
```

- **Abstract layer.** `QBSCat S` for a `RandomSource S` is complete, cocomplete and cartesian closed
  (no hypotheses). `ProbabilityInterface` and `StatisticalInterface` describe the measure monads abstractly;
  `Instance` packages them as `IsQBSLike` / `IsStatisticalQBSLike`.
- **Discrete model.** Measures are weighted countable families over a complete semiring. Everything is generic in
  the semiring; the Boolean, Viterbi and additive `[0,∞]` semirings are instances (README also lists `ℕ∞`; its `OmegaSemiring` is `Analysis.ExtNat`).
- **Continuous model.** A measure is a probe `R → X` plus a Daniell functional on Cantor space. Built bottom-up:
  `Borel` (σ-algebra) → `Analysis` (premeasure on clopen sets, extension to Borel sets, integral, Riesz) → `Continuous`
  (monad, strength, commutativity by Fubini, uniform distribution, s-finite monad).
- **Examples.** `Example/*` use only the discrete model, plus the generic `Bayes`.

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

## Hypotheses

The code is `--safe --without-K` with no postulates. Non-constructive principles are module parameters:
`lem : (P : Set) → P ⊎ ¬P`, `lem₁` (at `Set₁`), `funext`. The `hyp` column of [Modules.md](Modules.md) says which
modules mention them directly. The abstract layer and `Example.Bayes` mention none. [Classical.md](Classical.md) says
why each is needed and which are inherent. Constructive alternatives: [ConstructiveLit.md](ConstructiveLit.md).

## What rebuilds when you change X

Agda rebuilds the importers of a changed module. Even a comment-only edit changed the checked file and triggered a
long re-check of dependents here (observed when adding header comments to `Core`), so batch comment edits. In rough order of blast radius:
`Core` (everything) > `Probability`/`Statistical` (all models) > `Analysis.LowerReals` and `Omega` (the whole
continuous stack) > `Continuous.SFinite` (s-finite files) > leaf `Example/*`, `Continuous.Uniform*`.

## Compile time

A from-scratch `make check` takes about 6–10 minutes (README, "Checking"); a cold Riesz-sized module once took 70 minutes before the cause was fixed. The known hot spots and their causes
(from `TODO.md` and the README): unfolded lower cuts (state algebra generically and bridge at the end), `with` on large
goals, passing implicit arguments that Agda could infer, `J`/`mapM`/`joinPre` not being `abstract`.
Tools: `make progress` (tolerates holes), `make profile`, `make profile-MODULE`.
Plan the generic-then-instantiate pattern for new statistical results.

## Where to add things

| New… | Put it in | Pattern to copy |
|---|---|---|
| distribution on `[0,1]` | `Continuous/` | `Uniform.agda` (a `Pre` from a probe and a measure) + `UniformMean.agda` |
| expectation/variance lemma, generic | `Analysis/` or a new `Inference/` layer | `Example/Probability.agda` (`Calculation`: generic, instantiate last) |
| discrete example | `Example/` | `Example/Bayes.agda` |
| model-level theorem | abstract layer, over `StatisticalInterface` | `StatisticalLemmas.agda` |
