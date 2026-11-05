# Quasi-Borel spaces in Agda

A formalisation of quasi-Borel spaces and probability in Agda, following Heunen, Kammar, Staton and Yang,
[*A Convenient Category for Higher-Order Probability Theory*](https://arxiv.org/abs/1701.02547).

A quasi-Borel space (QBS) is a set together with a class of "random elements". Functions between such spaces,
including higher-order functions, stay well behaved, so you can state probability theory for programs that take
programs as arguments. The library builds the category of QBSs, states what a probability monad is, and then
constructs two concrete models of it: a discrete one and a continuous one on Cantor space. On top of these it
proves results about distributions, Bayesian and frequentist inference, and information quantities.

The code is `--safe --without-K` and has no postulates. The classical principles it needs (excluded middle, called
`lem`) are explicit module parameters. [docs/Classical.md](docs/Classical.md) says where and why.

## Install and use

You need Agda 2.7.0.1 and two libraries registered in `~/.agda/libraries`:
`standard-library` (v2.3) and `agda-categories` (commit `c2e7c13e`).

To use qbs from your own project:

1. Add the path of this directory's `qbs.agda-lib` to `~/.agda/libraries`.
2. Add `qbs` to the `depend:` line of your own `.agda-lib`.
3. `import QBS.Example.Program` (or any module listed below) in your code.

The library file is `qbs.agda-lib` (sources in `src/`, modules named `QBS.*`).

## Build and check

| Command | What it does |
|---|---|
| `make check` | Typecheck every module. Strict: no Agda output, no holes, no postulates. Slow on a cold build. |
| `make doccheck` | Check the docs against the code: header comments, the module index, code excerpts, listed names. Needs no Agda. |
| `make longcheck` | Flag declarations that are too long (over 25 lines, 1500 characters or 160 columns). Needs no Agda. |
| `make progress` | Like `check`, but unsolved holes are allowed. For work in progress. |
| `make html` | Build the Agda HTML documentation in `html/`, with `html/index.html` listing every module. |
| `make htmlserve` | `make html`, then serve `html/` on port 8081 (`PORT=...` to change). |
| `make profile`, `make profile-MODULE` | Per-module timings; see the header of the [Makefile](Makefile). |

Agda keeps interfaces in `_build/`, so a second `make check` only rechecks what changed.
Compile times and what is slow: [docs/Architecture.md](docs/Architecture.md), "Compile time".

## The areas

Files live under `src/QBS/`. Roughly, each area builds on those above it in this list.

| Area | Where | What |
|---|---|---|
| Abstract layer | `Core`, `Category`, `Limits`, `Colimits`, `Complete`, `Exponential`, `Probability`, `Statistical`, `IsQBSLike`, `IsStatisticalQBSLike`, `Instance` | `QBSCat S` (QBSs over a random source `S`) is complete, cocomplete and cartesian closed. `ProbabilityInterface` and `StatisticalInterface` say what a probability monad and a soft-conditioning monad are. |
| Discrete model | `Model/` | Random source `ℕ`. Measures are weighted countable families over a complete semiring (Boolean, Viterbi, `ℕ∞`, additive `[0,∞]`). |
| Continuous model | `Borel/`, `Analysis/`, `Continuous/` | Random source Cantor space `2^ℕ`. Measures are Daniell functionals (integrals) on measurable functions. It has the fair coin, the uniform distribution, an s-finite measure monad, and integrals of unbounded `[0,∞]`-valued functions. |
| Signed layer | `Analysis/Signed*`, `Continuous/Signed*` | Signed values and expectations of signed tests, built on the non-negative core. |
| Inference | `Inference/` | Bayesian and frequentist statistics, Gaussian and exponential distributions, estimators, Bayes risk. |
| Information | `Continuous/Entropy`, `KLDiv`, `InfoProduct`, `SignedVar` | Variance, entropy and KL divergence. |
| Examples | `Example/` | Programs in `do`-notation, conditioning, Bayes' rule, copy-and-paste set-ups (`Recipes`). |

[docs/Architecture.md](docs/Architecture.md) draws the dependencies. The library has about 320 modules; the
one-line index is [docs/Modules.md](docs/Modules.md).

## Headline results

Abstract layer:

- `QBSCat S` is complete, cocomplete and cartesian closed, for every random source, with no hypotheses
  (`Limits`, `Colimits`, `Complete`, `Exponential`).
- Both models satisfy the full statistical interface: `Model.Discrete.discreteStatisticalQBSLike` (for any
  normalisable semiring) and `Continuous.SFiniteStat.continuousStat`.

Continuous model:

- The fair-coin measure on Cantor space, and independence of its even and odd bits
  (`Continuous.FairCoin`, `Continuous.CoinIndep.fairCoin-indep`).
- The uniform distribution on `[0,1]` with mean ½, CDF `P(u ≤ t) = t`, second moment and variance
  (`Continuous.Uniform`, `UniformMean`, `UniformCDF`, `UniformVariance`).
- The s-finite measure monad with strength, commutativity and normalisation (`Continuous.SFinite*`), built on an
  integral for unbounded functions with Tonelli and Fubini (`Analysis.Lebesgue`, `Tonelli`, `JFubini`).
- Lebesgue measure is determined by its masses on intervals (`Continuous.LebesgueInterval.leb-unique`);
  uniqueness of measures on the half-line and the real line (`Continuous.UniquenessWQ`, `UniquenessRQ`).
- Product measures and Fubini (`Continuous.Product`); dominated convergence and Fatou's lemma
  (`Continuous.Dominated`, `Fatou`); monotone change of variables (`Continuous.ChangeOfVariables`).

Signed expectations (`Continuous.Signed*`):

- Signed tests, their expectations against any s-finite measure, and linearity (`SignedTest`, `SignedExpect`).
- Values in `(−∞, ∞]` (`SignedInf`), moving expectations along maps (`SignedTransport`), limits and
  differentiation under the integral (`SignedLimits.dct-Ex`, `deriv-Ex`).
- Fubini and independence for signed tests (`SignedFubini.Ex-⊗`); the logarithm as a signed value
  (`SignedLog.log-mul`).

Distributions and inference:

- Exponential distribution with all its moments, `E[Xⁿ] = n!` (`Continuous.ExpDist`, `Inference.ExpMomentN`).
- Gaussian N(μ, s²) on the real line with its mean and variance, with no value for π
  (`Inference.GaussReal`, `GaussScale`, `GaussShift`, `GaussVar`); the half-normal (`Inference.HalfNormal`).
- Sample mean and sample variance are unbiased estimators, for uniform draws and for any sampler
  (`Inference.UniformExperiment`, `Sampler`, `UniformSampler`; generic form in `Inference.Frequentist`).
- Bayes' rule for discrete models, sequential updating, and exchangeability (`Example.Bayes`,
  `Inference.Bayesian.posterior-exchangeable`).
- A coin with a uniform prior: the posterior is a distribution, with the Beta integral for integer parameters
  (`Inference.CoinUniformPrior`, `CoinPosterior`, `Continuous.BetaIntegral`).
- Bayesian and frequentist views on one model, and the Bayes risk of two estimators
  (`Inference.BernoulliCompare`, `CoinBayesRisk`).

Information quantities:

- Variance of a signed test, and the centred variance of N(μ, s²) equals s² (`Continuous.SignedVar`,
  `Inference.GaussVar`).
- Entropy relative to a base measure (`Continuous.Entropy`) and KL divergence with Gibbs' inequality
  `KL-nonneg` (`Continuous.KLDiv`).
- KL divergence and entropy add over independent products: `KL-⊗`, `Ent-⊗` (`Continuous.InfoProduct`).

## Where to start reading

- To see a program run: `src/QBS/Example/Program.agda`, then `Example/Recipes.agda`.
- For the overview of everything: [src/QBS.agda](src/QBS.agda), one section per area in reading order.
- For the abstract statement of probability: `Statistical.agda` and `IsStatisticalQBSLike.agda`.
- For the continuous construction: `Continuous/FairCoin.agda`, then `Continuous/Uniform.agda`.
- For statistics: `Inference/Frequentist.agda` and `Inference/Bayesian.agda`.
- For tasks ("how do I condition on data?"): [docs/Guide.md](docs/Guide.md).

## Documentation

| Read | For |
|---|---|
| [src/QBS.agda](src/QBS.agda) | the library overview: one section per area, importing its main modules |
| [docs/Guide.md](docs/Guide.md) | task-oriented tour: which model to use, write a program, condition, continuous integrals, signed expectations, Gaussians, information quantities |
| [docs/Interface.md](docs/Interface.md) | the public names, by module, with one-line meanings |
| [docs/Architecture.md](docs/Architecture.md) | layers, dependencies, hypotheses, compile time, where to add things |
| [docs/Modules.md](docs/Modules.md) | one line for each module (generated) |
| [docs/History.md](docs/History.md) | how the library was built, layer by layer, with the performance pitfalls found |
| [docs/Classical.md](docs/Classical.md), [docs/ConstructiveLit.md](docs/ConstructiveLit.md) | where `lem` is used; literature for a constructive version |
| [docs/UniquenessLit.md](docs/UniquenessLit.md) | literature for the uniqueness-of-measures results |
| [plans/](plans/) | plans and their logs: documentation, uniform-distribution moments, Bayesian and frequentist inference |
| [TODO.md](TODO.md) | open work |

`make doccheck` keeps these in step with the code (header comments, module index, excerpts, listed names).
