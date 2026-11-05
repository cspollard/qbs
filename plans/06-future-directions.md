# Plan 06: future directions (collected 2026-11-05; possibilities, not commitments)

Directions suggested by an outside review of the library, recorded with what already exists, what is already
planned, and a plausible first step.  None is scheduled.  Item numbers, when these become plans, continue after
plan 05 (last: 55).

## 1. Consistency and the bias–variance decomposition

**Gap.** The estimator layer proves unbiasedness (`Analysis/Estimator`, `Inference/Frequentist`, and for unbounded
signed tests `Continuous/SgSample`), but nothing about behaviour as n grows.  `Frequentist` defines `bias`,
`variance` and `mse` but never relates them.

**Already planned (plan 05).** Item 50 `Inference/WeakLaw`: Markov, Chebyshev, the weak law in the rate form
n ε² P{|Sₙ − nμ| ≥ nε} ≤ σ², stated for any family satisfying `SgMoments.Moments` (so for every iid family through
`IID.IID-moments`).  Var Sₙ ≃ n σ² is `SgSample.Var-sum`.

**Still open.**
- Bias–variance decomposition: mse τ t ≃ variance t + (bias τ t)², an identity in the signed ring
  (`Frequentist.meanSq` at τ θ versus at E t; the cross term vanishes because E[t − E t] ≃ 0).  Cheap: one lemma
  in `Frequentist` or a small companion module, plus its unbounded counterpart over `SignedVar` (`Ex-cen` already
  computes E[(f − c)²]).
- MSE of the sample mean, division-free: E[(Sₙ − nμ)²] ≃ n σ², i.e. MSE(Sₙ/n) = σ²/n (follows from `Var-sum`).
- Consistency as a statement: "for every ε > 0 and δ > 0 there is N with P{|Sₙ/n − μ| ≥ ε} ≤ δ for n ≥ N",
  derived from `weak-law-rate` (needs an Archimedean step on the lower reals: σ²/(n ε²) → 0, i.e. for finite σ²
  and positive ε some n has n ε² δ ≥ σ²).  Then consistency of the sample variance, which needs fourth moments
  (Var of Fᵢ²) or a separate argument; state it under a finite fourth-moment hypothesis.
- Possible home: `Inference/Consistency` (needs 50) and a `Frequentist` lemma for the decomposition.

## 2. A higher-order showcase

**Gap.** The worked examples are first-order (coins, uniform, Gaussian, exponential); plain measure theory on ℝ
covers them.  QBS earns its keep when function spaces carry probability.

**What exists.** `Exponential` gives `Y^X` and `CartesianClosed (QBSCat S)`; `Probability` has Kock's strength and
double strength; the continuous monad and s-finite measures act on any QBS.  Plan 05 item 49 (`Exchangeable`) plans
the easy half of de Finetti (a mixture of iid laws is exchangeable); the hard half is listed out of scope there.

**Possible steps, smallest first.**
- Random functions: a measure on `Y^X` built from a sampler, e.g. a random affine or step function
  x ↦ A x + B from independent coefficients, with the pushforward of evaluation at a point (the law of f(x)) and
  E[f(x) f(y)] (a covariance kernel), using the exponential's evaluation map and `Independence`.
- Kernels as values: a prior over kernels Θ ⇒ T X as a measure on (T X)^Θ, and Bayesian updating of it.
- de Finetti in the QBS form of Heunen–Kammar–Staton–Yang (2017): an exchangeable sequence on a standard Borel
  space is a mixture of iid laws, with the mixing measure on T X.  Large: needs the infinite product measure on
  `X^ℕ` (Kolmogorov extension, or the Cantor-space construction: the coin coordinates of plan 05 item 47 already
  give countably many independent uniforms) and a tail / empirical-measure argument.
- A nonparametric prior: a Dirichlet-process-style stick-breaking construction (countably many Beta and base
  draws from the coin coordinates) as a measure on T X, with its mean measure.  Needs Beta laws and the infinite
  product.
- Random sets 2^ℝ as in the original QBS paper; least connected to the current statistics.

## 3. A computable fragment

**Gap.** `lem₁` blocks evaluation, and a measurable probe can depend on infinitely many bits, so nothing runs.

**What exists.** `docs/Classical.md` §4–6 lists which classical uses are inherent and which are presentation
artifacts; its priorities (indicators as lower reals without decisions, resizing and uip behind named assumptions,
partial normalisation) are prerequisites.  Function extensionality is already removed (plan 04).

**Possible steps.**
- A subcategory of QBS whose probes are continuous on Cantor space (each output bit, or each rational
  approximation, decided by a finite prefix), closed under products, pushforward along continuous maps and bind.
- Constructive values: dyadic or rational interval approximations of [0, 1] and of [0, ∞] in place of lower cuts.
- The uniform sampler (`expansion`) and samplers built from it by pushforward and bind are then executable; a
  bridge theorem: the first n bits determine the output to within 2⁻ⁿ (for the uniform; a modulus of continuity in
  general), and the semantics of the fragment agrees with the classical semantics on its image.
- Normalisation, posteriors and integrals stay classical; the fragment covers sampling only.

## 4. Correctness of inference algorithms

**Gap.** Posteriors exist (`Inference/CoinPosterior.bayes`: reweight by the likelihood and normalise,
`SFiniteNorm`), but no algorithm is shown to target them.

**Possible steps.**
- Rejection sampling: for a likelihood ℓ ≤ M, propose θ ~ prior and accept with probability ℓ(θ)/M (a second coin
  draw); the law of the accepted draw (the first acceptance, a geometric loop, or the conditional law given one
  acceptance) is the posterior.  The one-step version is a reweighting identity; the loop needs a countable sum
  over the number of rejections (the coin coordinates of plan 05 item 47 provide the independent rounds).
- Importance sampling: E_posterior[f] ≃ E_prior[ℓ f] / E_prior[ℓ] (already essentially `bayes`); the
  self-normalised estimator Σ ℓ(θᵢ) f(θᵢ) / Σ ℓ(θᵢ) with θᵢ iid from the prior: unbiasedness of numerator and
  denominator from `SgSample`, and consistency of the ratio from direction 1.
- Metropolis–Hastings (Ścibior et al. 2018): the kernel preserves the posterior (detailed balance as an equality
  of measures on Θ × Θ, via `Product` and `ψ`).  Larger; convergence is out of reach without ergodic theory.
- These statements are about the semantics and do not need direction 3; direction 3 would make the algorithms
  runnable.

## Dependencies

1 needs plan 05 item 50.  2 needs plan 05 items 46–49 (the infinite product for de Finetti and stick-breaking).
4 needs plan 05 items 46–47 (independent rounds) and, for the self-normalised estimator, direction 1.  3 is
independent of plan 05 and starts from the `Classical.md` priorities.
