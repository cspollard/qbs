# Plan 3: supporting both Bayesian and frequentist inference

## Goal
One library layer in which a statistical model is stated once and both kinds of inference are expressed and proved
about it:
- **Frequentist:** estimators, bias, variance, sampling distributions, (later) confidence intervals and tests.
  Probabilities are over data for a fixed parameter.
- **Bayesian:** priors, posteriors, evidence, predictive distributions, conjugacy. Probabilities are over the
  parameter given fixed data.

## Shared foundation: the statistical model
```
record Model (Θ X : QBS) : Set where
  law : Θ ⇒ M X                       -- parameter ↦ sampling distribution (a Markov kernel)
```
The QBS setting is a good fit: `Θ ⇒ M X` is a morphism, so the kernel is measurable in θ by construction
(exponential objects), with no side conditions to state.
- iid samples: `law^n : Θ ⇒ M (X ^ n)` built from `Tensor` / `bind` (commutativity already proved).
- A statistic is a morphism `T : X ^ n ⇒ S`.
- Both sides use the same integral `∫` and the same signed layer from Plan 2.

## Design decisions (2026-10-30, after a literature check and a look at the code)
Literature: a statistical model is a Markov kernel `Θ → P(X)` (Kleisli map of the Giry monad; Fritz 2020, nLab, Mathlib's kernel
library); priors are states on `Θ`; posteriors are Bayesian inverses, which for QBS rest on disintegration and stay open, so
we define them through an explicit likelihood (score, then normalise).  In our monad a measure is a probe `α` with a probability
measure `m` (`Pre X`), and `law-surjective` says every element arises so: a kernel and "a probability space per parameter with
its observations" are the same thing, the second being what Plan 2 computes with.
Findings in the code that shape the plan:
- `∫` only integrates `[0,1]`-valued tests (`Hom S X AQ`); the signed expectation `E` lives on bounded signed functions on a
  probability space (`Analysis/SignedIntegral`, `BoundedRing`).  Bias, variance and MSE need the signed one.
- There is no QBS of signed reals.  `Sg` consists of *bounded* pairs, so it fails `glue-random` (countably many pieces with
  growing bounds), which is exactly why Plan 2 stayed on one probability space.  Gaussian data needs such a space anyway.
So the frequentist half comes in two layers:
- **Layer 1 (algebraic, buildable now): `Inference/Frequentist`.**  An `Experiment Θ` is, for each parameter, a probability space
  and a sequence of observations in the ring of bounded signed random variables.  A statistic is a ring term in `X₀…X_{n−1}`
  (`Term n`, interpreted in any commutative ring), so sample mean and sample variance are statistics.  `bias`, `variance`, `mse`,
  `Unbiased` are defined with Plan 2's `E` and the ring `boundedRing`; the estimator theorem of `Analysis/Estimator` gives
  `unbiased-mean`, `unbiased-variance` for every experiment whose observations have the right moments; the uniform-interval
  experiment (`θ = (a,c)`, `Yᵢ = a + c·Xᵢ`) is the first instance.
- **Layer 2 (kernel, later): `Inference/Model`.**  `Model Θ X` is `kernel : Hom S Θ (TQ X)`, `lawAt θ : Pre X`, with statistics
  `X ⇒ signed reals` and `E_θ[g] = E_m(g ∘ α)`.  Needs a QBS of signed reals with *locally* bounded elements (boundedness only
  imposed when integrating against a given measure) and the bridge from `Pre X` to `SF m`; both are real design work.  Bridge
  to layer 1: a model with `X` the signed reals gives an experiment by taking the coordinate probes as observations.
The Bayesian half (`Inference/Bayesian`) is independent of both layers until continuous data: it is stated for the discrete
`Example/Bayes` first (prior, joint, evidence, posterior, sequential update, predictive), then `Pre`-based for Beta–Bernoulli.

**Status:** 3a DONE (2026-10-30): `Inference/Frequentist` (all holes filled; ~35 s cold, 4 s warm) and `Inference/UniformExperiment` (the uniform-interval instance with `sample-mean-unbiased`, `sample-variance-unbiased`). Parameters live in `Set₁` because `Sg` does.

**3b DONE (2026-10-30):** `Inference/Bayesian` (discrete, generic in the normalisable semiring): `sequential`, `evidence-sequential`, `predictive-chain`, `evidence-total` (the evidence is a distribution on the data), and the Bernoulli model with `likSeq-counts`, `posterior-seq`, `posterior-exchangeable`; `Inference/CoinBias`, a worked example with numbers (also at the lower reals). Deliberately *not* done here: the side-by-side with the frequentist estimator on the same data. The two halves live in different worlds today (frequentist: the continuous model with signed values `Sg`; Bayesian: the discrete model over a generic semiring), so comparing posterior mean with sample mean, and the Bayes risk of an estimator, needs the layer-2 bridge of 3c (a QBS of signed reals and a kernel `Θ ⇒ M X` in one model). The explicit joint `prior ⊗ likelihood` needs the same kernels; for now the evidence is the marginal of the joint by definition (`evidence p w = ∫ p w`, `evidence-total`).

### 3c in detail (design, 2026-10-30)
Findings from reading the code, which simplify the plan above:
- **The signed-reals QBS needs no boundedness.** `Meas` (threshold measurability of `R₁ → Cut`) has `Meas-ext`, `Meas-const`,
  `Meas-pre`, `Meas-glue`, so `CutQ` (carrier: lower cuts, random elements: `Meas`) is a QBS, exactly as `AQ` is for `Fun`. A
  signed test on `X` is a pair of maps `X ⇒ CutQ` with a common natural bound: boundedness is a property of the test, not of
  the space, so the glue problem that blocked a QBS of bounded signed values never arises.
- **Every model we can actually build is a sampler.** A kernel `Θ ⇒ T X` is, in this library, represented by a *joint* probe: a
  map `Θ × ℛ ⇒ X` (a program with parameter `θ` and coin flips `r`) together with the fair coin (cf. `Monad.sec` and the
  `Wit` structure of `TQ`).  So the expectation of a bounded statistic `g` at `θ` is `E (g ∘ draw θ)` over `fairCoin`, a
  `BSF fairCoin`, and the iid sample is `Xᵢ = g ∘ draw θ ∘ coordᵢ`: Plan 2's coordinates and independence
  (`CoinCoords.E-coord`, `E-indep`, stated for arbitrary bounded signed functions) apply unchanged.  No product measures on
  general `Pre X` and no Fubini beyond what is proved.
- **Hence the bridge is a corollary.** `Frequentist.Moments` of the iid experiment follow from the *single-draw* moments
  `E g = μ`, `E g² = σ² + μ²` alone (`second` by `E-coord`, `uncorr` by `E-indep`).  That is what `UniformSample.moments`
  does for `u`; the new lemma `iid-moments` is its generic form.
- **Not on the critical path:** well-definedness of `E` on the quotient `TQ X` (`p ≈ᵖ q → E-at p g ≃ E-at q g`) needs that
  integrals of `[0,1]`-tests determine integrals of unbounded measurable functions (truncation `min(g, n)` plus monotone
  convergence).  Real work, declared as `E-resp` with a hole; models given as samplers do not need it.
Modules: `Continuous/SignedTests` (`CutQ`, `STest`, `J-bounded`, `pullback` to `BSF`), `Inference/Sampler` (`Sampler`, `draw`,
`single`, `iidExperiment`, `SingleMoments`, `iid-moments`, unbiasedness corollaries, `kernelOf`, `E-at`, `E-resp`),
`Inference/UniformSampler` (validation: the uniform-interval model as a sampler reproduces `UniformExperiment`'s theorems).
Lemmas to prove, in order of difficulty: `CutQ` axioms (direct from `Meas-*`); `J-bounded` (bounded measurable has bounded
integral: monotonicity and `J` of a constant); `iid-moments` (assembly of Plan 2 lemmas); `kernelOf` random (build the `Wit`);
the validation instance (signed arithmetic for `a + c·u`); `E-resp` (hard, optional).

### Revised staging (supersedes the staging below where they differ)
- 3a. `Inference/Frequentist` skeleton (declarations with holes), then definitions, then the generic theorems, then the uniform
  instance (`Inference/UniformExperiment`).  Each module compiles on its own in seconds; keep proofs short.
- 3b. `Inference/Bayesian` over the discrete model: Bernoulli with a finite parameter grid, shared with the frequentist statement
  on the same data (estimator unbiasedness over the grid, posterior mean).
- 3c. Layer 2: signed-reals QBS, bridge, `Model`.  3d: Beta–Bernoulli.  3e: Gaussian.  3f: intervals, tests, MLE, Cramér–Rao.

## Frequentist module (`Inference/Frequentist.agda`)
1. Estimator `θ̂ : X^n ⇒ Θ`, with `bias θ = E_{law θ}[θ̂] − θ` and `variance`, `mse`.
   Unbiased means `∀ θ → bias θ = 0`. The statement is a `∀ θ` over *global elements* `1 ⇒ Θ`, which is how
   QBS expresses "for each parameter value".
2. Plan 2's theorems instantiated as `unbiased-mean`, `unbiased-variance`.
3. Sampling distribution of a statistic: pushforward along `T`. Already available as `fmap`/`law`.
4. Later: likelihood, score function, Fisher information, Cramér–Rao, MLE, confidence sets and tests as
   measurable subsets with coverage `∀ θ → P_θ(θ ∈ C(X)) ≥ 1 − α`.
5. Each item beyond 2 needs real analysis (derivatives, `log`) that is not in the library. Treat as future work.

## Bayesian module (`Inference/Bayesian.agda`)
1. Prior `π : 1 ⇒ M Θ` (an element of the monad, or a probability).
2. Joint `π ⊗ law : 1 ⇒ M (Θ × X)` via `bind`, strength.
3. Posterior given data `x`: `condition`/`score` by the likelihood, then `normalize` (all exist: discrete
   `Example/Bayes.agda`, continuous `SFiniteStat.normalize`). Continuous data needs a likelihood *density*,
   so Plan 2's real-valued layer, plus a Gaussian density, plus the Gaussian integral for the evidence in the
   continuous case.
4. Theorems: the discrete Bayes rule (done); evidence formula; sequential updating (posterior after two
   observations equals posterior with the product likelihood); posterior predictive.
5. Conjugate families as worked examples that need only polynomial densities: Beta–Bernoulli (the Beta
   integral is a finite computation for integer parameters), then Gaussian–Gaussian (needs exp).
6. Disintegration is open for QBS (Vákár–Ong); do not rely on it. Define the posterior through the explicit
   likelihood form above.

## Bridges
- **Decision-theoretic:** Bayes risk `∫ π(θ) · risk(θ̂, θ)` for an estimator, linking the two views.
- **Likelihood principle:** the likelihood function (θ ↦ density at the observed x) is the shared object; both the MLE
  and the posterior are defined from it.
- **Laws as hypotheses:** all theorems are generic in `IsStatisticalQBSLike`, so they hold for the discrete models
  (finite examples, cheap to run) and the continuous model alike.

## Staging
1. Plan 1 (docs) and Plan 2 (signed layer, uniform moments, estimator theorem) first. Nothing here is useful earlier.
2. `Model`, `law^n`, `bias`, `variance` as an abstract, generic layer, with the uniform instance from Plan 2.
3. Bayesian module over the discrete model (reuse `Example/Bayes.agda`): Bernoulli with a finite grid of parameters.
   This gives the frequentist/Bayesian side-by-side on one model without any new analysis.
4. Continuous parameter with the uniform prior and Bernoulli data (Beta–Bernoulli, polynomial densities).
5. Gaussian: density, exp, Gaussian integral; both Gaussian estimation theorems and Gaussian–Gaussian conjugacy.
6. Confidence intervals, tests, MLE, Cramér–Rao (long term).

## Open questions
- How should iid samples be typed: `X ^ n`, a stream, or `Fin n → X`? `Fin n → X` composes best with `Complete.agda`.
- Whether to extend `StatisticalInterface` or keep `Model` as separate record over it. Preference: separate; the
  interface is already 34 fields.
- Whether frequentist coverage statements need probabilities as *real-valued* (lower reals suffice for `≥ 1 − α`
  in one direction, but not in general). Resolve when confidence sets are reached.
- Constructive foundations (see `Docs/ConstructiveLit.md`): keep named hypotheses so this layer stays portable.
