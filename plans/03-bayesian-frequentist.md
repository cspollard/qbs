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
- **Not on the critical path (done, see "3c status"):** well-definedness of `E` on the quotient `TQ X`
  (`p ≈ᵖ q → E-at p g ≃ E-at q g`), `E-resp`.  Statistics are bounded, so rescaling replaces truncation and monotone
  convergence.
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

### 3c status

Status: `Inference/Sampler` and `Inference/UniformSampler` are back on `main` (2026-11-01, see "3d step 4 outcome"); they were off it for a while because `Sampler` took >12 CPU-minutes and several GB to check.  Done there: `Continuous/SignedTests` (`CutQ`, `J-bounded`, `pullback`) and `Inference/Sampler` (`draw-random`, `iid-moments`, `samplerModel`, `E-at-sampler`).  `Inference/UniformSampler` validates the bridge: the uniform distribution as a sampler (one-point parameter space, identity test) has the single-draw moments of `UniformVariance`, and the unbiasedness theorems follow from `iid-moments`. `E-resp` (well-definedness of `E-at` on `TQ X`) is done on `main` in `Inference/ExpectationResp`, without truncation or monotone convergence: a statistic bounded by `N` is rescaled by `2⁻ᴺ` to a [0,1]-valued test, so `p ≈ᵖ q` applies directly, and `J-scale` plus cancelling `2⁻ᴺ` recovers its integrals.  That module defines `E-at` itself (the same formula as `Sampler.E-at`), so it does not depend on `Sampler`.  `Inference/BernoulliCompare` (Bayesian vs frequentist on the fair or two-headed coin) is on `main`, complete (see "3d step 4 outcome").

### 3d: expectations over continuous measures (roadmap, 2026-11-01)

Where things stand on `main`:
- `Continuous.∫` integrates [0,1]-valued tests, with `∫-map`, `∫-η`, `∫-join`; `Lebesgue.J` integrates unbounded
  [0,∞]-valued functions, with monotone convergence (`Analysis/Unbounded`) and Tonelli for kernels (`Analysis/Tonelli`).
- `SignedIntegral.E` integrates signed functions with integrable parts (`E-+`, `E-neg`, `E-scale`, `E-const`);
  `Variance` has `Var f ≃ E[f²] − (E f)²`.
- `E-at p g` (bounded signed test `g : STest X` under `p : Pre X`) and `E-resp` (it respects `≈ᵖ`), in
  `Inference/ExpectationResp`.
- Worked distributions: only the uniform (mean, CDF, second moment, variance); `Analysis/Density` builds measures
  from densities.  `Inference/UniformExperiment` proves unbiasedness for i.i.d. uniform draws on an interval.
- Values are lower reals and signed values are formal differences without division, so results are stated multiplied
  out (e.g. `x12 (Var u) ≃ 1S`).

Steps, in order of effort:
1. **The calculus of `E-at`** (done: `Inference/Expectation`, `Inference/ExpectationProduct`): `E-at (η x) g ≃ g x`,
   `E-at (map f p) g ≃ E-at p (g ∘ f)`, linearity in `g`, constants; stretch: the tower law
   `E-at (join P) g ≃ E-at P (λ q → E-at q g)` (needs `q ↦ E-at q g` as an `STest (TQ X)`, as `∫ᶠ` is for `∫`) and
   independence under the strength (`E[f(x) g(y)] = E f · E g`, via the Fubini already proved for `∫`).  Expected to
   reuse the rescaling trick of `E-resp`: prove for [0,1] tests through the `∫` laws, rescale by `2⁻ᴺ`, cancel.
2. **[done, see outcome below]** **Unbounded statistics.**  `STest` requires one natural-number bound, so `E-at` cannot express, e.g., `E[x²]` for a
   distribution with unbounded support.  Extend `E-at` and `E-resp` to integrable tests; `SignedIntegral` already
   allows integrable parts, and monotone convergence exists.  Real work.
3. **[partly done, see outcome below]** **More distributions.**  Bernoulli is nearly free.  Density-defined ones (exponential, Gaussian) need the density
   (`e^{−x}`, …) as a measurable `[0,∞]`-valued function, which the library does not have yet; `Density.densM` then
   gives the measure.
4. **[done, see outcomes below]** **The sampler–monad bridge.**  `Inference/Sampler` is off `main` (over 12 CPU-minutes to check, see "3c status");
   making it cheap would bring back `BernoulliCompare` (branch `orphaned-wip`) and the frequentist results stated over
   samplers.

3d step 1 outcome (2026-11-01): `Inference/Expectation` (about 7 s to check) defines the test algebra on `STest`
(`valT`, `_+T_`, `-T_`, `scaleT`, `constT`, `precompT`, and `expT g`, the test `q ↦ E-at q g` on `TQ X`) and proves
`E-at-η`, `E-at-map`, `E-at-+`, `E-at-neg`, `E-at-scale`, `E-at-const`, `E-at-expT` and the tower law `E-at-join`
(`E-at (joinPre P) g ≃ E-at P (expT g)`).  The algebraic laws hold because the pulled-back signed functions agree
definitionally with the `SignedIntegral` operations; the tower law uses `∫-join` and the rescaling of `E-resp`.

Independence (`Inference/ExpectationProduct`, about 9 s to check): the product test `f ⊗T g` (parts `f⁺g⁺ + f⁻g⁻` and
`f⁺g⁻ + f⁻g⁺`, bound `2NM`, `valT-⊗T` by `≃-refl`); `E-at-cong` (pointwise `≃` tests have `≃` expectations, via
`cancel-bnd`); `E-at-σ` (`E-at (σPre (x , q)) (f ⊗T g) ≃ valT f x *S E-at q g`); and `E-at-⊗`
(`E-at (p ⊗ᵖ q) (f ⊗T g) ≃ E-at p f *S E-at q g`) for `p ⊗ᵖ q = joinPre (mapPre (σq q) p)`, the left-strength product.

3d step 2 outcome (2026-11-01): `Inference/ExpectationInt` (about 8 s).  `ITest p` (parts `Hom X CutQ` whose pulled-back
integrals under `p` are finite), `E-atᴵ`, `fromSTest` with `E-atᴵ-fromSTest` (agrees with `E-at`, `≃-refl`),
`truncHom h k` (the truncation `tr k ∘ h` as a [0,1] test), `J-resp∞` (`p ≈ᵖ q` equates `J` of any unbounded
`h : Hom X CutQ`, infinite values included: `J-def` unfolds `J` to `⨆ₖ 2ᵏ · ∫ (tr k ∘ h)`, and each truncated
integral is an `∫` of a test), `transportI`, `E-respᴵ`, and linearity (`_+I_`, `-I_`, `scaleI`, `E-atᴵ-+`, `E-atᴵ-neg`,
`E-atᴵ-scale`).  No new lemma about `J` was needed.  Callers pass `{p = p} {q = q}` to `J-resp∞`/`transportI` (`_≈ᵖ_` is a function, so they are not inferable).

3d step 3 outcome (2026-11-01): `Inference/ExpectationExamples` (about 7 s) and additions to `ExpectationInt`.
- `ExpectationInt`: `J-η`, `valI`, `E-atᴵ-η`, `precompI`, `E-atᴵ-map` (step 2 is now complete).
- Uniform through `E-at`: `idT`, `sqT : STest AQ`; `E-at-uniform-id : E-at uniform idT ≃ ι ½` (reusing `UniformMean`)
  and `E-at-uniform-sq` (the second moment, reusing `UniformMoment`).
- Bernoulli(½): `bern : Pre AQ`, the first bit of the fair coin valued in {0,1} ⊆ [0,1]; `E-at-bern : E-at bern idT ≃ ι ½`;
  `E-at-bern²` (two independent draws, by `E-at-⊗`: `≃ ι ½ *S ι ½`) and its multiplied-out quarter.
- Not done: Bernoulli as a `Pre` on a Boolean QBS.  The library has no Boolean QBS with measurable indicators
  (`CodiscQ Bool` makes them non-measurable; `1Q +Q 1Q` in `Colimits` would work but needs a copairing into `CutQ`).

What an exponential distribution would need (assessment, not started):
1. `e^{−x}` as a lower cut.  Lower cuts have only non-negative sums and no division, so `e^{−x}` needs a direct cut
   (`q < e^{−x}` iff `q · e^{x} < 1`) or an inverse.  Missing: `exp` as a `⨆` of partial sums with `exp-add` (a Cauchy
   product; `Series`/`SeriesSup` have `psum` and monotone convergence but no Cauchy product), monotonicity, and
   `exp x * exp (−x) ≈ 1`.
2. Measurability of `r ↦ e^{−x(r)}` (`Meas-⨆` with `Meas-⊗`/`Meas-pre` on the partial sums).
3. A base measure on [0,∞): every measure lives on Cantor space, so either push the uniform along an unbounded map
   (needs `log` or `1/u`) or use the s-finite Lebesgue measure (`SFinite*`, `Tonelli`).  Normalisation needs
   `∫₀^∞ e^{−x} dx = 1` as the limit of `1 − e^{−N}`.
4. The mean `E[X] = 1` from `x e^{−x}`: integration by parts, or a self-similarity recursion like `UniformMean`.
5. Transfer: `densM` gives a `Measure`; a `Pre` on a QBS of [0,∞) with the statistic `x` as an `ITest`, after which
   `E-atᴵ`, `J-resp∞` and `E-respᴵ` apply.
The CDF route (push the uniform along `−log(1−u)`) avoids 1–3 but needs `log` as a measurable `AQ → [0,∞]`, with the
same series obstacles.

3d step 4 outcome (2026-11-01): `Inference/Sampler` and `Inference/UniformSampler` are back on `main`, about 9 s and
under 1 GB each (dependencies built).
- Diagnosis: the cost was declaring a `record` inside the parameterised `Sampler` module.  `record SingleMoments`
  (two fields) exhausted a 3 GB cap after about 60 s, mostly GC; it still did with one field, `no-eta-equality`, or the
  field type factored out, while the same type as a plain definition was cheap, and a trivial record at top level
  outside the module was cheap.  `record Model` cost about 25 s and 0.8 GB extra the same way.  Cause inside Agda
  unknown.  **Lesson: avoid declaring records inside heavily parameterised modules here; use Σ/× or synonyms.**
- Changes: `SingleMoments` is a pair `(∀ θ → MeanAt θ) × (∀ θ → SecondAt θ)`; `Model Θ X` is the synonym
  `Hom S Θ (TQ X)`; `E-at` comes from `ExpectationResp`; ported to `Func`-valued `α`, `LEM₁`, no `funext`;
  `Frequentist.Moments` is per-θ.  `UniformVariance` gained `u⁺`/`u⁻` (its `u` is `abstract`).
- Not done: `BernoulliCompare`.  The `orphaned-wip` version is a skeleton (the two samplers and the theorem are holes),
  so it needs new proofs: the head indicator `[expansion r ≤ t]` as an `STest`, its expectation from `UniformCDF`, and
  the link to `CoinBias.Additive`.

`BernoulliCompare` (2026-11-01, about 9 s, under 1 GB): `headSampler t = cdfTest t ∘H uniformSampler` (draw
`[expansion r ≤ t]`), `twoHeadedS`/`fairS`/`sampler h`; `single-draw` (`E[head | two-headed] ≃ 1`, `E[head | fair] ≃ ½`,
from `UniformCDF.cdf`); `likelihood-is-expectation` (single-draw expectation ≃ `CoinBias.heads`, used directly through
`Additive`); `evidence-is-prior-expectation` (`½·E[head | two-headed] + ½·E[head | fair] ≃ ½·1 + ½·½`, the right-hand side
of `CoinBias.evidence-heads`).  Weaker than the skeleton's intent in one way: the prior is the explicit two-point ½/½
sum, not an expectation over a kernel on the hypothesis space.  Branch `orphaned-wip` is now fully superseded.

Exponential groundwork, step 1 of "What an exponential distribution would need" (2026-11-02): done.
- `Analysis/Cauchy` (generic): `⨆-*-lub`, and `cauchy : ∑ᶠ a * ∑ᶠ b ≈ ∑ᶠ conv` for non-negative series, with
  diagonal sums `diag` defined without ℕ subtraction.
- `Analysis/Exp` (`module Exp A`, `module WithInv inv inv-ok`, abstract in any `OmegaSemiring` with inverses of
  naturals given as plain parameters, no record): `exp x = ∑ᶠ (xⁿ/n!)`, `exp-zero`, `exp-mono`, `exp-cong`, `1+≤exp`,
  and `Add.exp-add : exp (x + y) ≈ exp x * exp y` (Cauchy product plus the recurrence `(n+1)·T(n+1) = (x+y)·T(n)`,
  no binomial theorem).
- `Analysis/ExpLower`: the lower-cut instance (`inv n = qC (1/(n+1))`, new `qC-mul`), `expC`, `expC-zero`,
  `expC-mono`, `expC-cong`, `1+≤expC`, `expC-add`.
- Next for the exponential: `e^{−x}` as a cut (`q < e^{−x}` iff `q · e^{x} < 1`, cut properties from `exp-mono` and
  `exp-add`); measurability of `r ↦ e^{−x(r)}` (`Meas-⨆` over partial sums, plus a measurable threshold for
  `q · e^{x(r)} < 1`); then a base measure on [0,∞) and normalisation (items 3–5 above).

`e^{−x}` (2026-11-02, `Analysis/NegExp`, `module NegExp (lem : LEM₀)`, about 4.5 s): `negExp x` is the cut
`q ∈ negExp x ⇔ Σ p. q < p × (∀ s ∈ expC x → p * s < 1)` (openness is immediate, `x = ∞` gives `zeroC`).  Proved:
`negExp-anti`, `negExp-zero : negExp zeroC ≋ oneC`, `negExp≤1`, `negExp-expC≤1 : negExp x ⊗ expC x ⊑ oneC` (all x),
`Meas-expC` and `Meas-negExp` (for any threshold-measurable `h`, not only bounded ones).  Not done: the reverse
`oneC ⊑ negExp x ⊗ expC x` for finite x.  Missing lemma: for 0 < ρ < 1 and `expC x` bounded there is s ∈ `expC x`, s > 0,
with ρ·s′ < s for all s′ ∈ `expC x` (by LEM; otherwise a chain s₀/ρⁿ contradicts the bound, via Bernoulli's inequality
and `arch`); estimated about 80 lines.

Reverse inequality (2026-11-02, done, about 120 lines; NegExp checks in 11.7 s, timed cold on an idle machine): `oneC≤negExp-expC` and
`negExp-expC : negExp x ⊗ expC x ≋ oneC`, both for `expC x` bounded by a rational B (`∀ s ∈ expC x → s < B`).  Route:
the near-maximal element by LEM, but with a linear chain (`s₀ + n·(1−ρ)·s₀ ≤ s`, by induction) in place of `ρⁿ` and
Bernoulli, then `arch B`.  Still missing: "x ⊑ nat N ⇒ expC x bounded", which needs a bound on the partial sums of
the series (≤ 3 for x ≤ 1, then `expC-add` up to N) in the abstract `Exp` module.

Bounded x (2026-11-02, done): `Exp.exp≤3 : x ≤ 1 → exp x ≤ 3` (geometric bound `ι(n+1) ≤ ½ⁿ`) and
`exp≤three^ : x ≤ natE N → exp x ≤ 3ᴺ` (via `exp-add`, abstract); `ExpLower.expC-bound` (strict rational bound 3ᴺ on
members of `expC x` when `x ⊑ natE N`); `NegExp.negExp-expC-nat : x ⊑ natE N → negExp x ⊗ expC x ≋ oneC`.  So
`e^{−x}·eˣ = 1` holds for every finite x given as bounded by a natural.  Times: Exp 2.9 s, ExpLower 3.4 s,
NegExp 11.8 s (unchanged from before the merge, 11.7 s).  Next: a base measure on [0,∞) and normalisation.

Base measure on [0,∞), item 3 (2026-11-02, done except normalisation).  Lebesgue measure on [0,∞) has mass ∞, so it
cannot be a `Measure` (`I-sub` forces `I 1 ≤ 1`).  It is an s-finite `Pre (XW WQ)` on the weight QBS `WQ` = [0,∞].
- `Continuous/HalfLine` (4.7 s): `shiftPre n` is the uniform shifted to n, and `lebPre = sumPre shiftPre` is
  λ = Σₙ (n + U).  `∫ᴹ-leb h : ∫ᴹ lebPre h ≈ ∑ᶠ n. J fairCoin (h ∘ shiftPt n)` holds for every `h : Hom S WQ WQ`,
  unbounded ones included.
- `Continuous/HalfLineNegExp` (5.2 s): `negExpH` is the test x ↦ e^{−x}.
  - `negExp-add`: e^{−(x+y)} = e^{−x}·e^{−y} for x, y, x+y bounded by naturals.
  - `I-negExp = ∫₀¹ e^{−u} du`, left uncomputed.
  - `∫ᴹ-leb-negExp-split : ∫ e^{−x} dλ ≈ ∑ᶠ n. e^{−n} · I-negExp`.
- Remaining for normalisation:
  - `I-negExp + e^{−1} ≈ 1`;
  - the geometric sum `(∑ᶠ n. e^{−n}) · (1 − e^{−1}) ≈ 1`, multiplied out;
  - combining these into `∫ e^{−x} dλ ≈ 1`.
- Item 5 (transfer) does not go through `densM`, because λ is s-finite rather than a `Measure`.  It needs a
  normalised `Pre` built from the weighted λ instead.

Normalisation (2026-11-02, done): `∫ᴹ-leb-negExp-norm : ∫ᴹ lebPre negExpH ≈ 1#`, i.e. ∫₀^∞ e^{−x} dx = 1, assuming
only LEM₁.
- `Analysis/Exp.exp≤quad : x ≤ 1 → exp x ≤ 1 + x + x²`.  This upper bound is needed for `1 − e^{−h} ≤ h + h²`.
- `Analysis/GeometricNorm` (abstract, `OmegaSemiring` plus `Arch`, 3.3 s):
  - `Geo.total : I + g ≈ 1 → ∑ᶠ gⁿ · I ≈ 1`;
  - `norm`, which pins `x 0 + q 0 ≈ 1` from a first-bit recursion plus error bounds, using `arch` and
    error-doubling invariants, with no limits or cancellation.
- `Continuous/HalfLineUnit` (5.6 s): `I-negExp-unit : ∫₀¹ e^{−u} du + e^{−1} ≈ 1`.  It uses self-similarity, as in
  `UniformMean`, on the family `F j = ∫₀¹ e^{−2⁻ʲu} du`.  There are no Riemann sums.
- `Continuous/HalfLineNorm` (5.0 s): `negExp-pw`, then the combination.
- Next:
  - item 4, the mean `∫ x e^{−x} dλ = 1`;
  - item 5, the exponential as a normalised `Pre` on [0,∞) with `E-atᴵ`.

Mean, item 4 (2026-11-02, done): `HalfLineMean.∫ᴹ-leb-xNegExp : ∫ᴹ lebPre xNegExpH ≈ 1#`, i.e. ∫₀^∞ x e^{−x} dx = 1.
- **K on [0,1]:** `K-pin : K + 2e^{−1} ≈ 1` for K = ∫₀¹ u e^{−u} du.
  - It uses self-similarity on `KK j = ∫₀¹ u e^{−2⁻ʲu} du`.
  - It pins via the new `GeometricNorm.norm-s`, which pins at every scale, not just j = 0.
  - The upper bound comes from the pointwise `(1+t)e^{−t} ≤ 1`.
- **Series:** `GeoMean.total : ∑ gⁿ(nI + K) ≈ 1`, by telescoping `∑_{n<N} gⁿ(nI+K) + (N+1)gᴺ = 1`.
- **Ring identities:** these were moved to the abstract module, because the solver is slow on concrete cuts.
- **Timings:** GeometricNorm 4.1 s (was 3.3 s), HalfLineMean 7.6 s.
- **Correction:** the agent caught a wrong form in my brief (`K + 2g ≈ I`).  The correct forms are `K + 2g = 1` and
  `K + g = I`.
- **Next:** item 5, the exponential as a normalised `Pre` on [0,∞), so that `E-atᴵ` gives E[X] = 1.

Exponential distribution, item 5 (2026-11-02, done).  Items 1–5 of "What an exponential distribution would need" are
now all done.
- **`Continuous/SFiniteReweight` (4.2 s):** a generic density reweighting `reweightPre d p` of an s-finite measure,
  with `∫ᴹ-reweight : ∫ᴹ (reweightPre d p) f ≈ ∫ᴹ p (d·f)`.  `scalePre` is the constant case.
- **`Continuous/ExpDist` (6.0 s):**
  - `expW = reweightPre negExpH lebPre` and `massP-expW ≈ 1`.
  - `expDist = normPre expW 1 … : Pre WQ`, a probability `Pre`.
  - `∫-expDist`, `∫-expDist-one` (mass 1) and `∫-expDist-id` (mean 1).
  - Some definitions are `abstract`.  Without that, unsolved `α.cong` metas appear downstream through the unfolded
    `sumPre`.
- **`Inference/ExpDistMean` (6.3 s):** `idI : ITest expDist` and `E-atᴵ-idI : E-atᴵ expDist idI ≃ 1`.  So
  `E-atᴵ-map`, `E-respᴵ` and linearity now apply to the exponential, with no bridging lemma.
- **Possible follow-ups:** memorylessness, the exponential as a prior or likelihood in a `Sampler` model.  E[X²] = 2 is
  now done (below).

Second moment and variance (2026-11-02, done):
- **`Continuous/HalfLineMoment2`:** `∫ᴹ-leb-x²NegExp : ∫ x² e^{−x} dλ ≈ 2`.  On [0,1] it uses
  `L-pin : L + 5e^{−1} ≈ 2`, pinned with `norm` on a combined quantity, using the K and I pins at every scale.
- **`Analysis/GeometricMoment2`:** `GeoMom2.total`, which telescopes with error (N²+2N+2)gᴺ.
- **`Continuous/ExpDistSq`:** `∫-expDist-sq ≈ 2`.
- **`Inference/ExpDistVar`:**
  - `sqI` and `E-atᴵ-sqI ≃ 2`.
  - `var-expDist : E[X²] − (E X)² ≃ 1`, stated in `Sg`.  `Analysis/Variance.Var` needs a bounded function, so it does
    not apply here.
- **`scripts/doccheck.py`:** module-name regexes now accept digits.  Before this they silently skipped names like
  `HalfLineMoment2`.
- **Times:** GeometricMoment2 4.1 s, ExpDistSq 6.0 s, ExpDistVar 7.8 s, and HalfLineMoment2 **45.9 s, 1.0 GB**.  That
  makes HalfLineMoment2 the slowest module in the tree, ahead of `Continuous/Strong` at about 41 s.  It is a
  candidate for a check-cost pass.
- **Check-cost pass (done):** HalfLineMoment2 went from 45.9 s to 14.9 s (1.03 GB to 0.86 GB).  Exported statements
  are unchanged.
  - The profile showed 28 s in `x2-rec`.  The cost was Agda comparing the type of the abstract identity
    `x2-rec-alg` with the goal by reducing `Lsplit` through concrete cut arithmetic.
  - Fix: make `Lsplit` `abstract` in `GeometricMoment2`, keep the body in a concrete `Lsplit′`, and add
    `Lsplit-def` as the bridge.
  - The split lemma now ends in `∑ᶠ GeoMom2.term`, which saves another 5.5 s of conversion.
  - Lesson: polynomial expressions shared between an abstract algebra module and a concrete instance should be
    `abstract` at the boundary.  Otherwise unification unfolds them through the concrete semiring.
  - Next hot spot: `shift-split`, at 2.3 s.

Bernoulli on a Boolean QBS (2026-11-02, done; this closes the "Not done" item of 3d step 3).
- `QBS/BoolQ` (2.6 s) is generic in the random source.  It defines `BoolQ = 1Q +Q 1Q`, `boolQ`, `constQ`, and
  `ifQ a b = copair (constQ a) (constQ b)`; the laws `ifQ-true` and `ifQ-false` hold by `refl`.
- `Inference/BoolDist` (6.2 s):
  - `bitB` is the first bit as a random element of `BoolQ`, and `bernB : Pre BoolQ`.
  - Tests: `ifT a b` and `indT`.
  - `E-at-bernB-if : E-at bernB (ifT a b) ≃ ½a + ½b` and `E-at-bernB-ind ≃ ½`.
  - The link to the old `bern` is `bernB≈bern : mapPre toAQ bernB ≈ᵖ bern`.
  - The biased coin is `bernθ θ`, the indicator of `{expansion ≤ θ}` (Borel by `Below-borel`, decided by LEM).  It
    satisfies `E-at-bernθ : E-at (bernθ θ) indT ≃ θ` for every θ ≤ 1, not only dyadic θ.  `indB` turns any decidable
    Borel set into a random element of `BoolQ`.
- Not done:
  - `bernθ ½ ≈ᵖ bernB`.
  - The first bit as a `Hom`: the library has no QBS for Cantor space itself.
- Next: the prior as a kernel.  That means θ ↦ `bernθ θ` as a `Hom AQ (TQ BoolQ)`, with the uniform prior on θ.  It
  gives the evidence for heads as `∫ θ dθ = ½`, which is Beta–Bernoulli with a continuous prior.

Coin with a uniform prior on θ (2026-11-02, done): `Inference/CoinUniformPrior` (11.8 s, 1.06 GB).
- **Kernel:** `coinKernel = samplerModel flipS : Model AQ BoolQ`, a measurable kernel θ ↦ `bernθ θ`.  Measurability
  in θ comes from `Below2-borel : Fun h → Fun t → Borel {x | h x ≤ t x}`, a variable-threshold version of
  `Below-borel`.
- **One flip:** `marg = joinPre (mapPre coinKernel uniform)`, and `E-at-marg : P(H) ≃ ½`.  The proof uses the tower
  law and `E-at-uniform-id`.
- **Two flips:** `coinKernel² : Hom AQ (TQ (BoolQ ×Q BoolQ))` gives two flips that are conditionally independent
  given θ.
  - `E-at-marg² : P(HH) ≃ ⅓`.
  - `HH-from-H : 3·P(HH) ≃ 2·P(H)`, i.e. the posterior mean after one head is 2/3, multiplied out.
- **Discrete versus continuous:** this is the continuous-prior counterpart of `CoinBias` and `BernoulliCompare`.
  Those use an explicit two-point prior; here the prior is an expectation over a kernel on the hypothesis space.

Continuous posterior (2026-11-02, done): `Inference/CoinPosterior` (7.1 s, 1.0 GB).
- **Bayes' rule in general:** `posterior ℓ p n h = normPre (reweightPre ℓ (ιPre p)) n h` (abstract), with
  `bayes : ∫ f d(posterior) ≈ n · ∫ ℓ·f dp`.
- **The coin:** after one head under the uniform prior, `post1` is Beta(2,1), with
  `post1-mean : 3 · E[θ | H] ≈ 2`.  The same result is also stated through `E-at`.
- **Sequential = batch:** `post2-agree : post2-seq ≈ᵖ post2-batch`.  Updating on H and then on H again gives the same
  posterior as updating on θ² at once.  So sequential updating is a theorem for continuous priors as well, matching
  the discrete `Bayesian.sequential`.

Independence for integrable tests (2026-11-02, done):
- **`Inference/ExpectationIntProduct` (8.6 s, 1.07 GB):**
  - `J-join`, the unbounded analogue of `∫-join`, via `Tonelli.J-bind`.  No truncation or sup interchange is needed.
  - `J-σ`, `J-⊠ : Jp (p ⊗ᵖ q) (u·v) ≈ Jp p u · Jp q v`.
  - `_⊗I_` and `E-atᴵ-⊗`.
- **`Inference/ExpDistPair` (13.0 s, 1.14 GB):** for two independent exponential draws, E[XY] ≃ 1, E[X+Y] ≃ 2 and
  E[X² + Y² + 2XY] ≃ 6.
  - X and Y are built as products with the constant test, because the marginal law `mapPre fstQ (p ⊗ᵖ q) ≈ᵖ p` is
    not yet proved.
  - The expanded test is not yet identified with the pointwise statistic (x+y)².

Product marginals (2026-11-02, done): `Inference/ProductMarginals`.
- **Marginal laws:** `fst-marginal : mapPre fstQ (p ⊗ᵖ q) ≈ᵖ p` and `snd-marginal`.
- **Integrable tests:** `E-atᴵ-cong` gives equal expectations for pointwise-equal tests.
- **Exponential pair:**
  - the coordinates `fstI`/`sndI` with E ≃ 1;
  - the pointwise statistic `sumSqI` = (x+y)², with E ≃ 6;
  - `var-sum : Var(X+Y) ≃ 2`.
- **Check cost:** about 31 s and 1.4 GB, the second-slowest new module.  Moving `var-arith` into the abstract `Alg`
  saved 3 s.  The rest is unfolding of concrete cut arithmetic in `sumSqI` (9 s), `var-arith` (4.8 s) and
  `pos-pw`/`neg-pw` (2.9 s each).  The cost pass that followed is recorded below.

n flips under a uniform prior (2026-11-02, done):
- **`Continuous/UniformMomentN` (5.4 s):** `moment-N : (n+1)·∫uⁿ ≈ 1` for all n.
  - It needs no binomial coefficients.  It uses the Pascal recursion `G j (k+1) = ½(G j k + G (j+1) k)` on
    `G j k = ∫ eʲ tᵏ` with first-bit self-similarity.
  - The unknown top moment is cancelled with `cancel≤`, `arch` and `complement`, needing only `Arch`.
- **`Inference/CoinUniformPriorN` (9.3 s):**
  - n+1 conditionally independent flips, `Kn n`, with the all-heads test `AH n`.
  - `heads-prob : (n+2)·P(Hⁿ⁺¹) ≃ 1`.
  - Laplace's rule of succession, `succession : (n+2)·P(Hⁿ⁺¹) ≃ (n+1)·P(Hⁿ)`.
- **`Inference/BernHalf` (5.8 s):** `bernθ-half≈bernB : bernθ ½ ≈ᵖ bernB`.
- **`longcheck` regression:** the merge pushed `longcheck` to 37 flagged (`BernHalf.I-θ`, `UniformMomentN.S-step`).
  The agent had misread the threshold.  Fixed by the cleanup below.

Longcheck fix and check-cost pass (2026-11-02, done):
- **`longcheck`:** back to 35 flagged.  `BernHalf.I-θ` lost its local helpers to module-level `θ-go`/`θ-split`, and
  `UniformMomentN.S-step` is split into `S-step₁`/`S-step₂`.  No exported statements changed.
- **Cause of the cost:** mixed forms of `_+_`.  The instantiated `Alg` statement uses
  `CommutativeSemiring._+_ (commutativeSemiring A)`, while numerals like `twoS`/`sixS` use `OmegaSemiring._+_ A`.
  Since `Cut` is an eta record, comparing the two unfolds the cut arithmetic field by field.  Separately,
  `α expPair ⟨$⟩ r` was unfolded inside each `sumSqI` field and in `pos-pw`/`neg-pw`.
- **Cure:**
  - State the arithmetic in a module generic over a `CommutativeSemiring` and a `SubSemiring` (`VarGen.var-gen`,
    `SixGen.six-gen`).  The numerals' pos/neg parts enter as small equations, discharged by `refl` at the use site,
    so the use site compares only small terms.
  - State the pointwise laws for an arbitrary pair `z` (`pos-z`, `neg-z`), and give `sumSqI` a typed `retest` helper.
  - This pattern probably applies elsewhere in the library.
- **Timings (forced recheck, dependencies warm, my run):**

  | Module | Before | After |
  |---|---|---|
  | `ProductMarginals` | 30.7 s, 1.4 GB | 9.6 s, 1.0 GB |
  | `ExpDistPair` | 11.6 s, 1.1 GB | 7.5 s, 1.1 GB |
  | `BernHalf` | 5.8 s | 5.8 s |
  | `UniformMomentN` | 5.4 s | 5.3 s |
  | `CoinUniformPriorN` | 9.3 s | 9.1 s |

  About 6.5 s of "Miscellaneous" remains as fixed overhead in both product modules.

Beta integral for integer parameters (2026-11-02, done):
- **`Continuous/BetaIntegral` (4.5 s, 0.6 GB):** `Bt k m = ∫ uᵏ vᵐ`, where `v` is the complement of the binary
  expansion (`complF`) and `uv : u + v ≈ 1` holds pointwise.
  - `Bt-add : B(k,m) ≈ B(k+1,m) + B(k,m+1)`; `Bt-base : (k+1)·B(k,0) ≈ 1`, from `moment-N`.
  - `beta-closed : (k+m+1)!·B(k,m) ≈ k!·m!`.
  - `beta-conj : (k+m+2)·B(k+1,m) ≈ (k+1)·B(k,m)`.  This is the general Beta–Bernoulli posterior mean
    (k+1)/(k+m+2) after k heads and m tails, on the integral side; it is not yet tied to a coin kernel.
  - The algebra is in `AlgB`, over an abstract Archimedean ω-semiring.  Each induction step cancels a bounded term
    with `BoundedCancel.cancel-bnd`.
- **Merge fixes (mine):**
  - The agent used `rewrite`, which `doccheck` forbids (plans/04).  I replaced it with an index-transport helper,
    `ix`.
  - The branch was cut from `597bc3a`, before the cleanup.  That is why the agent saw 37 flagged; main stays at 35.
- **Not done:** the symmetry B(k,m) = B(m,k); a coin model with k heads among k+m flips.

`Continuous/Strong` check-cost pass (2026-11-02, done): 42.6 s → 21.0 s (1.29 GB → 1.33 GB, my run).
- **Cause:** not arithmetic.  `Strength.commutative` took 37 s of 40 s, unifying the `∫-join`/`Setoid.trans` chain
  (metavariable endpoints) against the goal's categorical composites.  `RS` was also built from `strength` while
  the goal used `StrongMonad.strength strongMonad`, which cost about 27 s in a `refl` check.
- **Fix:**
  - Build `RS` from `strongMonad`.
  - Add typed `refl` lemmas `lhsEq`/`rhsEq` for each side at the goal's form, and type the Fubini chain `mid`.
  - `commutative = trans lhsEq (trans mid (sym rhsEq))`.  Exported statements are unchanged.
- **Importers:** unchanged (`ProbInstance` 5.1 s, `CoinUniformPrior` 12.5 s).  A first `CoinUniformPrior` run gave
  19.8 s; two reruns gave 12.5 s.
- **What remains:** about 13 s in `commutative`, almost all in checking `sym rhsEq` (`F₁ σ ∘ τ` against `σH`).  Next:
  an abstract wrapper, or a definitional lemma `σ ≡ σH`, so the comparison does not unfold `strength`.

### Expectations of functions under continuous densities: what is missing (assessment, 2026-11-02)

**Goal.** For a density `d` and a function `g`, make `E[g(X)] = ∫ g(x) d(x) dx` routine to prove for each new
`(d, g)`.  Today every such expectation is a bespoke proof:
- the identity and the square under the exponential;
- `e^{−x}`, `x e^{−x}` and `x² e^{−x}`, each with its own self-similarity recursion (`HalfLineUnit`, `HalfLineMean`,
  `HalfLineMoment2`, `GeometricNorm`, `GeometricMoment2`), about 300–600 lines each.

Three things are missing:
- a generic way to package a density as a distribution;
- a general method for computing `∫ h dλ` for concrete `h`;
- integrability side conditions for signed `g`.

What exists already:
- `lebPre = sumPre shiftPre`, Lebesgue measure on [0,∞) as an s-finite `Pre`.
- `reweightPre`/`∫ᴹ-reweight` for densities, and `normPre`.
- `ExpDist` as the one worked instance.
- `E-atᴵ` with `ITest`, `E-atᴵ-map`, `E-respᴵ` and linearity.
- `J` monotone convergence and Tonelli.
- `Analysis/Density.densM` on the `Measure` side.

Items, in dependency order:

1. **Generic density distributions (cheap; generalises `ExpDist` and `ExpDistMean`).**
   - Given `d : WQ ⇒ WQ` with `∫ᴹ lebPre d ≈ 1#`, define `densDist d nrm : Pre WQ` with
     `∫-dens : ∫ᴹ (ιPre (densDist d nrm)) f ≈ ∫ᴹ lebPre (d · f)`.
   - `densI g`: an `ITest` built from the bounds `Bnd (∫ᴹ lebPre (d · g⁺))` and the same for `g⁻`.
   - `E-atᴵ-dens : E-atᴵ (densDist d nrm) (densI g) ≃` the signed Lebesgue integral of `d · g`.
   - Then `ExpDist` becomes an instance, and every later distribution costs one normalisation proof.

2. **A derivative-free fundamental theorem of calculus, in tail form (the key item).**
   - Lower reals hold no negative values, so use a non-negative *tail antiderivative* `G` (`G(x) = ∫ₓ^∞ h`).
   - Criterion on dyadic intervals, for `h` monotone on `[a, b]`:
     `(b−a)·h(b) ≤ G(a) − G(b) ≤ (b−a)·h(a)` (decreasing case), stated additively without subtraction.
   - Conclusion: `∫ₐᵇ h + G(b) ≈ G(a)`.
   - Proof:
     - Integrals of dyadic step functions are their sums, from the first-n-bits structure of the fair coin.
     - The criterion sums and telescopes over the 2ⁿ pieces.
     - Lower and upper sums differ by `2⁻ⁿ (h(a) − h(b))`.
     - Close with the archimedean cancellation of `UniformMomentN` (`cancel≤`, `arch`, `complement`/`cancel-bnd`).
   - Half-line: `lebPre = sumPre shiftPre` gives `∫₀^∞ h + ⨅ₙ G(n) ≈ G(0)`.  With `G(n) → 0` this is `∫₀^∞ h ≈ G(0)`,
     via the telescoping series and monotone convergence.
   - Piecewise monotone `h`: split at finitely many dyadic points.
   - After this, each new integral reduces to *pointwise algebra* about `G` and `h`, using `1+t ≤ eᵗ`, `exp-add` and
     polynomial bounds, with no new measure theory.  Example: `G(x) = e^{−x} ∑_{k≤n} n!/k! xᵏ` for `h = xⁿ e^{−x}`.
   - **Integration-by-parts variant** (needed for the Gaussian, item 6): `∫ₐᵇ h + G(b) ≈ G(a) + ∫ₐᵇ k`, for a
     criterion whose increments are bounded by `h − k` on each piece.

3. **All polynomial moments of the exponential:** `∫ xⁿ e^{−x} dλ = n!`, as a first use of item 2.
   - It replaces `HalfLineMean` and `HalfLineMoment2` by instances.
   - It gives finiteness of every polynomial moment, which item 4 needs.
   - Alternative if item 2 stalls: an n-indexed recursion like `UniformMomentN`.

4. **Integrability by domination.**
   - `Bnd`-monotonicity of `J`: if `g⁺, g⁻ ≤ c·(1 + xᵏ)` and `d` has a finite k-th moment, then `densI g` exists.
   - Without this, every `ITest` needs a bespoke finiteness proof.

5. **A function library with measurability and monotonicity, closed under the operations used** (superseded by the
   certificate calculus in "Revised direction" at the end of this plan):
   - polynomials (`mulH`, sums, constants);
   - `negExp ∘ p` for polynomial `p ≥ 0`;
   - dyadic rescaling `x ↦ 2ᵏ x`.
   - Each comes with `Meas`, monotonicity on intervals (for item 2), and a growth bound (for item 4).
   - Pieces exist (`Meas-⊗`, `Meas-negExp`, `xNegExpH`, `sqW`) but are scattered across modules.

6. **The whole real line, for symmetric densities and the Gaussian.**
   - A QBS of signed reals.  `Continuous/RealModel` is [0,∞] only; the signed layer has `Sg`, but there is no
     `ℝ`-valued QBS with Lebesgue measure.
   - Lebesgue measure on ℝ as `leb⁺ + reflect leb⁻`.
   - A symmetry lemma: `E[g] = 0` for odd `g` under an even density, via the `pos`/`neg` parts on each half.
   - **Gaussian without π:**
     - Leave the normaliser `Z = ∫ e^{−x²/2}` abstract, and prove it finite and positive by a bound such as `e^{−x}`
       domination.
     - Item 2's integration-by-parts form, with `G(x) = x e^{−x²/2}` and `k = e^{−x²/2}`, gives
       `∫ x² e^{−x²/2} = Z`.  So `Var = 1` and `E[X] = 0` hold with no value for `Z`.
     - `Z = √(2π)` (π as a cut, polar coordinates or Wallis) is a separate, much larger item, and none of the moment
       results need it.

7. **Affine change of variables (needed for parameterised families).**  (Revised: families as pushforwards plus one
   change-of-variables theorem; see "Revised direction" at the end of this plan.)
   - Covers Exp(λ), N(μ, σ²), and posteriors over a rate.
   - Scaling: `∫ h(λx) dλ(x) · λ ≈ ∫ h`.  Translation by a real `c`: only integer shifts exist, as `shiftPre`.
   - Route: prove both for the functions of item 5 through item 2 (both sides have the same tail antiderivative up to
     rescaling).  This avoids a general uniqueness-of-measures theorem.

Suggested order: 1 and 2 in parallel (they are independent), then 3 (validates 2), 4 and 5 together, then 6 and 7.

Performance notes:
- Do item 2's algebra (telescoping, squeeze, cancellation) in modules generic over an abstract Archimedean
  ω-semiring, like `AlgB` in `BetaIntegral`.
- Keep concrete instances to small equations, as `VarGen`/`SixGen` do.  Expect item 2 itself to be one or two modules
  of about 300 lines; each later integral should then be well under 100.

Density item 1, generic density distributions (2026-11-02, done):
- **`Continuous/DensityDist` (6.0 s, 0.86 GB):** `densW d = reweightPre d lebPre` (abstract) and
  `densDist d nrm = normPre (densW d) 1# _` (abstract), for `nrm : ∫ᴹ lebPre d ≈ 1#`.  Exports `∫-dens`
  (`∫ᴹ (ιPre (densDist d nrm)) f ≈ ∫ᴹ lebPre (mulH d f)`) and `∫-dens-one`.
- **`Inference/DensityExpectation` (7.3 s, 0.97 GB):**
  - `J-dens`;
  - `densI d nrm g⁺ g⁻ b⁺ b⁻ : ITest (densDist d nrm)`, from `Bnd` of `∫ᴹ lebPre (mulH d g±)`;
  - `E-atᴵ-dens`, giving `≃ (∫ d·g⁺ − ∫ d·g⁻)`;
  - `zero-integral`;
  - the exponential's mean and second moment as one-line instances, `E-atᴵ-idD` and `E-atᴵ-sqD`.
- **Not done:**
  - `densDist negExpH expNrm ≈ᵖ expDist`.  The integrals agree, but the two `Pre`s are not shown equal.
  - Parts are `WQ`-valued (`toC` converts them).
- **Merge fix (mine):** removed backticked module paths from the `Interface.md` bullets, because `doccheck` reads
  them as identifiers.

Density item 2, derivative-free FTC in tail form (2026-11-02, done: milestones A and B, plus validation):
- **`Analysis/TailFTC` (3.1 s), `module AlgT A R`, over an abstract Archimedean ω-semiring:**
  - the dyadic pieces `Dy n a` (an inductive family: `dy0`, `dyL`, `dyR`);
  - the invariants `Up`/`Lo`, with `up-step`/`lo-step`;
  - `cancel≤P`, which cancels a term bounded by 2ᴷ by halving K times;
  - `squeeze`, `tele`, `tail-le`, `tail-eq`;
  - `exp-facts`/`exp-cert`, the pointwise exp algebra for certificates.
- **`Continuous/TailFTC` (4.7 s), `module Unit`:** `ftc-unit : ∫₀¹ h + G 1 ≈ G 0`.  Hypotheses:
  - `h` decreasing and bounded by 1, with one `Fun` for measurability;
  - `G` bounded by 2ᴷ on dyadic points;
  - the certificate on every dyadic piece `[a, a+½ⁿ]`:
    `G(a+½ⁿ) + ½ⁿ·h(a+½ⁿ) ≤ G a ≤ G(a+½ⁿ) + ½ⁿ·h a`.
  - Proof: induction on depth over all pieces at once, splitting off the first bit, then `squeeze` with `arch`.  It
    needs no explicit 2ⁿ sums and no measurability of rescaled functions.
- **`Continuous/TailFTCHalfLine` (5.2 s), `module Leb`:** the same certificate at every integer shift.
  - `leb-≤ : ∫ᴹ lebPre h ≤ G 0`, always.
  - `leb-≈`: equality, given the archimedean tail `∀ m → Σ N, G(N) ≤ ½ᵐ`.  Telescopes `ftc-unit` over `[n, n+1]`.
- **Validation:**
  - `Continuous/TailFTCExp` (5.3 s) re-derives `HalfLineUnit.I-negExp-unit`.
  - `Continuous/TailFTCExpHalf` (5.5 s) gives `∫-negExp : ∫₀^∞ e^{−x} ≈ 1`.
  - About 90 lines each, against `HalfLineUnit`, `HalfLineNorm` and `GeometricNorm` at roughly 700 lines together.
    The certificate is pure exp algebra (`1+w ≤ eʷ ≤ 1+w+w²`, `negExp-add`).
- **Agent's obstacles:**
  - An unresolved implicit `k` in `up-step` made Agda unify `P _k` on concrete cuts.  Fixed by passing `{k = suc K}`.
  - A `with` in a certificate lemma exhausted 3 GB.  Fixed by splitting it into two typed lemmas.
- **Not done:**
  - The increasing-`h` variant.
  - `h` bounded only by 1.  Larger integrands need scaling, or a version with `h ≤ 2ᴷ`.
  - The integration-by-parts variant.
- **Merge:** the branch was cut from `597bc3a`, so it lacked this plan section and `BetaIntegral` (it built its own
  `cancel≤P`).  I resolved the `Interface.md` and `Modules.md` conflicts myself.  `make check` (191 files),
  `longcheck` (35) and `doccheck` pass.
- **Next:** item 3 is now unblocked: `∫ xⁿ e^{−x} = n!` with `G(x) = e^{−x} ∑_{k≤n} n!/k! xᵏ`.  It needs `h` bounded
  by more than 1, or `h` split into pieces bounded by 1, and `xⁿe^{−x}` is not monotone on [0, n].  So it first needs
  the `h ≤ 2ᴷ` generalisation and piecewise monotonicity (split at an integer).

Decision-theoretic bridge, coin Bayes risk (2026-11-02, done):
- **`Inference/CoinBayesRisk` (10.2 s, 1.1 GB):** one flip with a uniform prior.  The joint is
  `joinPre (mapPre (θ ↦ σ(θ, coinKernel θ)) uniform)`.  The risk is `E-at joint` of the expanded signed test
  θ̂² − 2θθ̂ + θ², built from `+T`, `scaleT` and `⊗T`.  `E-joint` reduces g(θ)·h(X) to a uniform expectation.
  - `risk-X : six riskX ≃ 1S`: θ̂ = X has r = 1/6.
  - `risk-P : eighteen riskP ≃ 1S`: the posterior mean θ̂ = (X+1)/3 has r = 1/18.  This goes through `risk-P9`,
    the risk of 3θ̂ − 3θ.
  - `risk-X18 : eighteen riskX ≃ three`, for comparing the two side by side.
- **Cost trap:** the ring lemmas on the concrete `signedRing` never finished in 5 min.  The fix is an `abstract` copy
  of the signed operations (`_⊞_`, `_⊠_`, `⊟_`) packaged as `ring′ : CommutativeRing`.  The generic `Alg` runs over
  it, using `u = −1` as a solver variable, and the bridges `⊞-≃`/`⊠-≃` lead back.
- **Not done:**
  - an `≤` statement r(posterior mean) ≤ r(X);
  - a pointwise proof that the tests are (θ̂ − θ)²;
  - a general Bayes-optimality theorem.

Density item 3, all exponential moments (2026-11-02, done): `∫₀^∞ xⁿ e^{−x} dx = n!` and `E[Xⁿ] ≃ n!`.
- **Route change:** the planned `G = e^{−x} ∑ n!/k! xᵏ` failed.  At the extremum x = n of xⁿe^{−x} the certificate
  has only third-order slack, so first-order exp facts cannot prove it.  Instead:
  - **Lipschitz-tolerant FTC with integration by parts:** `∫h + G(b) ≈ G(a) + ∫k`.  The certificate holds up to
    `w²c` on each piece `[a, a+w]`, and `h` and `k` are Lipschitz, not monotone.  This covers increasing, decreasing
    and mixed shapes at once.
  - **Induction:** with `G = h = xʲ⁺¹e^{−x}` and `k = (j+1)xʲe^{−x}`, induct from `∫e^{−x} = 1`.
  - **Scaling:** `½ˢ` scaling handles integrands larger than 1.
  - **Frequent tail:** for every m and N₀ there is some N ≥ N₀ with `G(N) ≤ ½ᵐ`.  This is enough because the
    partial sums increase, and it avoids floor arithmetic.
- **Modules (my timings):**

  | Module | Time | Exports |
  |---|---|---|
  | `Analysis/TailFTCLip` | 3.5 s | `AlgL` |
  | `Continuous/TailFTCLip` | 6.8 s | `ftc-lip` |
  | `Continuous/TailFTCLipJ` | 6.5 s | `ftc-J`, for data bounded by 2ˢ |
  | `Continuous/TailFTCLipHalf` | 5.9 s | `glue : ∫ᴹ lebPre h ≈ ∫ᴹ lebPre k` |
  | `Analysis/PolyExpCert` | 5.9 s | polynomial × exp certificates |
  | `Analysis/ExpTail` | 3.2 s | the frequent tail |
  | `Continuous/HalfLineMomentN` | 9.9 s | `ibp-unit` |
  | `Continuous/HalfLineMomentFact` | 6.8 s | `moment-succ`, `∫ᴹ-pw-moment : ∫ xⁿe^{−x} ≈ fact n` |
  | `Inference/ExpMomentN` | 8.2 s | `E-atᴵ-powD n ≃ fact n` |

  `HalfLineMomentFact` also re-derives `∫-x` and `∫-x²` with the same statements as `HalfLineMean`/`HalfLineMoment2`.
  All modules are ≤ 1 GB.
- **Performance lessons:**
  - `with` on large certificate goals cost 2.5 GB.  Projections and top-level lemmas fixed it.
  - Instantiating `module L = LipJ …` with inline lambdas cost 20 s and 3.1 GB.  Naming each hypothesis with an
    explicit type brought it under 10 s.
- **Note:** the agent reports that `longdecls.py`'s own defaults (18 lines, 1000 chars, 130 cols) are stricter than
  the 25/1500/160 I have been putting in briefs.  The check `make longcheck` runs is what counts; it stays at 35.
- **Merge:** `make check` (201 files), `longcheck` (35) and `doccheck` pass.  The old bespoke modules
  `HalfLineMean`/`HalfLineMoment2`/`GeometricMoment2` are now redundant, and could be retired or kept as references.
- **Remaining items of the density list:** 4 (integrability by domination), 5 (function library), 6 (real line,
  symmetric densities, the Gaussian without π) and 7 (affine change of variables).  The Lipschitz FTC with
  integration by parts is exactly what item 6's Gaussian variance needs.

Density item 6, half-line part: Gaussian moments without π (2026-11-02, done).
- **Setting:** φ(x) = e^{−x²/2} on [0,∞), with normaliser `Z = ∫ᴹ lebPre phiH` left abstract (√(π/2) is out of scope).
- **Results:**
  - **`Continuous/GaussHalfLine` (8.9 s):** `phiH`, `gMomH i` (xⁱφ), `gKH j` ((j+1)xʲφ), and
    `AtInterval.ibp-unit` (integration by parts on each `[n₀, n₀+1]`, with G = xʲ⁺¹φ).
  - **`Continuous/GaussMoment` (6.2 s):**
    - `moment-succ : ∫ x^{j+2}φ ≈ (j+1)·∫ xʲφ`, via `TailFTCLipHalf.glue`;
    - `∫-x²φ : ∫ x²φ ≈ Z`;
    - `even-moment n : ∫ x^{2n}φ ≈ (2n−1)!!·Z`.
  - **`Continuous/GaussFinite` (6.1 s):** `Z-le : Z ≤ 4`, since each unit integral is at most Φ(n) ≤ 2·½ⁿ.
  - **`Continuous/GaussInverse` (7.7 s):** `finZ`, `posZ` (from Φ(1) ≥ ½), and `Z-inv : Σ n, Z·n ≈ 1`.
  - **`Inference/HalfNormal` (7.6 s):** `halfNormal = normPre (densW phiH) n _` and `E-atᴵ-hn : E[X²] ≃ 1`.  The
    canonical instance `HN` uses n = `invC Z`, so no hypotheses remain.
- **Supporting modules:** `Analysis/GaussCert` (`AlgG`, the polynomial × Gaussian certificates, with `pack` abstract),
  `Analysis/GaussExp`, `Analysis/CutSplit` (`split1`: x ≤ 1 or 1 ≤ x, by LEM) and `Analysis/GaussTail`.  All
  modules are ≤ 1 GB (my timings, at load ≈ 3.5).
- **Performance lessons:**
  - `AtInterval` first took 134–173 s.  Conversions through the module-applied `X.hh`/`X.kh` unfolded the cut `*`.
    Restating the pack facts at the local names (`pk j = X.pack j`) brought it to 10 s.  Making `pack` abstract
    alone did not help.
  - `with posOrZero Z` normalised `Z` and took minutes and 3.3 GB.  A helper function that pattern-matches,
    with no `with`, fixed it.
- **Merge:** `make check` (210 files), `longcheck` (35) and `doccheck` pass.
- **Still open for item 6:** the whole real line (a signed-reals QBS, Lebesgue measure on ℝ, the symmetry lemma), the
  Gaussian on ℝ with E[X] = 0 and Var = 1 by symmetry from these half-line moments, and `Z = √(π/2)`.

Density item 4, integrability by domination (2026-11-02, done).
- **`Inference/Domination` (7.4 s, 1.0 GB):**
  - finiteness transfer: `Bnd-≤`, `Bnd-add`, `Bnd-scale`, `J-Bnd-mono`, `ITest-dom`;
  - integral lemmas on `WQ` (none existed before): `∫ᴹ-mono`, `addH`, `∫ᴹ-scale`, `∫ᴹ-add`, `∫ᴹ-dom`,
    `∫ᴹ-Bnd-dom`;
  - for densities: `densI-dom`, an `ITest (densDist d nrm)` from `g± ≤ c·b` with `Bnd c` and `Bnd (∫ d·b)`.
    `E-atᴵ-dom` is the corresponding instance of `E-atᴵ-dens`.
- **`Inference/PolyDomination` (8.4 s, 1.16 GB):**
  - `expI k c …`: any `g±` with `g± ≤ c·(1 + xᵏ)` is integrable under the exponential (`expB k` gives `0! + k!`).
  - `HNDom`/`HNZ.hnI`: the same under `halfNormal`, for even degree `2m` (bound `Z + (2m−1)!!·Z`, scaled by `n`).
  - Validation: `powD-dom`/`E-atᴵ-powD-dom` re-derive `ExpMomentN.powD`, and `sqI-dom` re-derives
    `HalfNormal.sqI`.
- **Not done:** odd-degree growth under the half-normal.  The agent missed that `Analysis/CutSplit.split1`
  (x ≤ 1 or 1 ≤ x, by LEM, from the Gaussian work) gives the needed `xᵏ ≤ 1 + x^{2k}`.  A bound of even degree
  ≥ k works meanwhile.
- **Merge:** `make check` (212 files), `longcheck` (35) and `doccheck` pass.  Timings were taken at load ≈ 6.5, so
  they are approximate.
- **Remaining density items:** 5 (function library: much of it now exists, scattered over `PolyExpCert`,
  `GaussCert`, `Domination`, `ExpMomentN`), 6 (the whole real line) and 7 (affine change of variables).

Density item 6, the whole real line (2026-11-02, done for symmetric densities).
- **Representation:** `RQ = WQ +Q WQ` (the QBS coproduct), with `inl x` read as `+x` and `inr x` as `−x`.  0 occurs
  twice, which is harmless because only integrals against `lebR` are used.  This is not a signed-reals QBS with
  arithmetic: there is no addition on `RQ`, so item 7's translation is still unavailable.
- **`Continuous/RealLine`:** `lebR = sumPre tsR` (`lebPre` pushed along `inl` and `inr`, padded with zero
  measures), and `∫ᴹ-lebR`: an integral over ℝ splits into the two half-line integrals.
- **`Continuous/RealDensity`:** `copairH d e` densities, `lebR-sym` (total mass `c + c`), and `module Sym` with
  `symDist` and `∫-sym`/`J-sym`.
- **`Inference/SymExpectation`:** the symmetry lemma.  `E-atᴵ-sym` gives expectations under any symmetric density as
  half-line integrals, and `E-atᴵ-odd` gives `E[g] ≃ 0` for odd `g`, with no value for the normaliser.  The generic
  `E-atᴵ-≈` (expectation from `≈` of the parts) cut `E-atᴵ-sym` from 7.7 s to 0.5 s.
- **`Inference/GaussReal`:** `gaussR` (normaliser `(Z + Z)⁻¹` via `GaussInverse.Z-inv`), `E-atᴵ-X : E[X] ≃ 0`,
  `E-atᴵ-X² : E[X²] ≃ 1`, and `var-gaussR : Var X ≃ 1`.  Integrability of x uses `x ≤ 1 + x²` from
  `CutSplit.split1` with `Domination.∫ᴹ-mono`/`∫ᴹ-add`.
- **Timings** (mine, at load ≈ 6.5): RealLine 6.0 s, RealDensity 7.5 s, SymExpectation 8.0 s, GaussReal 12.5 s,
  all ≤ 1.05 GB.
- **Merge:** `make check` (216 files), `longcheck` (35) and `doccheck` pass.
- **Remaining density items:** 5 (function library), 7 (affine change of variables; needs scaling on `WQ` and, for
  N(μ, σ²), a translation on ℝ that this representation does not have), and `Z = √(2π)`.

Density item 7, scaling part: the exponential with a rate (2026-11-02, done for rational 0 < λ ≤ 1).
- **Rate representation:** a cut `l` with a hypothesised reciprocal `c` (`l * c ≈ 1#`, `l ≤ 1#`,
  `c ≤ natE (suc ν)`).  `Rat a b ab` is the instance (a+1)/(b+1), a ≤ b, from `ExpLower.qinvC`.  `e^{−λx}` is
  `negExp (l * x)`; no new analysis was needed.
- **Method:** the rate-1 certificates of `PolyExpCert.Ex.pack` are evaluated at λx with width λw and multiplied by
  `s·c`.  `cλ = 1` makes the main terms exact, and the error term `(s·λ)·2^S ≤ 2^W` needs λ ≤ 1.  Tails come from the
  rate-1 `Tail.tail` at `N = ν·N′`.  The algebra is abstract in `Analysis/ExpRate` (`AlgRate`) and
  `Analysis/ExpRateSigned`.
- **Results:**
  - `Continuous/ExpRateInt`: `∫-negExpR : ∫ e^{−λx} ≈ c`, so `λ·∫ e^{−λx} ≈ 1`.
  - `Continuous/ExpRateMoment`: `moment n : ∫ xⁿ e^{−λx} ≈ cⁿ⁺¹·n!` (integration by parts via
    `TailFTCLipHalf.Glue`).
  - `Inference/ExpRateDist`: `expDistλ`, `rate-moment n : E[Xⁿ]·λⁿ ≃ n!`, `mean-rate`, `second-rate`, and
    `var-rate : Var·λ² ≃ 1`.
- **Timings** (mine, at load ≈ 6): ExpRate 4.9 s, ExpRateSigned 3.0 s, HalfLineRate 6.4 s, ExpRateInt 8.6 s,
  ExpRateMoment 11.0 s (1.3 GB), ExpRateDist 13.9 s (2.1 GB, the largest memory of any recent module).
- **Performance lessons:** a single `refl` first took 33 s.  It was fixed by making the scaled functions plain
  definitions (`AlgRate.Fn`) that the tests use syntactically, and by passing the implicit arguments of `P-*`
  explicitly.  Proving the variance algebra on concrete cuts exhausted a 3 GB heap, so it moved to an abstract module.
- **Merge:** `make check` (222 files), `longcheck` (35) and `doccheck` pass.
- **Not done:**
  - λ > 1: done since; see the next note.
  - `densDist` at rate 1 compared with `expDist` (`≈ᵖ`).
  - Translation, which N(μ, σ²) needs.  `RQ` has no addition.

Density item 7, rates above 1 (2026-11-02, done).
- **Route:** the tail FTC fixes the mesh to dyadic pieces, so neither a finer mesh nor a `CutSplit` case split helps.
  The new abstract `Analysis/ExpRateExt` (`AlgExt`) passes certificates valid for widths t ≤ ½ᴷ to all t ≤ 1 by
  halving [a, a+t] K times; one halving adds errors as 4(½t)²E = t²E.  With l ≤ 2^(μ+1) and K = μ+1 the rate-1
  data is only used at width λt ≤ 1.
- **Interface change:** `Rate`, `Tl`, `Int`, `Mom` and `Dist` take `μ` and `lμ : l ≤ natE (suc μ)` in place of
  `l1 : l ≤ 1#`; the results keep their names and statements.  `Rat a b`/`DistRat a b` cover every positive
  rational (a+1)/(b+1), and `DistRat a 0` every positive integer.
- **Timings** (mine, at load ≈ 6): ExpRateExt 4.1 s, ExpRate 5.2 s, ExpRateInt 8.1 s, ExpRateMoment 11.8 s,
  ExpRateDist 14.7 s (2.0 GB).
- **Merge:** `make check` (223 files), `longcheck` (35) and `doccheck` pass.
- **Still open for item 7:** `expDistλ` at rate 1 against `expDist` (`≈ᵖ`), and translation (N(μ, σ²)).

Density follow-ups: odd-degree half-normal domination and rate-1 consistency (2026-11-02, done).
- **`Inference/PolyDominationOdd` (8.6 s, 1.16 GB):** `pw≤1+ev : xᵏ ≤ 1 + x^{2k}` on `WQ` via `CutSplit.split1`;
  `hnIk`, an `ITest halfNormal` for any `g± ≤ c·(1 + xᵏ)` with `k` arbitrary (reduces to `HNZ.hnI` at degree 2k);
  `xI`, the first moment.  The ring algebra is generic (`AlgO`).
- **`Inference/ExpRateOne` (12.2 s, 1.96 GB):** `expRate-one f : ∫ᴹ (ιPre expDistλ) f ≈ ∫ᴹ (ιPre expDist) f` for
  every `f`, with `expDistλ` at `l = c = 1#`.  Both sides reduce through `∫-dens`/`∫-expDist` to pointwise-equal
  densities; no uniqueness of measures was needed.  No `≈ᵖ` relation exists, so it is stated as equal integrals.
- **Merge:** `make check` (225 files), `longcheck` (35) and `doccheck` pass.  Timings mine, at load ≈ 5.7.
- **Not done:** the value of E[X] under the half-normal (`∫ x φ = 1`).  The Gauss packs only cover
  `G = x^{j+1}φ` with j ≥ 0; `G = φ` needs a new pack (Lipschitz bounds, certificates, tail).
- **Remaining density items:** 5 (a consolidated function library), translation on ℝ (for N(μ, σ²); `RQ` has no
  addition), the half-normal mean (done since; see the next note), and `Z = √(2π)`.

The half-normal mean and the Gaussian E|X| (2026-11-02, done).
- **Route:** `G = φ` is the j = −1 case of the Gauss packs, with `h = xφ` and `k = 0`, so the certificate is first
  order (no Bernstein bounds).  `TailFTCLipHalf.Glue` assumes `G 0 = 0`, which fails for φ, so the sum is handled
  directly: `∑_{n<N} aₙ + φ(N) ≈ φ(0) ≈ 1`, with `≥` from a far-out N where `φ(N) ≤ ½ᵐ` (`GaussTail.big`).
- **Modules** (timings mine, at load ≈ 6):
  - `Analysis/GaussCertM1` (3.4 s): abstract `AlgGM`, the first-order certificate.
  - `Continuous/GaussMeanUnit` (16.3 s, 1.0 GB): `AtInterval1.ibp-unit1`, reusing `GaussHalfLine.AtInterval`'s
    skeleton.
  - `Continuous/GaussMean` (7.2 s): `∫-xφ : ∫ xφ ≈ 1`.
  - `Inference/HalfNormalMean` (8.6 s): `E-atᴵ-xI : E[X] ≃ n` under `halfNormal` (n the canonical normaliser from
    `Z-inv`).
  - `Inference/GaussRealAbs` (8.8 s): `E-atᴵ-abs`, `Z2-abs : (Z+Z)·E|X| ≈ 2` under `gaussR`.
- **Merge:** `make check` (230 files), `longcheck` (35) and `doccheck` pass.
- **Notes:** `E[X] ≃ n` holds only for the canonical normaliser, because `PolyDominationOdd.xI` is built at
  `Z-inv`.  `PolyDominationOdd`'s header still calls the mean "not done".
- **Remaining density items:** 5 (a consolidated function library), translation on ℝ (N(μ, σ²)), and
  `Z = √(2π)`.

## Revised direction for continuous expectations (2026-11-02)

The generic machinery is in place: expectations under a density (`densDist`, `∫-dens`), integrability by domination,
the symmetry lemma, and the tail FTC (`TailFTCLip`/`LipJ`/`LipHalf`).  What has been repeated, at 300–1000 lines a
time, is proving the tail FTC's hypotheses for each concrete integrand: Lipschitz bounds for `h`, `k` and the
certificate `G b + w h(a) ≤ G a + w k(a) + w² c` (and its reverse), i.e. `G′ = k − h`, in packs such as `PolyExpCert`,
`GaussCert`, `GaussCertM1` and the halving in `ExpRateExt`.  Lower reals have no derivative, so nothing composes.  Two
changes replace items 5 and 7 and the translation item.

A. **Certificate calculus** (replaces item 5).
   - One notion, `Deriv G h k`: on every dyadic piece of [0,1] (or of [n, n+1]) the certificate holds with some
     constant, h and k are Lipschitz, and all are bounded (the data `LipJ` needs).  The derivative is signed, as the
     formal difference `k − h` of non-negative parts.
   - Closure rules, each proved once over an abstract Archimedean ω-semiring:
     sums (`(G₁ + G₂)′`), scalar multiples, products (product rule: `k = k₁G₂ + G₁k₂`, `h = h₁G₂ + G₁h₂`),
     composition with an affine or monotone map (chain rule), and translation `x ↦ n + x` (to pass from [0,1] to
     [n, n+1]).
   - Base cases: constants, `x` (hence `xⁿ` by the product rule), `e^{−x}`; then `e^{−x²/2}` by the chain rule.
   - A bridge from `Deriv` to `LipJ`/`Glue` hypotheses, so integration by parts on the half-line is "build `Deriv`
     by the rules, apply the FTC".
   - Validation: re-derive a few existing results (`∫ xⁿe^{−x} ≈ n!`, `∫ xφ ≈ 1`, `∫ x²φ ≈ Z`) from the calculus.
     Keep the existing concrete modules as checks.
   - Measurability (`Hom`/`Meas`) of products and compositions is separate and largely exists; collect it alongside.

B. **Families as pushforwards** (replaces item 7 and translation on ℝ).
   - In a QBS a random variable is a map, and `E_{f∗μ}[g] = E_μ[g ∘ f]` holds generically (`mapM`).  Define
     Exp(λ) as the pushforward of Exp(1) under `x ↦ x/λ`, and N(μ, σ²) as the pushforward of N(0,1) under
     `x ↦ μ + σx`; moments then follow from the standard ones by linearity, with no new integrals.
   - N(μ, σ²) needs only the affine map into a signed codomain, not addition on `RQ`.
   - Densities stay necessary for conditioning (`score`) and Bayes.  One change-of-variables theorem (scaling and
     translation of Lebesgue measure, proved through A by matching antiderivatives) links the pushforward families to
     their densities, once, generically.
   - Validation: the pushforward Exp(λ) agrees with `ExpRateDist.expDistλ` (equal integrals for all tests).

C. **Unchanged:** `Z = √(2π)` stays a separate, large item that no moment result needs.

Order: A first (B's change-of-variables theorem uses it); B's moment part needs only `mapM` and could run in
parallel, but run one agent at a time while the machine is loaded.

Revised item A, the certificate calculus (2026-11-02, done except the chain rule).
- **Design (`Analysis/Deriv`, `AlgD`):** `D M c G h k` (G′ = k − h on [0, M]) is stated per point pair (a, a+w),
  a + w ≤ M, w ≤ 1: bounds `G, h, k ≤ c`, Lipschitz `h`, `k` with constant `c` (both ways), and the two-sided
  certificate `G(a+w) + w·h a ≤ G a + w·k a + w²c` and converse.  The Lipschitz bound of `G` is derived (`Gup`/`Gdn`).
  `Deriv M G h k = Σ c (c ≤ 2ˢ × D M c G h k)` hides the constant.
- **Rules:** `DFconst`, `DFid`, `DFsum`, `DFscale`, `DFshift` (x ↦ t + x), `DFaff` (x ↦ l·x, l ≤ 1), `DFresp`,
  `Dmono`; `DFprod` (`Analysis/DerivProd`): multiply the two certificates directly and move the cross terms back to a
  by `Gup`/`Gdn`, error about 10c², no cancellation.
- **Bases (`Analysis/DerivExp`):** `DE` for e^{−x} (reusing `PolyExpCert` facts), `pwD` for xⁱ, and
  `xjE : Deriv M (xʲ⁺¹e^{−x}) (xʲ⁺¹e^{−x}) ((j+1)xʲe^{−x})`, which is what `PolyExpCert.Ex.pack` supplied by hand.
- **Bridge (`Continuous/DerivBridge`):** `Unit.ftc-unit` (Deriv on [0,1] to `J h + G 1 ≈ G 0 + J k` via `LipJ`),
  `OnHalfLine.unit` (shift to [n, n+1]), `glue-D` (via `Glue`, G 0 = 0) and `glue-D0 : ∫ h ≈ G 0 + ∫ k` with no
  G 0 = 0 hypothesis.  Measurability is still passed in as parameters.
- **Validation (`Continuous/DerivMoment`):** `∫-moment : ∫ xⁿe^{−x} ≈ n!` re-derived in about 60 lines, replacing
  the `PolyExpCert` pack and the hand-written interval shifting.
- **Timings** (mine, at load ≈ 6): Deriv 4.3 s, DerivProd 4.4 s, DerivExp 3.2 s, DerivBridge 8.2 s (1.1 GB),
  DerivMoment 6.7 s.
- **Merge:** `make check` (235 files), `longcheck` (35) and `doccheck` pass.
- **Not done:**
  - The chain rule (done since for e^{−u}; see the next note).  A general monotone inner function does not fall out; the useful special case is e^{−u} for a
    `Deriv` inner u (h = E(u)·k_u, k = E(u)·h_u), which needs a signed-increment form of the e^{−x} facts.  It would
    give the Gaussian integrals (`∫ xφ`, `∫ x²φ`) from the calculus.
  - `DFaff` only for l ≤ 1 (l > 1 by composing with the halving of `ExpRateExt`, or by shrinking the width).
  - Measurability rules for products and compositions.
  - Item B (pushforward families, change of variables).

Revised item A, the exponential chain rule (2026-11-02, done).  Item A is now complete.
- **`Analysis/DerivChain` (`AlgDX`, 4.5 s):** `DFexp : Deriv M u h k → Deriv M (E ∘ u) (E(u)·k) (E(u)·h)`, i.e.
  (e^{−u})′ = −e^{−u}·u′, with constant `Cx c` depending only on u's constant.  No signed increments were needed:
  the exponential facts are taken at a bound `B ≥ 3c` covering every sum, and the two certificates close with errors
  w²(c² + c + 4c²) and w²(c + 2c²).  Lipschitz bounds reuse `DerivProd.lipP`.
- **`Analysis/DerivGauss` (3.0 s):** `DFquad` (x²/2 by the product rule and `half`), `DFgauss` (φ, h = xφ, k = 0),
  `DFgauss1` (xφ, h = x²φ, k = φ).
- **`Continuous/DerivGaussMoment` (7.0 s, 0.91 GB):** `∫-xφ : ∫ xφ ≈ 1` and `∫-x²φ : ∫ x²φ ≈ Z`, re-derived from
  the calculus through `glue-D0`, matching `GaussMean` and `GaussMoment`.
- **Merge:** `make check` (238 files), `longcheck` (35) and `doccheck` pass.  Timings mine, at load ≈ 6.
- **Left from A:** `DFaff` for l > 1; measurability rules for products and compositions (still passed to the bridge).
- **Next:** item B (families as pushforwards; one change-of-variables theorem through A).

Revised item B, families as pushforwards (2026-11-02, done except the change of variables).
- **Pushforward expectation:** the generic lemmas existed (`SFinite.∫ᴹ-map`, `Monad.∫-map`,
  `ExpectationInt.E-atᴵ-map`).  New in `Inference/PushforwardExpectation` (5.3 s): `pushI`/`E-atᴵ-push` (an
  `ITest` of the pushforward from one of the composites, same expectation) and `constI`/`E-atᴵ-const`.
- **`Inference/ExpPushforward` (7.7 s, 1.05 GB):** `expPush = mapPre (scaleH c idW) expDist` for any finite `c`
  (no positivity, rationality or reciprocal).  `E-atᴵ-powPush n : E[Xⁿ] ≃ cⁿ·n!` from the Exp(1) moments with no new
  integral; `mean-push`, `second-push`, `var-push : Var ≃ c²`; with `l * c ≈ 1`, `mean-rate`/`var-rate` as in
  `ExpRateDist`.  This supersedes the density route of `ExpRate*` for moments (≈ 1000 lines there).
- **`Inference/GaussAffine` (8.3 s, 1.17 GB):** N(μ, σ²) as the statistic `μ + σX` of `gaussR` (`affI`; μ, σ signed),
  not as a `Pre` on a new codomain: `E-atᴵ-affI : E[μ + σX] ≃ μ`, `var-affI : Var ≃ σ²`.  Algebra generic in
  `Analysis/AffineAlg` (3.0 s).
- **Merge:** `make check` (242 files), `longcheck` (35) and `doccheck` pass.  Timings mine, at load ≈ 5.
- **Change of variables (not done; findings):**
  - Dyadic scaling `∫ f(2x) dλ = ½ ∫ f dλ` looks structural.  It needs a first-bit split of the fair coin,
    `J fairCoin h = ½ Σ_b J (h (b ∷ ·))`, and a reindexing of `∑ᶠ` over ℕ × Bool ≅ ℕ; neither exists yet.
  - General c needs a uniqueness principle for measures on `WQ` (agreement on intervals ⇒ equal integrals; a π–λ or
    monotone-class argument).  `Analysis/Uniqueness` covers only probability measures on the coin space agreeing on
    cylinders; transporting it to `WQ` through the binary expansion may be the route.
  - Until then, densities and pushforwards agree only where checked directly (`ExpRateOne` at rate 1).
- **Left:** the change-of-variables theorem (above); a `Pre` for N(μ, σ²) on a signed codomain; from item A,
  measurability rules and `DFaff` for l > 1.

Change of variables, dyadic scaling (2026-11-02, done).
- **Lemma 1 already existed** for bounded tests (`Continuous/FirstBit.firstBit-fun`); `Continuous/FirstBitInf`
  (4.3 s) extends it to unbounded `Meas` tests via truncations and `⨆-mix`: `firstBit-J`.
- **`Analysis/DyadicAlg` (2.9 s, generic):** `∑ᶠ-dbl : ∑ᶠ a ≈ ∑ᶠ n. (a (2n) + a (2n+1))`, `⨆-mix`, `cons-alg`,
  `tw k = 2ᵏ` with `tw-hp`.
- **`Continuous/HalfLineScale` (6.9 s, 1.05 GB):** for every test `h`, `∫-dbl : ∫ h(2x) ≈ ½·∫ h`,
  `∫-half : ∫ h(x/2) ≈ 2·∫ h`, `∫-tw′ k : 2ᵏ·∫ h(2ᵏx) ≈ ∫ h`.
- **`Inference/ExpPushforwardAgree` (7.8 s, 1.08 GB):** `agree f`: the pushforward `expPush` at c = ½ and
  `densDist (2e^{−2x})` have equal integrals for every test; the first density/pushforward agreement beyond rate 1,
  for all tests, with no certificate calculus.
- **Merge:** `make check` (246 files), `longcheck` (35) and `doccheck` pass.  Timings mine, at load ≈ 5.5.
- **Left for the general theorem:**
  - general c: a uniqueness principle on `WQ` (agreement on intervals ⇒ equal integrals), e.g. `Analysis/Uniqueness`
    transported along `expansion`; dyadic c avoided it because coin cylinders are dyadic intervals;
  - translation `x ↦ x + t` (integer t is `shiftPre`; general t needs additive structure or uniqueness);
  - the N(μ, σ²) `Pre` on a signed codomain; measurability rules; `DFaff` for l > 1.

Change of variables, general c (2026-11-02, investigated; not attempted).
- **Route via step functions fails:** sups of dyadic step functions reach only lower-semicontinuous tests, and `J` is
  `Iinf` over truncations, not a sup over step functions; even a step test needs `∫ 1[0,t] ≈ t` for non-dyadic t.
- **Uniqueness on `WQ` is unavailable:** there is no Borel structure on `WQ` (only on Cantor space); tests are
  measurable only through probes, so every comparison is of `J fairCoin (h ∘ φ)` for two probes, and needs a
  measurable `T : Cantor → Cantor` realising the scaling plus its law under the fair coin (`Analysis/Uniqueness`).
- **Rational c = p/q would need:** a digit transducer for u ↦ u/q (no inverse of `expansion` or digit extraction
  exists), its cylinder laws by counting, `Uniqueness` on Cantor space, and gluing the p/q pieces with `shiftPre`;
  estimated ≥ 1500 lines.  Irrational c needs a further idea (h(cx) is not monotone in c, so `J-⨆` along rationals
  does not apply).
- **Reachable smaller piece:** the law of `expansion` under the fair coin, `fair{expansion r ≤ t} = t` for every cut t.
- **Decision:** general c is deferred.  Dyadic rates use `HalfLineScale`; for other rates, compare moments through
  `ExpPushforward.E-atᴵ-powPush`, which needs no change of variables.

## Uniqueness on the half-line (planned 2026-11-02; skeleton first, then agents)

Goal: one general theorem, **measures on `WQ` that agree on dyadic intervals agree on every test**. Scaling,
translation, monotone change of variables and density identification then each reduce to a check on intervals.
Literature and route: `docs/UniquenessLit.md`. The theorem replaces the deferred general-c route above.

**Skeleton workflow.**
- I write every module below on an integration branch `uniq`. Each gets its header, imports and the statements
  listed, with `?` for every proof. Named intermediate lemmas are top-level declarations, so no hole hides a big step
  (as in the s-finite skeleton, `TODO.md` audit).
- `make progress` checks the skeleton (`scripts/progress-overlay.py`). Strict `make check` would fail on it, so main
  stays hole-free: agents branch from `uniq`, I merge their work into `uniq`, and `uniq` merges into main when it has
  no holes (or module by module, as each becomes hole-free together with its imports).
- An agent may add lemmas and helper modules, and may change a statement only after reporting why. The top-level
  statements are the contract.

**Modules (skeleton written 2026-11-02 on branch `uniq`; holes per module in brackets).**  The headers state the route;
the top-level statements are the contract.
1. `Borel/Cells` [done]: `Blk k`, `Cell k w`, `Top`, `words n`; `cylBlk`, `cylCell`, `borelTop`; disjointness
   (`blk-unique`, `top-blk`, `cell-unique`), `cell-words`, and `cyl-refine` (every cylinder is decided on the cells of
   some depth inside a block).  Combinatorics only, no `lem`.
2. `Analysis/UniquenessWeighted` [done]: the weighted pushforward `Jw m mw mx g mg = ∫ w(r) · g(x r) dm`;
   `wM` (mass ≤ 1 gives a `Measure`), `I-wM`; `uniqW-le1`, `uniqW-fun`, `uniqW` (equal finite mass and agreement on
   cylinders give agreement on every `Meas` g).
3. `Continuous/Intervals` [done]: `Ge` (the order of cuts at level `Set`), `InIv`, `InInf`, `ge-borel`; the tests
   `χIv a b`, `χInf` with their `-in`/`-out` laws; `dy n m = m·½ⁿ`, `χI n m`, `χI-split`.
4. `Continuous/UniquenessR` [done]: `χR` (indicator test of a Borel set of `ℛ = Probes.ℛQ S`), `χR-pt`, `onTop`,
   `onBlk`, `∫ᴹ-split`; under `agreeCell`, `finBlk`, `agreeTop`: `agree-blkCyl`, `agree-blk`, `agree-top`,
   `uniqR : μ ≈ᴹ ν`.
5. `Continuous/DigitCode` [done]: `val`, `digits`, `digits-cong`, `meas-digits`, `code : Hom S WQ ℛ`,
   `code-pt`, `decode : Hom S ℛ WQ`, `decode-code`, `code-cell`, `code-top`.
6. `Continuous/UniquenessWQ` [done, headline]: `test-factor`, `pushCell`, `pushBlk`, `pushTop`; under `agreeI`, `finI`,
   `agreeInf`: `uniqPush`, `uniqWQ : μ ≈ᴹ ν`.
7. `Continuous/LebesgueDyadic` [done]: `fair-top`, `cell-in`, `cell-out` (law of `j + expansion r` on dyadic intervals),
   `leb-χI`, `leb-inf`, `leb-fin`.
8. `Continuous/LebesgueInterval` [done]: `leb-Iv : a + ∫ lebPre χ[a,b) ≈ b`; `leb-unique` (interval masses
   characterise Lebesgue measure).
9. `Continuous/LebesgueScale` [done]: `scaledLeb`, `∫ᴹ-scaledLeb`, `scaled-Iv`, `∫-scale : c · ∫ h(cx) ≈ ∫ h`.
10. `Continuous/LebesgueShift` [done]: `shiftH`, `shiftedLeb`, `∫ᴹ-shiftedLeb`, `shifted-Iv`,
    `∫-shift : ∫ h(x+t) + ∫_{[0,t)} h ≈ ∫ h`.
- Monotone change of variables and every-rate agreement: stated in "Change of variables" below.

**Outcome: `Continuous/DigitCode` (2026-11-02, merged into `uniq`).**
- All 9 holes filled; contract unchanged (`val` is now an alias of `DigitStream.val`).  No new statements were needed
  in `Intervals` or `Cells`.
- Route: a digit machine with states `un j` (unary part) and `fr d m` (x ∈ [m/2ᵈ, (m+1)/2ᵈ)) decides one threshold
  `Ge thr x` per bit by excluded middle.  So `meas-digits` is induction on the position, each step a Boolean
  combination of `ge-borel` sets.  `decode` is the run length plus the expansion of the rest, via `lead`.
  `decode-code` needed no "sup of dyadic truncations" lemma, only `below-dec`, `arch` and `nat-big`.
- New helpers: `Analysis/DigitAlg` (4.1 s, 0.45 GB), `Continuous/DigitCut` (5.8 s, 0.64 GB),
  `Continuous/DigitStream` (7.3 s, 0.68 GB), `Continuous/DigitDecode` (6.4 s, 0.70 GB).  `DigitCode` itself:
  6.2 s, 0.69 GB.  Timings mine, through the progress overlay.

**Outcome: `Borel/Cells` and `Continuous/Intervals` (2026-11-03, two agents in parallel, merged into `uniq`).**
- All holes filled in both, contracts unchanged, no new modules.
- `Cells`: no excluded middle.  `cyl-refine` takes the finite support of the cylinder (`cyl-fin`), decides it at a
  canonical point of each cell (`dec-cyl`, by `Bool`) and transfers the answer to the whole cell.
- `Intervals`: one helper `indH` builds a test from a Borel predicate; `ge-borel` is an intersection over the
  rationals; `χI-split` via `split-iv` and the halving of dyadic points from `DigitAlg`.
- The cleanup of the Digit modules (long declarations) is also merged; the helper `ur` was renamed `unRun`.
- Timings (measurement agent, two runs, load ≈ 3.7): `Cells` 3.9 s, 0.54 GB; `Intervals` 4.8 s, 0.69 GB; `DigitAlg`
  3.1 s, 0.45 GB; `DigitCut` 4.6 s, 0.67 GB; `DigitStream` 6.6 s, 0.85 GB; `DigitDecode` 6.4 s, 0.82 GB;
  `DigitCode` 6.2 s, 0.90 GB.

**Outcome: `Analysis/UniquenessWeighted` and `Continuous/LebesgueDyadic` (2026-11-03, two agents in parallel, merged).**
- All holes filled in both, contracts unchanged.
- `UniquenessWeighted`: `wM` is the pushforward of a density measure (`Density.densM`); finite mass is scaled by `hp N`
  and unscaled by `pw N` (no additive cancellation); `uniqW` via `Density.Approx` truncations and `⨆-cong`.
- `LebesgueDyadic`: `fair-top` by induction with `FirstBit` (no cylinders) and `Arch.arch`; `cell-in`/`cell-out` by
  induction on n with the first-bit step `χI (n+1) m (shiftPt j (b∷r)) ≈ χI n m (shiftPt (2j+b) r)`; the cell
  `[j+1, j+2)` meets `j + expansion r` only at the all-true point.  New helpers `LebesgueDyadicAlg` (cut facts) and
  `LebesgueDyadicNat` (ℕ arithmetic).
- Lesson (agent report): a `with` on a term mentioning cuts, and unannotated binders or `_` arguments to `χIv-in`/`-out`,
  blew the 3 GB heap; use helper lemmas with projections and explicit arguments.
- Timings (measurement agent, two runs, load ≈ 4): `UniquenessWeighted` 5.5 s, 0.72 GB; `LebesgueDyadicNat` 3.0 s,
  0.44 GB; `LebesgueDyadicAlg` 6.4 s, 0.87 GB; `LebesgueDyadic` 7.6 s, 1.00 GB.

**Outcome: `Continuous/UniquenessR` (2026-11-03, merged into `uniq`).**
- All 7 holes filled, contract unchanged, no new modules (325 lines).
- `χR` is `Probes.probe` of `χ U`; `∫ᴹ-split` pointwise (`top-or-blk` via `Borel/Lead`) then `J-add`, `JSum.J-∑`;
  `agree-blkCyl` sums cells of depth n by a recursive `sumW` (no word lists); `agree-blk` is `uniqW` on the weighted
  pushforward with weight `w·χBlk`, with equal masses from `agree-blkCyl k cylTop`; `agree-top` via
  `∫ᴹ p (onTop g) ≈ g(all-true) * ∫ᴹ p χTop`.
- The agent used the agda MCP (`agda_load_and_goals`, 1–2 s per reload, precise errors), but wrote proofs directly
  rather than through hole actions.
- Timing (measurement agent, two runs, load ≈ 5): 7.8 s, 0.92 GB.

**Outcome: `Continuous/UniquenessWQ` (2026-11-03, merged into `uniq`): the headline theorem is proved.**
- All 6 holes filled, contract unchanged, no new lemmas.  `pushBlk` reads `Blk k` as `Cell k []` and transports the
  index along `k * 2 ^ 0 + 0 ≡ k`; `finBlk` transports `Bnd` along `pushBlk` with `≤-resp`.
- Timing (measurement agent, two runs, load ≈ 4): 7.0 s, 0.91 GB.

**Outcome: `Continuous/LebesgueInterval` (2026-11-03, merged into `uniq`).**
- Both holes filled, contract unchanged.  New helper `LebesgueIntervalAlg`, generic in a pre-measure whose dyadic
  cells have mass ½ⁿ: `F b = ∫ χ[0,b)` is monotone, `F (m/2ⁿ) ≈ m/2ⁿ` by induction on m, and `F b ≈ b` for bounded b
  from the dyadic points either side of b with `arch`, so no monotone convergence was needed.  `leb-unique` is
  `uniqWQ` with the left endpoint cancelled by `cancel-bnd`.
- Timings (measurement agent, two runs, load ≈ 4): `LebesgueIntervalAlg` 7.0 s, 1.00 GB; `LebesgueInterval` 7.5 s,
  1.04 GB.

**Outcome: `Continuous/LebesgueScale` and `Continuous/LebesgueShift` (2026-11-03, two agents in parallel, merged).
`uniq` has no holes left.**
- All holes filled in both, contracts unchanged.
- `LebesgueScale`: `scaledLeb c = scalePre c (mapM (scaleH c idW) lebPre)`; helper `LebesgueScaleAlg` (`Ge a (c·x)` iff
  `Ge (a·c′) x`, `χIv-scale`, `χInf-scale`).
- `LebesgueShift`: `shiftedLeb t` is a `sumPre` padded with zero-weight terms (no binary sum in `SFinite`); the interval
  law reduces to masses of [0,b) (`Iv-from-F`), split by the classical totality of cuts.  The library had no cut
  difference, so `LebesgueShiftCut` builds `diffC t b` with `t ⊕ diffC ≋ b` for t bounded by a rational, and
  `diff-⇐ : b ⊑ x ⊕ t → diffC ⊑ x` (no cancellation, x may be ∞).  Helper `LebesgueShiftAlg`.
- Lesson: implicit arguments of lemmas about `Ge` or `mk⊑` do not unify (membership is not injective); make them
  explicit.
- Timings (measurement agent, two runs, load ≈ 4): `LebesgueScaleAlg` 6.2 s, 0.82 GB; `LebesgueScale` 9.1 s, 1.21 GB;
  `LebesgueShiftCut` 3.3 s, 0.48 GB; `LebesgueShiftAlg` 7.0 s, 1.00 GB; `LebesgueShift` 9.7 s, 1.40 GB (closest to
  the 1.5 GB line).

**Order of agents (one at a time).**
- 1, 2 and 3 are independent and small.
- 5 is the riskiest, so it goes early to test the design.
- Then 4, 6 and 7.
- 8–10 last.
- Estimated sizes: 1 ≈ 200 lines, 2 ≈ 300, 3 ≈ 200, 4 ≈ 400, 5 ≈ 500–800, 6 ≈ 200, 7 ≈ 300, 8–10 ≈ 150 each.

**Risks, as settled by the skeleton.**
- Settled: `mapM` is generic in `X : QBS S`, with `∫ᴹ-map : ∫ᴹ (mapM f p) h ≈ ∫ᴹ p (h ∘ f)`.
- Settled: `Hom S ℛQ WQ` is exactly `Meas` (`Probes.probe`/`unprobe`), so `decode` and `h ∘ decode` are tests.
- Settled: the order of cuts `_≤_` lives in `Set₁`, but Borel predicates live in `Set`.  `Intervals.Ge` restates
  `a ≤ x` as `∀ q → mem a q → mem x q`.
- Settled: cylinders constrain arbitrary bits.  `UniquenessR` assumes agreement on cells only and derives it for
  cylinders inside a block (`Cells.cyl-refine`).
- Settled: mass at ∞ is handled by `agreeInf`/`agreeTop`.
- Settled (DigitCode outcome): `digits` respects `≈` of cuts (`digits-cong`) and is measurable (`meas-digits`).
- Performance: concrete cut arithmetic only in leaf modules, solvers in generic `Alg` modules, as before.

## Change of variables (planned 2026-11-03; skeleton first, then agents; branch `cov`)

Goal: substitution for every increasing bijection with a derivative certificate, and the density/pushforward agreement
for every scale, both from the uniqueness tools above rather than integrand-specific estimates.

**Route.**
- Change of variables works on the source side, which avoids an FTC at arbitrary points.  For φ with inverse ψ,
  compare `lebψ = mapM ψ lebPre` with `lebφ′ = reweightPre φ′ lebPre` by `UniquenessWQ.uniqWQ`.
  - On a dyadic interval [d, d′), `lebψ` gives φ d′ − φ d: pull back by ψ (`χIv-ψ`) to [φ d, φ d′), then `leb-Iv`.
    The arbitrary endpoints φ d are exactly what `leb-Iv` handles.
  - `lebφ′` gives the same by the FTC at dyadic points only (`FTCDyadic.ftc-dy` with h = 0).
  - Cancel the finite φ d.
- `ftc-dy` rescales: G(t/2ⁿ) has `Deriv` data by `DFaff` (slope ½ⁿ ≤ 1), so `DerivBridge.OnHalfLine.unit m` gives
  [m, m+1) for it; `piece` converts the fair-coin integral to `χ[m, m+1)` (null set: the all-true point), and `resc`
  moves back to [m/2ⁿ, (m+1)/2ⁿ) by `∫-scale` at 2ⁿ.
- Every-rate agreement is `∫-scale` for the test y ↦ l g(l y) f(y), for any normalised density g; Exp is g = e^{−x}.

**Modules (skeleton on `cov`).**
11. `Continuous/FTCDyadic` [done]: `hp-inv`, `hp-dy`, `rescH`, `piece`, `resc`, `dv-resc`, `ftc-dy`.
12. `Continuous/ChangeOfVariables` [done] (imports 11): hypotheses `dv`, `gc-to`, `gc-from`, `φψ`, `ψ-fin`; `Φ-mono`,
    `Φ-zero`, `Φ-fin`, `χIv-ψ`, `χInf-ψ`, `lebψ`, `lebφ′`, `massψ`, `massφ′`, `agreeI`, `finI`, `inf-ψ`, `inf-φ′`,
    `push-eq`, `cov-inv : ∫ h(ψ y) dy ≈ ∫ h φ′`, `cov : ∫ g(φ x) φ′(x) dx ≈ ∫ g`.
13. `Inference/ScaleDensity` [done] (independent of 11–12): `scD g = l g(l ·)`, `scD-pt`, `nrm-sc`, `push-dens`
    (pushforward of `densDist g` by x ↦ c x is `densDist (scD g)`), `densR`, `∫-negExpR`, `nrmR`, `scD-negExp`,
    `agree` (Exp(c) pushforward ≈ density λ e^{−λx}), `agree-dist` (against `ExpRateDist.Dist.expDistλ`).

**Outcome (2026-11-03, merged into `cov`; no holes, contracts unchanged).**
- `ScaleDensity`: `push-dens` is `ι-nat`/`∫ᴹ-map`/`∫-dens` then `∫-scale c l`; `∫-negExpR` from `∫-scale l c` on e^{−x};
  `scD-negExp` is `refl`.  No helper module.
- `FTCDyadic`: helper `FTCDyadicPiece` proves `piece` with `null-le` (F ≤ F′ off the all-true point, F constant there,
  possibly ∞ ⇒ J F ≤ J F′, from F ≤ F′ + c·χ_Top and `fair-top`), so neither monotone convergence nor the j = 0
  fallback was needed.  The two `hp`s are definitionally equal (`hp-dy` is `*-comm`).
- `ChangeOfVariables`: helper `ChangeOfVariablesAlg` (`inf-bnd`/`bnd-notinf` by excluded middle; `module Pull` with
  `χIv-pull`, `χInf-pull`; `inf-null : ∫ lebPre (f · χInf) ≈ 0` for every f, even f(∞) = ∞).  `agreeI` cancels with
  `cancel-bnd` as in `leb-unique`.
- Lessons: `hp 0` is not definitionally `1#` (`hp-zero`); `with <-cmp i j` on a goal mentioning
  `map (χI 0 j) ⟨$⟩ shiftPt i r` hangs Agda; pass the comparison to a helper instead.
- Timings (measurement agent, two runs, load ≈ 5): `ScaleDensity` 10.6 s, 1.44 GB (closest to the 1.5 GB line);
  `FTCDyadicPiece` 7.4 s, 1.02 GB; `FTCDyadic` 9.5 s, 1.22 GB; `ChangeOfVariablesAlg` 7.5 s, 1.06 GB;
  `ChangeOfVariables` 9.6 s, 1.24 GB.

**Order of agents.** 13 and 11 are independent and can run in parallel; 12 after 11.  Estimated sizes: 11 ≈ 300
lines (`piece` is the riskiest), 12 ≈ 300, 13 ≈ 150.

**Risks.**
- `piece`: `χ[j, j+1)(j + expansion r)` fails only at the all-true r; f may be ∞ there, so the null set must be handled
  by `fair-top` with monotone convergence, not by a bound on f.  Fallback: prove it for j = 0 and move by `∫-shift`.
- Two `hp`s: `FTCDyadic` uses `Arch R`'s, `Intervals.dy` uses `Half`'s; `hp-dy` is where they meet.
- `gc-to`/`gc-from` are stated with `_≤_` (`Set₁`); `χIv-ψ` needs them at `Ge`, as in `LebesgueScaleAlg`.

## Tests from function properties, and the real line (planned 2026-11-03; skeleton first, then agents; branch `rq`)

Goal: stop proving measurability by hand.  A function on the cuts that is monotone, or locally Lipschitz, or carries
`Deriv` data, is a test automatically; change of variables then takes plain functions.  On the whole real line
`RQ = WQ +Q WQ`: uniqueness from the two halves, scaling and reflection, and N(0, s²) as a pushforward of `gaussR`.

**Route.**
- Monotone F: the threshold set {x | q ∈ F x} is an up-set (down-set), so with excluded middle it is a countable union
  of {x ≥ d} for rationals d (`Intervals.ge-borel`), plus possibly the single point inf U.
- Locally Lipschitz F: q ∈ F x on [0, N+1] iff some dyadic cell ∋ x has q + c/2ⁿ ∈ F(m/2ⁿ); countable union of cells
  intersected with decided conditions, plus {∞}.  `Deriv` data gives local Lipschitz bounds for G, h, k
  (`Ct1`/`Ct2`, `LpU`/`LpD`).
- RQ: a measure is determined by its halves `restrL`/`restrR` (reweight by the summand indicator, fold onto WQ),
  because every test is the sum of its halves (`∫-split`).  `lebR-unique` reduces to `leb-unique` on each half.
- Scaling on RQ is `∫-scale` on each half; N(0, s²) integrates like the symmetric density `scD phiH` (`push-sym`).

**Modules (skeleton on `rq`).**
14. `Continuous/MonoTest` [done]: `Meas-mono`, `monoH F cF mF`, `Meas-anti`, `antiH`.
15. `Continuous/LipTest` [done]: `LocLip`, `Meas-lip`, `lipH`; from `dv : ∀ N → Deriv (N+1) G h k`: `deriv-cgG/h/k`,
    `deriv-lipG/h/k`, `derivH`, `liphH`, `lipkH`.
16. `Continuous/ChangeOfVariablesFn` [done] (imports 14, 15, `ChangeOfVariables`): functions Φ, Ψ, k with the hypotheses of
    `ChangeOfVariables`; `Ψ-mono`, `Ψ-cong`, `φH`, `ψH`, `φ′H`, `covF-inv`, `covF`.
17. `Continuous/UniquenessRQ` [done]: `foldH`, `oneL`, `oneR`, `restrL`, `restrR`, `∫-restrL`, `∫-restrR`, `∫-split`,
    `uniqRQ`, `restrL-lebR`, `restrR-lebR`, `lebR-unique`.
18. `Continuous/RealScale` [done]: `scaleRH c`, `reflRH`, `∫-scaleR`, `∫-reflR`.
19. `Inference/GaussScale` [done] (imports 18, `ScaleDensity`, `GaussReal`): `scDs`, `scD-int`, `push-sym`, `gaussσ`,
    `gauss-dens`, `second : ∫ x² dN(0, s²) ≈ s²`.

**Outcome 14, 17 (2026-11-03, merged into `rq`; no holes, contracts unchanged).**
- `MonoTest`: helper `MonoTestAlg.up-borel` (any ≈-respecting up-closed V : ∣A∣ → Set has Borel preimages).  Not the
  inf-U route: E = ⋂ V as a set of rationals; V agrees with {E ⊆ x} except where x = E as sets, where V is a constant
  P decided by `lem₁`; {E ⊆ h c} and {h c ⊆ E} are countable intersections (`all-enum`).  `Meas-anti` uses the
  complement and double negation.
- `UniquenessRQ`: helper `UniquenessRQAlg` (`addX`, `∫ᴹ-addX`: `Domination.addH`/`∫ᴹ-add` for any X); pointwise
  equalities on RQ by splitting on `inj₁`/`inj₂`.  `lebR-unique`'s `where` block was lifted to top-level lemmas
  (`inf-sp`, `infL`, `infR`, …) to keep longcheck at 35.
- Timings (orchestrator, sequential, load ≈ 4.3): `MonoTestAlg` 4.1 s, 0.57 GB; `MonoTest` 4.7 s, 0.68 GB;
  `UniquenessRQAlg` 4.9 s, 0.70 GB; `UniquenessRQ` 9.2 s, 1.27 GB.

**Outcome 15, 16, 18, 19 (2026-11-03, merged into `rq`; no holes, contracts unchanged; batch hole-free).**
- `LipTest`: helper `LipTestAlg` (`module LipAlg`).  The real gap was that `LocLip` speaks only of points a + w, so
  each cell point needs w with a + w ≈ x: `sub-le`, from `LebesgueShiftCut.diffC`.  Route: q ∈ F x iff `Ge (ratC ρ)
  (F x)` for some rational ρ > q, and `Ge Q (F x)` for x ≤ N+1 iff every level n has a cell with
  Q ≤ F(m/2ⁿ) + ½ⁿ c; Borel as {∞} ∩ const ∪ ⋃_N (≤ N+1 ∩ ⋂ₙ ⋃ₘ (cell ∩ const)).  `deriv-*` read off `D-cG`/`D-ch`/
  `D-ck`, `Gup`/`Gdn` (constant c + c), `D-hU`/`D-hD`, `D-kU`/`D-kD`.  A `with` on a cut term timed out (300 s) again.
- `ChangeOfVariablesFn`: `cov`/`cov-inv` at `φH ψH φ′H`; the hypotheses transfer by identity.  `Ψ-mono` from the
  Galois connection, `Ψ-cong` by antisymmetry.
- `RealScale`: helper lemma `scl` (the halves of h ∘ scaleRH c, pointwise `refl`); `∫-scaleR` is `∫ᴹ-lebR`,
  `distribˡ`, `∫-scale` per half; `∫-reflR` is `+-comm`.
- `GaussScale`: `gaussR` is definitionally `Sym.symDist phiH Z refl n′ nn`.  Helper `half` (the per-half substitution
  of `push-dens`), shared by `push-sym` and `sqhalf`; solver lemmas `sq2`, `cm`, `fin`.
- Timings (orchestrator, sequential, load ≈ 4.0): `LipTestAlg` 8.1 s, 1.04 GB; `LipTest` 7.5 s, 0.99 GB;
  `ChangeOfVariablesFn` 9.4 s, 1.23 GB; `RealScale` 9.3 s, 1.20 GB; `GaussScale` 12.4 s, 1.46 GB (closest to the
  1.5 GB line).

**Order of agents.** 14 ∥ 17, then 15 ∥ 18, then 16 ∥ 19.  Estimated sizes: 14 ≈ 250 lines, 15 ≈ 350 (the riskiest),
16 ≈ 100, 17 ≈ 200, 18 ≈ 100, 19 ≈ 150.

**Risks.**
- 14: inf U of an up-set of cuts must be built as a cut (union of the rationals below every element of U); whether
  inf U ∈ U is decided by excluded middle (`LEM₁` on a `Set₁` proposition).  `Meas` may want the threshold sets at
  `Set` level (`Ge`), not `_≤_`.
- 15: `LocLip` uses `_≤_`; the cell argument needs roundedness of F x (`Cut` rounded) and Bnd c.  If `Deriv` does not
  bound G's increments directly, `deriv-lipG` goes through `Ct1`/`Ct2` with h, k ≤ c from `LpU`/`LpD`.  Fallback:
  derive `deriv-lip*` from `D` fields one at a time in a helper module.
- 16: the values of φ′ at ∞ in `LipTest.lipkH` and in `ChangeOfVariables` must agree; `ChangeOfVariables` takes φ′ as a
  morphism, so `covF` is `cov` at `φH`, `ψH`, `φ′H` plus `Ψ-mono`/`Ψ-cong` from `gc-to`/`gc-from`.
- 17: additivity of `∫ᴹ` on tests over RQ (Domination's `addH` is over WQ only); `copair` computes only on `inl`/`inr`,
  and pointwise equalities on RQ need the coproduct's elimination (`Colimits`).
- 19: `Sym.symDist` is abstract; `push-sym` must go through `∫-sym` only.
- Deferred: translation x ↦ x + t on RQ (needs gluing the pieces of [0, t) and the cut difference), N(μ, σ²),
  products ℝ × ℝ, signed expectations with dominated convergence.

## Translation and products (planned 2026-11-03; skeleton first, then agents; branch `shift`)

Goal: the Gaussian N(μ, s²) for every finite μ, and product measures with Fubini, so that expectations of functions
of two variables reduce to iterated integrals.

**Route.**
- Translation: truncated subtraction of cuts gives the tests x ↦ x ∸ t and x ↦ t ∸ x (`MonoTest`).  The translation
  x ↦ x + t of RQ maps `inl x` to `inl (x + t)`.  It maps `inr x` to `inl (t ∸ x)` when x ≤ t and to `inr (x ∸ t)`
  otherwise; the case split is by excluded middle, and on random elements by the Borel set {β ≤ t}.  Invariance of
  `lebR` splits into three half-line pieces: `LebesgueShift.∫-shift` twice, plus the reflection of [0, t).
- Products: `prodPre s t = join (mapM τ (σ (s , t)))`; Fubini in both orders comes from `SFiniteCommute.commA` and
  `Fub.fubiniᴹ`.  Rectangles, marginals and congruence follow; on the plane: iterated integrals, area, swap.

**Modules.**
- [done] 20 `Continuous/Monus`: `monus`, `monus-cong/mono/anti/add/zero/+`, `subH`, `rsubH`.
- [done] 21 `Continuous/RealShift`: `shiftRH`, `shift-inl/inr-le/inr-gt`, `∫-reflIv`, `∫-shiftR`, `shiftNegRH`,
  `∫-shiftNegR`.
- [done] 22 `Inference/GaussShift`: `gaussμ`, `gaussμ⁻`, `∫-gaussμ(⁻)`, `sym-X`, `fin-X`, `shift-id`, `mean`, `mean⁻`.
- [done] 23 `Continuous/Product`: `prodPre`, `intL/intR(-pt)`, `∫-prod`, `∫-prod′`, `∫-rect`, `marg₁/₂`, `prod-cong`.
- [done] 24 `Continuous/LebPlane`: `leb2`, `∫-leb2(′)`, `∫-leb2-rect`, `rectH`, `area`, `swapH`, `∫-swap`.

**Order of agents.** One agent on 20 → 21 → 22, in parallel with one agent on 23 → 24.  Estimated sizes: 20 ≈ 150 lines,
21 ≈ 300 (the riskiest), 22 ≈ 150, 23 ≈ 150, 24 ≈ 120.

**Risks.**
- 20: `diffC` needs t ⊑ b and a rational bound on t; b = x ⊔ t needs a max of cuts (`LowerRealsMin` has min only).
- 21: `shiftRH`'s `map-random` glues pieces of a random element of RQ along a Borel set (`Colimits`, `LipTestAlg.
  le-borel`); `∫-reflIv` may need `LebesgueInterval.leb-unique` on [0, t) with reflected intervals.  The point x = t
  must be shown null, or absorbed by choosing ≤ versus < consistently.
- 22: `sym-X` from `GaussScale.gauss-dens`, whose two halves are equal by `copairH` computing by `refl`.
- 23: `intL` must be a morphism, i.e. `Fub.Gs` (built from `∫ᶠ` and `τH`); `intL-pt` is then `τ-int`.
- Deferred: the standard Gaussian pair N(0, I₂) with E[X² + Y²] = 2, uniqueness of products on rectangles, signed
  expectations with dominated convergence.

**Outcome (2026-11-03).** All five modules hole-free; no statement changed.
- `Monus`: `monus x t` is a direct cut (q < 0, or t rationally bounded and some q′ > q with q′ + s ∈ x for all s ∈ t),
  not `diffC t (x ⊔ t)`, which would make `monus-anti`/`monus-zero` false for unbounded t; `monus-diffC` relates the
  two.  `monus-zero` by an Archimedean argument (`closure`, `no-shift`).
- `RealShift`: `shiftRH = copair (inlH ∘ shiftH t) (gH t)`, where `gH t` picks by excluded middle and glues
  `map-random` on the Borel set {α ≤ t}.  Helper modules `RealShiftNull` (indicators of {x ≤ c} and its complement,
  the points 0 and t are null, `gt-shift`) and `RealShiftRefl` (h ↦ ∫_{[0,t)} h(t ∸ x) + ∫ h(x + t) is Lebesgue measure
  by `leb-unique`, giving `∫-reflIv`).
- `GaussShift`: finiteness from `Bnd (s · ∫ Xn)`; symmetry of N₀ via the reflection; `mean⁻` from `mean`'s key step by
  reflection.
- `Product`: `intL s g = fixH s (∫ᶠ g ∘ τH)`, `intR t g = fixH₂ t (∫ᶠ g ∘ σH)`; Fubini is `commA` and `fubiniᴹ`; helper
  `cmul`.  `LebPlane`: `area` via `leb-Iv` and `cancel-bnd`; `∫-swap` from the two iterated forms.
- Timings (orchestrator, sequential, load ≈ 3.2): `Monus` 7.2 s, 0.93 GB; `RealShiftNull` 10.5 s, 1.28 GB;
  `RealShiftRefl` 10.7 s, 1.32 GB; `RealShift` 10.4 s, 1.39 GB; `GaussShift` 14.9 s, 1.56 GB (over the 1.5 GB line);
  `Product` 6.7 s, 0.88 GB; `LebPlane` 8.4 s, 1.08 GB.

## Dominated convergence (planned 2026-11-03; skeleton first, then agents; branch `dct`)

Goal: limits of expectations for tests on any X and any s-finite measure: monotone convergence (up and down),
Fatou in both directions, and dominated convergence, with convergence in [0, ∞] meaning lim inf ≈ lim sup ≈ l.

**Route.**
- Infima of lower cuts are interiors of intersections (`interC`); lim inf/lim sup follow.  Pointwise sup/inf of tests
  are tests (`Meas-⨆`, and a new `Meas-inter`).  Upward monotone convergence for `∫ᴹ` is `J-⨆`.
- Downward monotone convergence (∫ h 0 finite) by truncation at N: the bounded case by subtraction (`Monus`) and
  upward convergence, the tail ∫ (h 0 ∸ N) made small by excluded middle.  Fatou from upward convergence, reverse
  Fatou from downward convergence, dominated convergence by chaining the two.

**Modules.**
- [done] 25 `Analysis/LowerRealsInf`: `interC`, `inter-lb/glb/mono`, `union-mono`, `liminfC`, `limsupC`, `liminf-limsup`,
  `liminf-mono`, `limsup-mono`.
- [done] 26 `Continuous/SupTest`: `Meas-inter`, `supH`, `infH`, `liminfH`, `limsupH` with pointwise lemmas, `∫ᴹ-monoX`,
  `∫ᴹ-sup`.
- [done] 27 `Continuous/Fatou`: `minH`, `approx`, `∫ᴹ-inf-fin`, `tail-small`, `∫ᴹ-inf`, `fatou`, `rev-fatou`.
- [done] 28 `Continuous/Dominated`: `Conv`, `dct`, `mct-conv`, `dct-prob`.

**Order of agents.** One agent on 25 → 26, then 27 → 28 (each depends on the last).  Splitting: 25 → 26 first, then
27 → 28.  Estimated sizes: 25 ≈ 100 lines, 26 ≈ 150, 27 ≈ 300 (the riskiest), 28 ≈ 80.

**Risks.**
- 26: `Meas-inter` needs a countable union over rationals q′ > q (enumeration as in `Meas.Meas-⊕`); ψ p f unfolds to
  the weight times f at the point, so `∫ᴹ-sup` needs `⊗-union` under `J-⨆`.
- 27: `tail-small` needs a finite lower real to be approached from below within ½ᵏ (locatedness, by excluded
  middle); `approx` the Archimedean property of cuts.  Fallback: prove `∫ᴹ-inf` with pointwise finiteness of h 0
  first (from `∫ᴹ-inf-fin`) and report.
- Deferred: signed dominated convergence (needs a convergence notion on the signed ring; the canonical f⁺, f⁻
  decomposition), the standard Gaussian pair, uniqueness of products on rectangles.

**Outcome (2026-11-03).** All four modules hole-free; no statement changed; `∫ᴹ-inf` proved as stated (no
pointwise finiteness), so the fallback was not needed.
- New helper modules: `Analysis/LowerRealsNear` (`near-sup-bnd`: a rationally bounded cut is approached from below,
  by excluded middle; `cancel-bnd-⊑`, order cancellation; `inter-add`; `min-split-⊑`) and `Continuous/FatouAux`
  (`monusH`, the test x ↦ f x ∸ g x for pointwise-bounded g; `addX`, `∫ᴹ-addX` on any X).
- `∫ᴹ-inf-fin`: the differences h 0 ∸ h n increase; `inter-add` gives h 0 ≤ ⋂ h + E pointwise, then cancellation.
  `∫ᴹ-inf`: `step-A` (∫ h n ≤ ∫ (h n ⊓ N) + ½ᵏ, via `min-split-⊑` and `cancel-bnd-⊑`) replaces the planned split
  f ≈ (f ⊓ N) + (f ∸ N), which would have needed a case split on cut comparison.
- `Dominated`: `prob-mass` (a probability measure integrates a constant c to c) for `dct-prob`.
- Timings (orchestrator, sequential, load ≈ 5.3): `LowerRealsInf` 3.3 s, 0.60 GB; `LowerRealsNear` 3.5 s, 0.54 GB;
  `SupTest` 4.9 s, 0.73 GB; `FatouAux` 7.3 s, 1.03 GB; `Fatou` 7.6 s, 1.00 GB; `Dominated` 7.7 s, 1.04 GB.

## Signed dominated convergence (planned 2026-11-03; skeleton first, then agents; branch `sdct`)

Goal: dominated convergence for signed tests, h⁺ n − h⁻ n → f⁺ − f⁻, on any X and any s-finite measure, with the
difference of expectations converging.  Signed values stay as pairs (no subtraction of lower reals); convergence of
a difference is stated by cross-adding (`SConv`).

**Route.**
- Convergence with explicit tolerances ½ᵏ (`EConv`) agrees with lim inf ≈ lim sup ≈ l for finite l (`Conv`):
  one direction by `inter-add` and `approx`, the other by excluded middle and `near-sup-bnd`.
- Where the dominating g is infinite the integral sees nothing (∫ g finite gives k · [g = ∞] ≤ g for all k).
- For the signed theorem: d n = h⁺ n + f⁻, e n = h⁻ n + f⁺ cut to {g finite}; p n = d n ∸ e n, q n = e n ∸ d n tend
  to 0 pointwise under the bound g + g, so ∫ p n, ∫ q n → 0 (`dct`); d n + q n ≈ e n + p n pointwise; integrate,
  drop the cut, rearrange.

**Modules.**
- [done] 29 `Continuous/ConvEps`: `EConv`, `conv-econv`, `econv-conv`, `SConv`, `sconv-pair`, `sconv-shift`.
- [done] 30 `Continuous/NullInf`: `finχ`, `infχ` with pointwise lemmas, `∫-infχ`, `∫-null`, `∫-fin-cut`, `∫-off-inf`.
- [done] 31 `Continuous/DominatedSigned`: `dct-signed`, `dct-signed-prob`.

**Order of agents.** One agent on 29 and 30 (independent), then 31.  Estimated sizes: 29 ≈ 200 lines, 30 ≈ 200,
31 ≈ 250.

**Risks.**
- 29: `conv-econv` needs, from ⋂ₙ ⋃_{k≥n} a ≤ l with l finite, a single tail ≤ l + ½ᵏ: excluded middle per tail, then a
  rational above l in every tail gives one in the interior of the intersection (needs a strict gap, via `hp`).
- 30: Borel-ness of {r | α r rationally bounded} (`indH`); `∫-null` via `∫ᴹ-sup` on j · [g = ∞] ⊓ u.
- 31: the pointwise identity d + q ≈ e + p needs a case split d ≤ e or e ≤ d, which lower reals do not decide;
  fallback: by excluded middle on d ≤ e, and on its failure derive e ≤ d by locatedness of bounded cuts
  (`near-sup-bnd`), or report.

**Outcome (2026-11-03).** All three modules hole-free; no statement changed.
- New helper module `Continuous/MonusAlg`: `BndQ` closure lemmas, `rat-bnd` (`BndQ` to `Bnd`), `cut-total` (any two
  cuts are comparable, by excluded middle on a rational witness), `monus-le`, `monus-small`, `monus-swap`.  The
  locatedness fallback for item 31 was not needed: `cut-total` gives the case split d ≤ e or e ≤ d directly.
- `ConvEps` uses `Arch.arch` in place of `Fatou.approx` (stated under an implicit X there).
- `NullInf`: `∫-infχ` by `zero-of` (k · E ≤ N for all k forces E ≈ 0); `∫-null` by `∫ᴹ-sup` on
  [g = ∞] · (u ⊓ n); finiteness as "some n ∉ g x", Borel by `⋃` and complement.
- `dct-signed` is proved directly from the integrated identity (∫ h⁺ + ∫ f⁻) + ∫ q ≈ (∫ h⁻ + ∫ f⁺) + ∫ p and
  ∫ p, ∫ q ≤ ½ᵏ eventually; `sconv-pair` and `sconv-shift` are proved but unused.  `dct-signed-prob` is `dct-signed`
  with g = N.
- Timings (orchestrator, sequential): MonusAlg 6.5 s / 1.03 GB, ConvEps 7.3 s / 1.09 GB, NullInf 8.7 s / 1.07 GB,
  DominatedSigned 7.8 s / 1.09 GB.

## Directions: multidimensional (proposed 2026-11-04; not started, not skeletoned)

Possible next batches, recorded for later; none is scheduled.  Statements below are sketches, not settled signatures.

**On hand.** `Continuous/Product` (s-finite s ⊗ t, Fubini both orders, rectangles, marginals, `prod-cong`),
`Continuous/LebPlane` (Lebesgue on ℝ², `area`, `∫-swap`), `Inference/ExpectationProduct` and `Inference/ExpDistPair`
(independence for signed tests under the probability monad), `Continuous/DominatedSigned` (signed limits).

**Candidate items (most general first).**
- *Finite products.* Xⁿ as iterated `_×Q_`, the n-fold product measure by induction on n over `Product.prodPre`,
  coordinate projections, iterated Fubini, and ∫ ∏ fᵢ(xᵢ) ≈ ∏ ∫ fᵢ.  Open: whether to index by `Fin n` or nest pairs.
- *Moments of random vectors.* For a random vector with finite second moments: mean vector and covariance matrix as
  signed values (`Sg`); independent coordinates have zero covariance; the affine rule mean(AX + b) = A mean + b and
  Cov(AX + b) = A Cov(X) Aᵀ for a signed matrix A.  Route: the pushforward principle and linearity of
  `ExpectationInt` only, so no change of variables.  Open: how to represent vectors and matrices of `Sg`.
- *Gaussian vectors.* N(0, Iₙ) as the n-fold product of `GaussReal.gaussR`: mean 0, covariance I, E‖X‖² ≃ n (the
  pair N(0, I₂) with E[X² + Y²] ≃ 2 is the small first case).  N(μ, AAᵀ) defined as AX + μ, with mean μ and covariance
  AAᵀ, as a corollary of the affine rule.
- *Variance under the measure N(μ, s²)* (one-dimensional gap, noted alongside): centred ∫ (x − μ)² dN(μ, s²) ≈ s² from
  `GaussShift.∫-gaussμ`, a shift-then-unshift lemma (`RealShift.shiftNegRH`) and `GaussScale.second`; the signed form
  E[X²] − (E X)² ≃ s² needs `ITest gaussμ` for X and X².  Both come in μ ≥ 0 and μ < 0 versions (`gaussμ`, `gaussμ⁻`).

**Main risk.** Fubini is proved for nonnegative tests; covariances need integrable signed tests on products, i.e.
moving `ITest`s across the product (the strength route of `ExpectationProduct`), and possibly a signed Fubini from the
parts.

**Out of scope for now.**
- Rotation invariance of N(0, I₂) and the density of N(μ, Σ): both need change of variables in two dimensions
  (Jacobians), and there is no value for π, so Gaussian vectors are characterised by construction and moments.
- Uniqueness of product measures from their values on rectangles: needs a π-λ style argument; a separate project.

## Signed layer (planned 2026-11-04; skeletons on branch `signed`, then agents)

Goal: one vocabulary for signed tests and their expectations against any s-finite measure, so that signed
quantities (centred moments, covariances, scores, log-likelihood ratios, a signed log) are stated uniformly.  The
[0, ∞] core stays as it is: `OmegaSemiring`, `J`, `Meas` and monotone convergence are what make the integral total
and computable (about 217 of 296 modules depend on them), and the signed integral is defined from it,
∫ f = ∫ f⁺ − ∫ f⁻, under an integrability condition, as in standard measure theory.  Replacing [0, ∞] by [−∞, ∞]
throughout is rejected: lower reals cannot be negated, the integral would stop being total (∞ − ∞), and every
measurability and arithmetic lemma would be rebuilt.

**Decisions.**
- Finite signed values are `Sg` (`Analysis/Signed`, `SignedOmega.Bounded A`).  Values in (−∞, ∞] are a second,
  one-sided type `Sg∞` (decided 2026-11-04): pairs (p, n) with n finite and p any element of [0, ∞], equal when
  p + n′ + c ≈ p′ + n + c for a finite c.  Addition is total (no −∞, so no ∞ − ∞) and the witness cannot collapse
  the type, since n, n′ and c are finite; negation is not total.  `Sg` embeds into `Sg∞`.  Two-sided infinities are
  rejected: [−∞, ∞] is not a group, the cross-added equality collapses when the witness may be ∞, and the integral
  would stay partial anyway.  The mirror case [−∞, ∞) (log-likelihoods, log 0 = −∞) is handled by negation of
  statements, not a third type; genuinely two-sided quantities (differential entropy) take a finiteness hypothesis.
- A signed test on X is a pair of tests `Hom S X WQ` (as `dct-signed` uses), not of `CutQ` tests; equality is
  cross-added pointwise, f⁺ + g⁻ ≈ g⁺ + f⁻ (parts may be infinite pointwise).
- The expectation is for s-finite `∫ᴹ`, with integrability `Bnd (∫ᴹ p f⁺) × Bnd (∫ᴹ p f⁻)` as a separate argument
  (values must not depend on the proof).  The probability monad enters by `ιPre`; existing `ITest`/`E-atᴵ` results
  are bridged, not redone.
- Avoid records inside parameterised modules where possible (expensive to check: `Analysis/Exp` header,
  `Inference/Sampler`); a plain Σ or a top-level record.

**Modules (sketch; numbering continues plan 03).**
- 32 `Continuous/SignedTest`: `SgT X` (parts `pos`, `neg`), `_≐_` with refl/sym/trans; pointwise `_+T_`, `-T_`,
  `scaleT` (signed constant, via `mulH` and `constW`), `_*T_` (f⁺g⁺ + f⁻g⁻, f⁺g⁻ + f⁻g⁺), `constT`, `fromW` (a
  nonnegative test), precomposition `_∘T_`; on the real line `idT` (x = x⁺ − x⁻ via `copairH`) and `sqT`.  Bridge
  `CutQ` ↔ `WQ` (identity homs) so `ITest` parts convert.
- 32a `Continuous/SignedInf`: `Sg∞` over an `OmegaSemiring` with the `Bounded` finite elements: `_≃∞_` (an
  equivalence), `_+∞_`, scaling by finite nonnegative constants, `ι∞ : Sg → Sg∞`, `top∞` (+∞), order `_≤∞_`
  (cross-added), `+∞-mono`, `ι∞-+`, and `fromPos : ∣A∣ → Sg∞` (a value in [0, ∞]).  Specific to lower reals (`infC` is +∞; transitivity uses
  `MonusAlg.cut-total`), so it lives under `Continuous/` (no `Analysis` module imports `Continuous`).
- 33 `Continuous/SignedExpect`: `Int p f`, `Ex p f i : Sg`; the one-sided expectation `Ex∞ p f i⁻ : Sg∞` for f with
  ∫ f⁻ finite only (positive part arbitrary), with `Ex∞-ι` (agrees with `ι∞ (Ex p f i)` when both are finite),
  `Ex∞-+`, `Ex∞-mono`, and `Ex∞-fin` (finite when ∫ f⁺ is); `Ex-irr` (independent of `i`), `Ex-cong` (from `_≐_`,
  by `∫ᴹ-addX`), linearity `Ex-+`, `Ex-neg`, `Ex-scale`, `Ex-const` (probability, via `prob-mass`), monotonicity in
  cross-added form, `Int-dom` (|f| ≤ g with ∫ g finite), `Int-+`, `Int-scale`.
- 34 `Continuous/SignedTransport`: `Ex-map` (pushforward, `∫ᴹ-map`), `Ex-scalePre`, the bridge
  `E-atᴵ p t ≃ Ex (ιPre p) (toSgT t) _`, so `var-gaussR`, `var-affI`, `ExpDistVar`, `GaussRealAbs` port by one lemma.
- 35 `Continuous/SignedLimits`: convergence in `Sg` (`SgConv`, tolerances ½ᵏ, as `ConvEps.SConv` on representatives);
  `dct-Ex`: `dct-signed` restated as Ex f n → Ex f.  Then differentiation under the integral along h = ½ⁿ:
  difference quotients 2ⁿ (f(θ + ½ⁿ) − f(θ)) converging pointwise to f′ and dominated by g give
  2ⁿ (Ex f(θ + ½ⁿ) − Ex f(θ)) → Ex f′ (no division needed).
- 36 `Continuous/SignedFubini`: for s ⊗ t (`Product.prodPre`) and an integrable signed test on X × Y, the inner
  integrals are finite off a null set; cut there (`NullInf.finχ`) to get a signed test on Y, and
  Ex (s ⊗ t) f ≃ Ex t (inner f); independence `Ex (s ⊗ t) (f ⊗ g) ≃ Ex s f *S Ex t g`.
- 37 `Continuous/SignedLog` (needs only 32a): for 0 < x < ∞ (bounded above and below by rationals),
  `logP`, `logN` characterised by e^{logP x} ≈ x on [1, ∞) and e^{−logN x} ≈ x on (0, 1] (definitions left to the
  agent, suggested in the header), `logS x : Sg`, one-sided `log∞` and `nlog∞` (−log 0 = ∞); `log-mul` (log xy ≃ log x + log y), `log-mono`, `log-exp`, and measurability of
  r ↦ log⁺/log⁻ (h r) for use as test parts.

**Order of agents.** Strict agda refuses imports with holes, so: round 1, one agent on 32 and 32a (independent,
both small); round 2, two agents, one on 33 → 34 → 35 and one on 37; round 3, 36 (needs 33 and `NullInf`).
Estimated sizes: 32 ≈ 200 lines, 32a ≈ 150, 33 ≈ 300, 34 ≈ 150, 35 ≈ 250, 36 ≈ 300, 37 ≈ 300.

**Risks.**
- 32a: transitivity of `_≃∞_` in `Analysis/Signed` uses the witness c + d + p′ + n′, which is not finite when
  p′ = ∞.  Route: by excluded middle, either p′ is finite (the old proof) or p′ ≈ ∞, and then p ≈ p″ ≈ ∞ (x + a ≈ ∞
  with a finite forces x ≈ ∞, from `Bnd` and `cancel-bnd`), so the pairs are equal with any witness.  Alternative:
  define `_≃∞_` as "both p, p′ infinite, or the finite cross-added equality", if the first route is awkward.
- 33: `Sg` elements carry `Bnd` proofs; `Ex-irr` must hold so that proofs never leak into statements.
- 34: `CutQ` and `WQ` are distinct QBSs on the same carrier; the bridge must be definitional enough that
  `E-atᴵ`'s pulled-back `J` matches `∫ᴹ (ιPre p)` (`ψ` unfolds to weight · f).
- 35: the derivative form needs f(θ + ½ⁿ) as a family of signed tests indexed by the parameter; stated for an
  explicit family, not a general parametric model.
- 36: inner integrals are finite only almost everywhere; relies on `NullInf` and on Fubini for each part.
- 37: `log⁻` needs x bounded below by a positive rational; `log-mul` needs `exp` addition (`Analysis/Exp`) and
  near-sup arguments (excluded middle) for the reverse inequalities.

**Unlocks.** Centred variance under N(μ, s²), Fisher information as E[score²] and E[score] ≃ 0 (via 35), KL as
E_P[log dP/dQ] in (−∞, ∞] with no finiteness hypothesis (via 32a, 37), discrete entropy and −log-likelihood
with +∞ allowed, covariance matrices and the affine rule (multidimensional directions), signed Fubini.

