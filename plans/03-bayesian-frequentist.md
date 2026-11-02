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
