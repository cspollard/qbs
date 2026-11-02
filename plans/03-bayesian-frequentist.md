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
