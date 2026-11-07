# Audit: `inference` domain (60 modules, src/QBS/Inference/, about 8,600 lines)

Evidence base: module headers of all 60 files, the top-level statements of Bayesian, CoinPosterior, ExpFamily, the
ExpDist*/ExpMomentN/ExpRateDist import blocks, and the Interface.md entries (lines 126-233).  Proofs were read only
where noted.  Findings flagged "unverified" come from headers and greps, not from reading the proofs.

## 1. Summary

The domain is statistical inference done on top of the two concrete probability models (discrete weights, and the
continuous lower-real monad of s-finite measures).  It has four strands, which are interleaved in the directory but
mathematically independent:

1. **Expectation calculus** (`Expectation*`, `SymExpectation`, `PushforwardExpectation`, `DensityExpectation`,
   `Domination`, `Poly*`): the signed/integrable expectation `E-at`/`E-atᴵ`, linearity, independence for `⊗ᵖ`,
   pushforward, integrability by domination.
2. **Named distributions as tests of that calculus** (`ExpDist*`, `ExpMomentN`, `ExpRate*`, `ExpPushforward*`,
   `Gauss*`, `HalfNormal*`, `Bern*`, `BoolDist`): means, variances and moments of Exp, Gaussian and half-normal laws.
3. **Bayesian inference** (`Bayesian`, `ExpFamily`, `Coin*`, `CondIID*`, `BernoulliCompare`): posteriors by reweight-and-
   normalise, sequential updating, the Beta(1,1)-Bernoulli model, Bayes risk, conditionally iid kernels.
4. **Frequentist inference** (`Frequentist`, `Sampler`, `Uniform*`, `IIDLaw`, `MultiSample*`, `Gauss{Vector,VectorLaw}`,
   `WeakLaw*`): unbiasedness of sample mean and variance, Chebyshev, weak law.

Recommendations (most important first):

1. **State Bayes' law once, as an equation between kernels, and derive the conjugacy results from it** (section 5).
   Today the posterior is defined three times (`Example/Bayes.posterior` for weights, `CoinPosterior.posterior` for
   s-finite measures, and the unnormalised `posteriorU`), and conjugacy twice (`Inference/ExpFamily`, discrete;
   `Continuous/ExpFamilyPost`, continuous) with no shared abstract statement.
2. **Split the directory** into `Inference/Bayes/`, `Inference/Frequentist/`, `Inference/Expectation/` and
   `Inference/Distributions/`.  Sixty flat modules, with strands 3 and 4 keyed only by "plan NN, item MM" references in
   headers, is the largest barrier for an outsider.  Cost: rename churn only (module names are public in Interface.md).
3. **Kill the 15-30 line import/`open` preamble repeated in about 54 modules** (`module X (lem₁ : LEM₁)`; each re-opens
   `Lebesgue (lemOf lem₁)`, `OmegaSemiring A`, `Bounded A`, `Weights`, `SFinite`, `SFiniteIncl`, ...).  One
   `Inference.Prelude lem₁` record/module that re-exports the standard bundle would shrink every file by 20-40 lines.
4. **Merge the helper sprawl** (`*Alg`, `*Aux`, `*Ring`: GaussVar/Aux/Pt, GaussVector/Alg, MultiSample/Alg/Ring,
   WeakLaw/Alg/Cheb, CondIID/Const/Coin/CoinStep): 17 modules whose sizes are 38-190 lines each.
5. **Make the Exp/Gauss distribution family one parametrised development**: ExpDistMean/Var/Pair, ExpMomentN,
   ExpRateDist/One, ExpPushforward/Agree, GaussReal/Abs/Scale/Shift/Var/Affine are the same pattern (build `ITest` from
   a half-line integral, then reduce) repeated per statistic and per distribution.

## 2. Main results

Status key: Y = in Interface.md and crisp; P = in Interface.md but buried or terse; N = not listed or not findable.

| Name (file:line) | Plain statement | Maths | Doc |
|---|---|---|---|
| `E-at`, `E-atᴵ` (Expectation, ExpectationInt) | expectation of a bounded / integrable signed statistic | E_p[g] = ∫g⁺ − ∫g⁻ valued in the signed completion | Y (Interface 126-135); header of ExpectationInt is good |
| `E-at-⊗`, `E-atᴵ-⊗` (ExpectationProduct, ExpectationIntProduct) | independence: E[f(X)g(Y)] = E f E g under `p ⊗ᵖ q` | E_{p⊗q}[f⊗g] = E_p f · E_q g | P: the integrable version is a separate file with no pointer from the bounded one beyond the header |
| `E-atᴵ-map` (PushforwardExpectation) | change of variables | E_{f∗p}[g] = E_p[g∘f] | P: only lives in the Gauss/Exp context; deserves a line in Guide.md |
| `posterior`, `bayes` (CoinPosterior) | Bayes' rule | ∫f dπ = n ∫ℓ f dp, n·∫ℓ dp = 1 | P: buried in a *coin* file (CoinPosterior.agda around lines 90-110) although it is fully general |
| `post1`, `post1-mean` (CoinPosterior:141,158) | after one head, uniform prior gives Beta(2,1), mean 2/3 | 3·E[θ|H] = 2 | Y |
| `post2-agree` (CoinPosterior:219) | sequential = batch updating | π(θ|H,H) via two steps equals one step with θ² | Y; generic content, see section 4 |
| `succession` (CoinUniformPriorN) | Laplace's rule of succession | (n+2)P(Hⁿ⁺¹) = (n+1)P(Hⁿ) | Y |
| `risk-P` (CoinBayesRisk) | posterior mean beats the sample-frequency estimator in Bayes risk | 1/18 < 1/6 | Y; 381 lines for two numbers (see section 4) |
| `posterior-update-norm` (ExpFamily, discrete) | conjugacy for multiplicative exponential families | posterior of conjugate prior (χ,ν) after xs is conjugate (χ+ΣT, ν+n) | P: absent from the Interface.md excerpts read; headline is the Bernoulli instance |
| `Bernoulli.likSeq-counts` (Bayesian) | Bernoulli likelihood depends on counts only | sufficiency | Y |
| `sampler-mean-unbiased` (Sampler) | sample mean unbiased for every sampler | E S_n/n = μ | Y |
| `chebyshev-at`, weak law (WeakLaw*) | Chebyshev and weak law of large numbers | P(|X−c|≥e) ≤ Var/e² | P: the three WeakLaw files are listed but the final WLLN statement is not named in a one-line summary |
| `iid-mean`, `iid-var`, `iid-ss` (IIDLaw) | moments of sums of iid draws | E S_n = nm, Var S_n = ns | Y |
| `affLaw-cov` (GaussVectorLaw) | Gaussian vectors: Cov(AZ+b) = A Cov Z Aᵀ | affine rule | P |
| `Kn-iid` (CondIIDCoin) | coin flips are conditionally iid and exchangeable | | N: plan-05 item numbers instead of a statement of the theorem |
| `gaussμ`, `mean`, `cvar` (GaussShift, GaussVar) | N(μ,s²) has mean μ and variance s² | | Y but spread over 6 files |
| `halfNormal`, E[X] = n (HalfNormal*) | half-normal law and mean, no π | | Y |

## 3. Documentation

- **Headers reference "plan 03/05/07, item NN" instead of stating the result.**  Examples: CondIID, CondIIDCoin,
  CondIIDCoinStep, CondIIDConst, GaussVector*, MultiSample*, WeakLaw*, ExpFamily.  An outsider cannot open plans/.
  Fix: keep the plan reference but lead with the theorem.  Proposed header for `CondIIDConst`: "`∫-constW`: ∫ c dq ≈ c · ∫ 1 dq
  for s-finite q (a constant test integrates to the constant times the mass)." (the current text is already close; the
  fix is to delete "plan 05, item 48 helper" from the first line).
- **`CoinPosterior` hides the general theorem.**  Its title should be "Bayes' rule for s-finite measures; Beta(2,1)
  example".  Proposed split: `Inference.Bayes` (lines about `posterior`, `massP-rw`, `inv-rw`, `bayes`) and
  `Inference.CoinPosterior` (the example).  See section 4 item A.
- **Module names that do not say what they contain.**  `Bayesian` (discrete Bayes extras; rename `Bayes.Discrete` or
  `DiscreteBayesExtras`), `Frequentist` (rename `Frequentist.Experiment`), `Sampler` (`Frequentist.Sampler`),
  `ExpFamily` here vs `Continuous.ExpFamily` (identical names in two packages; rename this one `Bayes.ExpFamilyDiscrete`),
  `Domination` (`Integrability.ByDomination`), `Expectation` (really "calculus of bounded signed tests").
- **Interface.md** lists these modules as very long single bullets (lines 126-145 are 6-10 lines each, with many identifiers).
  Proposed addition at the top of the Inference part of Interface.md, one table of strands:

  | want | read first |
  |---|---|
  | expectation of a signed or unbounded statistic | `Inference.ExpectationInt` |
  | Bayes' rule and posteriors | `Inference.CoinPosterior` (`posterior`, `bayes`) and `Example.Bayes` |
  | conjugacy | `Inference.ExpFamily` (discrete) and `Continuous.ExpFamilyPost` (continuous) |
  | unbiased estimators, law of large numbers | `Inference.Frequentist`, `IIDLaw`, `WeakLaw` |
  | Gaussian laws | `Inference.GaussShift`, `GaussVar`, `GaussVectorLaw` |

  Guide.md lines 210-214 describe Bayesian inference in four bullets and do not mention `ExpFamily`, `CondIID`, or the
  frequentist strand; add them.
- Module-count honesty: Contributing/Architecture say modules are "named by what they contain"; `GaussVarAux`, `MultiSampleAlg`,
  `WeakLawAlg` break that (they are helpers).  Put helpers in a `Helpers` subfolder or merge (section 4).

## 4. Simplification

**A. Bayes' rule is proved in two models with different statements.**  `Example/Bayes.agda:~88` (`MP.∫ (posterior p w n h) f ≈ n * ∫ p (_·_ w f)`)
and `CoinPosterior.agda` (`∫f d(posterior ℓ p n h) ≈ n ∫ ℓ f dp`) are the same equation.  Both models are instances of
the abstract probability/statistical interface (`QBS.Probability`/`Statistical` in the abstract domain).  Proposed:
state `reweight`, `normalise`, `bayes`, `posterior-prop` (normalised posteriors of proportional weights agree),
`sequential` (reweight twice = reweight by the product), and `inv-unique` once over the abstract interface (needs
`reweightPre` to be an interface operation; the continuous model has it as `SFiniteReweight.reweightPre`, the discrete as
`Example/Bayes`).  Instantiate in both.  Gain: the ExpFamily conjugacy (A2) and `post2-agree` follow without per-model
proofs.  Risk: the abstract layer would need a "reweightable measures" interface (a small record); universe levels
are the main hazard because the continuous model is parameterised by `lem₁`.  Unverified: whether `IsStatisticalQBSLike`
already exposes a reweighting; check before adding.

**A2. Conjugacy duplicated.**  `Inference/ExpFamily.agda` (380 lines, discrete, ℕ-valued statistics, `posterior-update`,
`posterior-update-norm`) and `Continuous/ExpFamilyPost.agda` (`posterior-update : reweight (priorPre p) (likWeight T) ≈ priorPre (updateSample p T)`).
The second is already stated as "reweighting by the likelihood gives the updated prior".  Both are the monoid-action
statement: the map (χ, ν) ↦ prior(χ, ν) is a homomorphism from the additive monoid of sufficient statistics to
the *reweighting action* on measures.  Prove the abstract lemma "if w_p · w_q = w_{p+q} then reweight q ∘ reweight p = reweight (p+q)" once; both
posterior-update lemmas are one-liners.  That would also let `likSeq-factor` be the single induction.

**B. `post2-seq` / `post2-batch`** (CoinPosterior.agda:198-219, about 35 lines with its own `inv-batch`, `inv-seq`) is
the instance of `Bayesian.sequential` (discrete) at the continuous model; A removes it.

**C. Repeated preamble.**  The same ~12 `open` lines of the form `open Lebesgue (lemOf lem₁) using (...)` appear in ExpDistMean:32-45,
ExpMomentN:~30-50 and ExpRateDist:~30-50, and in most of the 54 modules that take `lem₁`.  A shared
`module Prelude (lem₁ : LEM₁)` (exporting `A`, `J`, `Bnd`, `_≃_`, `WQ`, `∫ᴹ`, `ιPre`, `ITest`, `E-atᴵ`) reduces every
file by about a quarter.  Cost: one new module; instance-argument/`using` lists then need `public`.  Compile cost is
neutral to slightly negative (re-opening records is cheap; the modules are re-instantiated per use today).
Risk: anything that relies on name shadowing between local `open`s.

**D. Per-statistic files for one pattern.**  `ExpDistMean` (74), `ExpDistVar` (88), `ExpMomentN` (78), `ExpRateDist` (145),
`ExpRateOne` (57): `ExpMomentN` already subsumes mean and variance (`n = 1, 2`, as its header says).  Make
`ExpDistMean`/`ExpDistVar` thin specialisations in one file, or delete them if dependents are few (ExpDistPair
and ProductMarginals import them; check with grep before deleting).  Same for `GaussVar`/`GaussVarAux`/`GaussVarPt`
(421 lines in three files for "variance of N(μ,s²)").

**E. Helper merges** (each helper is used by exactly one parent according to its header):
`WeakLawAlg` (68) + `WeakLawCheb` (68) into `WeakLaw` (154), giving about 290 lines; `CondIIDConst` (38) into `CondIID`
(it is "used by CondIID.joint-fst" and compares to `SFiniteSum.∫ᴹ-scale`; arguably it belongs in `SFiniteSum`);
`CondIIDCoinStep` (72) into `CondIIDCoin`; `GaussVectorAlg` (63) into `GaussVector`; `MultiSampleRing` (93) and
`MultiSampleAlg` (148) are the one place where a split is justified (ring identities abstracted over a commutative
ring), but name them `MultiSample.RingLemmas` and `MultiSample.Transport`.  Gain: fewer files, clearer imports.
Cost: bigger modules (type-check memory; none exceeds 400 lines after merging).

**F. `BoolDist` (347) and `CoinBayesRisk` (381)** are the two largest files and carry bespoke arithmetic
(`risk-X`, `risk-P9`, `risk-P`, `risk-X18`: four statements about 1/6 and 1/18).  The header says the arithmetic
is in an abstract `Alg` applied to a copy of the signed ring; replacing the hand-multiplied forms by a
`CommutativeSemiring` solver (`Tactic.RingSolver`) call in that `Alg` would plausibly halve it.  Unverified: did not read the proofs.

**G. Domination is split**: `Domination` (generic) + `PolyDomination` (even degree under Exp) + `PolyDominationOdd` (half-normal, all degrees).  The odd file's header says it
"extends" the even one; the even-degree-only hypothesis looks like a historical artefact (the odd file proves
`xᵏ ≤ 1 + x^{2k}`).  Check if `PolyDomination` can use the same lemma for the Exp case, then keep one `PolyDomination` with both instances.

**H. Hypotheses never used** (to check): `ExpRateDist` takes `l ≤ natE (suc μ)` and `c ≤ natE (suc ν)` as finiteness hypotheses; `ExpPushforward` already
shows that `Bnd c` suffices without a reciprocal.  If `expDistλ` were defined as `expPush c` plus one agreement lemma
(`ExpPushforwardAgree` does this for c = ½), `ExpRateDist` (145) + `ExpRateOne` (57) could shrink to the agreement lemma.
The same remark applies to `GaussScale`/`GaussShift`/`GaussAffine`: `GaussAffine` obtains N(μ,σ²) from N(0,1) with "no new integral",
which is how `GaussShift` and `GaussScale` should also be phrased (one `affine pushforward` lemma, then moments by
`PushforwardExpectation`).  Unverified for the proofs.

## 5. Categorical language

- **Kleisli composition is not used anywhere in the domain** (`grep Kleisli` over `src/QBS/Inference`: no matches;
  the only mention in the library is a comment in `StatisticalLemmas.agda:3`).  Kernels appear as morphisms
  `Θ ⇒ T X` (`coinKernel`, `Kn`, `kpow`, `ψH` in CondIID) and are composed by `joinPre (mapPre K p)` (see the headline of
  `CoinUniformPrior`: `joinPre (mapPre coinKernel uniform)`), which is `p >>= K` written out.  **Recommendation: do not
  switch to agda-categories' `Kleisli`.**  The library's monad `T` is a monad in the QBS category over a *setoid-level*
  `Pre` of probes, with equality `≈ᵖ` that is not propositional; agda-categories' `Kleisli` needs a `Monad` on a
  `Category` with `_≈_` on hom-sets, which the QBS category does have, but each use of `Kleisli.id`/`_∘_` would unfold to
  `join ∘ map`, and every proof in this domain is about integrals (`∫-join`, `∫-map`), not about categorical
  equations.  What is worth doing is defining **one named composition** `_>>=ᵖ_ : Pre X → (X ⇒ T Y) → Pre Y` (and `_⋆_` for kernels
  `Θ ⇒ T X`, `X ⇒ T Y`) with `∫-bind : ∫ (p >>= K) f ≈ ∫ p (λ x → ∫ (K x) f)`, then rewrite the headlines
  in that vocabulary.  Cheap: no universe or setoid problems (it is a def).
- **Bayes' law as a categorical equation.**  In Markov-category language (Cho–Jacobs; Fritz): a kernel `k : Θ ⇒ T X` with prior
  `p`, the joint is `⟨id, k⟩ ∘ p : 1 ⇒ T (Θ × X)`; a Bayesian inverse is `k† : X ⇒ T Θ` with
  `swap ∘ ⟨id,k⟩ ∘ p ≈ ⟨id, k†⟩ ∘ (k ∘ p)`.  The library's `CoinBayesRisk.joint` and `E-joint` already construct the joint, but
  the statement `bayes` is a *density* identity (∫f dπ = n ∫ℓ f dp) which is the special case when `k` has density ℓ with respect to a reference measure.
  Worth stating: **disintegration for dominated kernels** `posterior ℓ p n h` is a Bayesian inverse of `k = ℓ·ν` (one
  lemma, building on `Continuous/SFiniteStrong` for strength).  Not worth stating at full Markov-category generality,
  since this library has `T X` of s-finite measures where "almost sure equality" requires measure-theoretic null-set
  reasoning not available in the setoid-based interface (cf. the out-of-reach list).  The benefit: `post1`,
  `post2-agree`, `ExpFamily` follow from the dominated-kernel lemma plus the monoid-action lemma (A2).
- **Strength/commutativity.**  `CondIID.ψH` is Kock's double strength; the library has `SFiniteStrong`.  The kernel power
  `kpow n K = K^{⊗n}` is the n-fold iterate of `ψ` along `Fin n → ·`; stating it as the monoidal functor structure
  `T (X)ⁿ ← (T X)ⁿ` (agda-categories `Categories.Functor.Monoidal`) would give `kpow` its naturality for free,
  but the cost is high (monoidal structure on the QBS category is a separate development, and the header says
  `Exchangeable` already has what is needed).  Defer.
- **Pushforward.**  `mapPre f p` with `E_{f∗p} g = E_p (g∘f)` is functoriality of `T`; `PushforwardExpectation`,
  `ExpPushforward`, `GaussAffine` and `ScaleDensity` all *use* it; stating the functor-law corollaries (`mapPre (f∘g) ≈ mapPre f ∘ mapPre g`, `mapPre id ≈ id`)
  once with agda-categories `Functor` reasoning would remove several inline recomputations, if the Continuous model already packages `T` as a `Functor`
  (unverified; grep `Endofunctor` in `Continuous/Monad` before adding).
- **Expectation as a linear functional.**  `E-at p` is additive and homogeneous (`_+T_`, `scaleT`, `E-at-+`, `E-at-scale`),
  so the whole algebra (`Expectation`, `ExpectationInt`) could be stated as a module morphism from the signed-test module to the signed values.  There is no agda-categories
  gain here; use stdlib `Algebra.Module.Morphism` only if the structure is already a module (unverified).  Bespoke version is fine.
- **Gaussian family** is the image of N(0,1) under the affine group; `GaussShift`/`GaussScale`/`GaussAffine` are three
  presentations of the same pushforward.  Stating the action of `Aff` on `RQ` once (a monoid action, composition law
  `aff a b ∘ aff c d = aff (ac) (ad+b)`) would remove the repeated case split on `μ ≥ 0` (`gaussμ` and `gaussμ⁻` exist only because
  the lower reals have no subtraction; this is a genuine constraint, not a defect).

## 6. Open questions for the maintainer

1. Does `IsStatisticalQBSLike` (or `Statistical`) already expose reweighting and normalisation?  If not, is a small
   `Reweightable` record at the abstract layer acceptable, so that `Example.Bayes`, `CoinPosterior` and the two ExpFamily
   modules share one statement of Bayes' rule?
2. Are `plans/` item numbers meant to stay in module headers permanently?  The audit suggests moving them after the mathematical statement.
3. Is `Inference.ExpFamily` (discrete, ℕ statistics) still wanted now that `Continuous.ExpFamilyPost` proves the
   continuous analogue with real exponents, or should the discrete one become the `Bernoulli`-only demonstration?
4. May `ExpDistMean`, `ExpDistVar` and `ExpRateOne` be folded into `ExpMomentN`/`ExpPushforward`?  Please list any downstream
   (non-Inference) importers I could not check.
5. Is a `Kleisli`-style named composition (`_>>=ᵖ_`) acceptable as an addition to `Continuous.Monad`, outside the Inference domain?
6. Is there a compile-time budget per merged file (section 4 E would create files of 200-300 lines)?
