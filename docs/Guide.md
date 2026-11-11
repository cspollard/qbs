# Guide: using the library

Task-oriented tour. For how the modules fit together see [Architecture.md](Architecture.md); for one line per module
see [Modules.md](Modules.md).
Code blocks that start with `-- from: path` are verbatim excerpts of that file; `scripts/doccheck.py` checks
that they are still there (run `make doccheck`).

## Reader's map

The library in layer order, with the headline result of each layer and where to read it. `Modules.md` has one
line per module.

| Layer | Headline result | Read |
|---|---|---|
| Abstract: quasi-Borel spaces over a random source | `QBSCat S` is complete, cocomplete, cartesian closed | `QBS.Core`, `QBS.Category`, `QBS.Exponential` |
| Abstract: probability and soft conditioning | a commutative strong monad with Fubini (`ProbabilityInterface`), plus scoring and sums (`StatisticalInterface`); Kleisli vocabulary in `QBS.Bind` | `QBS.Probability`, `QBS.Statistical`, `Categories.Monad.Commutative.Cartesian`, `QBS.QBSLike` |
| Discrete model | weighted programs over any complete semiring; Bayes' rule and rejection; `discreteStatisticalQBSLike` | `QBS.Model.Discrete`, `QBS.Example.Program`, `QBS.Example.Recipes` |
| Lower reals | `[0,∞]` as lower cuts of ℚ: Ω, then Arch/Min, then series and instances | `QBS.Analysis.Omega` (header), `QBS.Analysis.LowerReals` |
| Measure construction | the fair coin on Cantor space as a Daniell functional, with uniqueness and regularity | `QBS.Analysis.CoinIntegral`, `QBS.Analysis.Daniell.Facts`, `QBS.Analysis.Uniqueness`, `QBS.Continuous.FairCoin` |
| s-finite measures | monad, strength, products, iid and exchangeability | `QBS.Continuous.Monad`, `QBS.Continuous.SFinite`, `QBS.Continuous.Product`, `QBS.Continuous.IID` |
| Lebesgue measure and convergence | `leb-unique` (one uniqueness lemma, then shift, scale, change of variables `push-eq`), `fatou`, `dct` | `QBS.Continuous.LebesgueInterval`, `QBS.Continuous.UniquenessCantor`, `QBS.Continuous.ChangeOfVariables`, `QBS.Continuous.Fatou`, `QBS.Continuous.Dominated` |
| Distributions | one density recipe `densDist`; uniform, exponential, Gaussian moments (certificate calculus `QBS.Analysis.Deriv*`) | `QBS.Continuous.DensityDist`, `QBS.Continuous.Uniform`, `QBS.Continuous.HalfLineMomentFact`, `QBS.Analysis.Deriv` |
| Signed layer and information | signed tests and expectations, variance, KL divergence | `QBS.Analysis.Signed`, `QBS.Continuous.SignedTest`, `QBS.Continuous.SignedExpect`, `QBS.Continuous.KLDiv` |
| Inference | Bayes' rule for s-finite measures (`bayes`), conjugacy, conditionally iid data, Chebyshev and the weak law | `QBS.Inference.CoinPosterior`, `QBS.Inference.ExpFamily`, `QBS.Inference.CondIID`, `QBS.Inference.WeakLaw` |

## 0. Which model do I use?

There is one abstract interface and two concrete models of it.

| I want to… | Use | Random source | Values | Hypotheses |
|---|---|---|---|---|
| prove something for *any* probability/measure monad | `IsQBSLike` (`QBS.QBSLike`) | any `RandomSource` | abstract weights `W` | none: the monad is an argument |
| write and run small probabilistic programs (`do`-notation), discrete distributions, Bayes' rule, rejection | discrete model: `Example.Program`, `Model.*` | `ℕ` (`discreteSource`) | any complete semiring: Boolean, Viterbi, ℕ∞, additive `[0,∞]` | `lem` only for the real-valued semirings (at `Set₁` for the additive one) |
| continuous distributions (uniform, fair coin, exponential, Gaussian), integrals of measurable functions, soft conditioning, normalisation, signed expectations, variance, KL divergence | continuous model: `Continuous.*`, `Analysis.*` | Cantor space `2^ℕ` | `[0,∞]` as lower cuts of ℚ | `lem` and `lem₁` (excluded middle at `Set`, `Set₁`); see [Classical.md](Classical.md) |

Rules of thumb:
- A theorem about *estimators and inference* should be stated generically (over `IsQBSLike` or over a
  semiring), then instantiated. That is how `Example.Bayes` and `Example.Probability` are written, and it also keeps
  compile times down (at the concrete lower-cut semiring Agda unfolds the cuts; see Architecture.md, "Compile time").
- The core integral is non-negative (`[0,∞]`). Signed quantities (variance, bias, log-likelihood ratios) are built on top
  of it; see section 5.

## 1. Write a probabilistic program and compute an expectation (discrete model)

`Example.Program` has `Programs A K ok1` (a complete semiring `A`, a weight class `K` such as `probClass A`),
giving `Prog T` (a measure on Agda values of type `T`), `pure`, `_>>=_` (so `do` works), and the expectation
`∫ p (test g)` of a function `g : T → A`. The rules `∫-pure` and `∫-bind` let you unfold it. `Flip` adds a fair coin.

```agda
-- from: src/QBS/Example/Program.agda
    both : Prog B
    both = do
      a ← flip
      b ← flip
      pure (a ∧B b)
```

```agda
-- from: src/QBS/Example/Program.agda
    ∫-flip : ∀ (g : B → ∣A∣) → ∫ flip (test g) ≈ half * g tB + half * g fB
```

A complete set-up (also a checked module, `Example.Recipes.Bernoulli`) for a Boolean coin over any complete
semiring `A` with `half + half ≈ 1`, including the weight class and the `Lift ℓ Bool` outcome type:

```agda
-- from: src/QBS/Example/Recipes.agda
  open Programs A (WC.probClass A) (λ p → p)          -- weight class: probability measures; `ok1` is the identity
```

```agda
-- from: src/QBS/Example/Recipes.agda
  flip-mean : ∫ flip (test isTrue) ≈ half
```

Notes: `flip : Prog B` is the coin itself; `isTrue` (in `Recipes`) is the indicator of `true` as a test function;
import `QBS.Model.WeightClasses` qualified, because `QBS.Analysis.Measure` also exports a `probClass` (a different one,
for the continuous model).

Workflow: `open Programs A K ok1`, `open Flip half half+half B tB fB _∧B_`, write your program, then prove its
expectation by rewriting with `∫-bind` / `∫-flip->>=` / `∫-pure` (see `∫-both`). `Example.Probability` shows the
same program with real probabilities:

```agda
-- from: src/QBS/Example/Probability.agda
  both-true : ∫ both (test isTrue) ≈ half * half
```

## 2. Condition on data

Three tools, in increasing generality:

1. **Hard rejection** (`Example.Conditioning`): `guard : Bool → Prog ⊤`, `reject`. The lost mass is the probability of
   rejection and `∫` is the unnormalised expectation. `∫-guard` computes `E[guard c >> k]`.
2. **Hard conditioning as a transformer** (`Example.HardConditioning`): `condition p c` keeps the runs where the
   observation `c` holds; `condition-split` is the law of total expectation.

   ```agda
   -- from: src/QBS/Example/HardConditioning.agda
     condition : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Obs X → Pre X
   ```
3. **Soft conditioning / Bayes' rule** (`Example.Bayes`, generic in a `NormalizableSemiring`): reweight the prior by
   a likelihood `w`, then normalise by the inverse `n` of the evidence.

   ```agda
   -- from: src/QBS/Example/Bayes.agda
     bayes : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (w f : Func (QBS.Carrier X) Aˢ) (n : ∣A∣)
       (h : evidence p w * n ≈ 1#) → MP.∫ (posterior p w n h) f ≈ n * ∫ p (_·_ {X} w f)
   ```

   Abstractly, the same operations are the fields `score`, `scaleM` and `normalize` of `StatisticalInterface`
   (`QBS.Monad.Statistical`).

## 3. Continuous distributions and integrals

The continuous model has the fair coin on Cantor space (`Continuous.FairCoin`), the uniform distribution on
`[0,1]`, and an integral of any measurable function.

- The whole set-up is one checked module, `Example.Recipes.UniformSetup lem₁`: it fixes the value semiring `A`
  (lower cuts, via `lemOf lem₁`), the unit interval `AQ`, `∫`, `half`, and `uniform : Pre AQ`.

```agda
-- from: src/QBS/Example/Recipes.agda
  open Continuous A (lemOf lem₁) probClass public using (∫)
```

- `∫ p f` (`Continuous.Monad`) is the integral of a morphism `f : Hom S X AQ` (values in `[0,1]`) against `p`.
  `Hom` is a record (a function plus a proof that it preserves random elements): get morphisms from the library
  (e.g. `idH S {AQ}` from `QBS.Core`, with `S = cantorSource` explicit), not from raw functions.
- `mean` below is stated for the underlying Daniell integral `I` of the fair coin along the binary expansion, i.e. for
  the integrand `expansion`; it is what `∫ uniform (idH S {AQ})` unfolds to, but that restatement is not proved
  as a named lemma yet.
- Facts proved so far: `E[u] = ½` and the CDF, `P(u ≤ t) = t`:

```agda
-- from: src/QBS/Continuous/UniformMean.agda
  mean : I fairCoin expansion Fun-expansion ≈ half
```

```agda
-- from: src/QBS/Continuous/UniformCDF.agda
  cdf : ∀ (t : ∣A∣) → t ≤ OmegaSemiring.1# A → ∫ uniformSub (cdfTest t) ≈ t
```

- More distributions: the exponential distribution (`Continuous.ExpDist`, all moments in `Inference.ExpMomentN`), the
  uniform variance (`Continuous.UniformVariance`), and Gaussians (section 5).
- Unbounded and weighted integrals use `J` (`Analysis.Lebesgue`), which integrates any threshold-measurable
  `[0,∞]`-valued function (`Meas`). The s-finite monad `TM` (`Continuous.SFinite*`) is built on `J`; its
  statistical structure is `continuousStat` in `Continuous.SFiniteStat`
  (`open SFiniteStat lem`), so every result stated over `StatisticalInterface` applies to it.

### Products, independence and iid (continuous core)

- Both monads are commutative strong monads (`Continuous.Strong.commutative` is Fubini; `Continuous.SFiniteCommute.commutative`
  is Tonelli for `[0,∞]`), and `Continuous.SFiniteIncl.inclusion` embeds the probability monad in the s-finite one.
- `Continuous.Product.prodPre` is the product of two s-finite measures (`∫-prod`, `∫-rect`); `Continuous.FinProd.prodⁿ` is the n-fold product.
- On a probability space, `Continuous.Independence.Indep` says the law of a tuple is the product of the laws (so `Ex-indep`, `Var-indep`
  follow), `Continuous.IID.IID` adds equal marginals, and `Continuous.Exchangeable.Exch` is invariance under swaps.
- `Continuous.CoinCoordsJoint.coins-iid`: the coordinates of the fair coin are iid.

## 4. Prove something generic

State your theorem over a record of the interface, then supply a model:

- `StatisticalInterface` (`QBS.Statistical`) is a record over a category with a `ProbabilityInterface`;
- the discrete instance is `discreteStatisticalQBSLike N` for a `NormalizableSemiring N` (`Model.Discrete`);
- the continuous one is `continuousStat` (`Continuous.SFiniteStat`).

Generic lemmas already available: `bind-sum` and `bind-scale` (`StatisticalLemmas`).

## 5. Signed expectations, Gaussians, information quantities

The integral above only takes values in `[0,∞]`. To talk about variance, bias or a log-likelihood ratio you need
signed values. The library does this in two steps.

**Signed values and tests.** A *signed test* on `X` (`Continuous.SignedTest`, type `SgT X`) is a pair of non-negative
tests `pos`, `neg` standing for `f⁺ − f⁻`. A signed value is `Sg` (`Analysis.Signed`): a difference of two finite
non-negative values. Only finite values are allowed there, since with `∞` the construction collapses. For values in
`(−∞, ∞]` there is a second type `Sg∞` (`Continuous.SignedInf`). It has addition but not negation, so there is no
`∞ − ∞`.

**Expectations.** `Ex p f i` (`Continuous.SignedExpect`) is the expectation of `f` against any s-finite measure `p`.
The argument `i : Int p f` says that both parts have finite integral. The value does not depend on `i` (`Ex-irr`).

```agda
-- from: src/QBS/Continuous/SignedFubini.agda
    Ex-⊗ : ∀ s t (f : SgT X) (g : SgT Y) (i : Int {X} s f) (j : Int {Y} t g) →
      Ex {XY} (prodPre {X} {Y} s t) (f ⊗T g) (Int-⊗ s t f g i j) ≃ Ex {X} s f i *S Ex {Y} t g j
```

That is independence: for a product measure the expectation of `f(x)·g(y)` is the product of the expectations.
Related modules:

| Need | Module |
|---|---|
| linearity, scaling, monotonicity, domination | `Continuous.SignedExpect` |
| push-forward along a map; bridge from the older `E-atᴵ` API | `Continuous.SignedTransport` |
| convergence, dominated convergence (`dct-Ex`), differentiation under the integral (`deriv-Ex`) | `Continuous.SignedLimits`, `DominatedSigned` |
| unsigned monotone and dominated convergence (`mct-conv`, `dct`), Fatou's lemma (`fatou`, `rev-fatou`) | `Continuous.Dominated`, `Continuous.Fatou` |
| Fubini for signed tests | `Continuous.SignedFubini` |
| the logarithm as a signed value (`log-mul`) | `Continuous.SignedLog` |

**Gaussians.** The real line is two half-lines, `RQ = WQ +Q WQ` (`Continuous.RealLine`). The standard Gaussian
is built from its density `e^{−x²/2}` and a normaliser `Z`, an abstract inverse of the integral. No value for π
is needed. Results:

- `Inference.GaussReal`: the standard Gaussian, with `E[X] ≃ 0` and `E[X²] ≃ 1`.
- `Inference.GaussScale`, `GaussShift`, `GaussAffine`: N(0, s²), N(μ, s²) and `μ + σx`, with the mean.
- `Inference.GaussVar`: the variance of N(μ, s²) under the measure itself.

```agda
-- from: src/QBS/Inference/GaussVar.agda
    Var-gaussμ : Var (gaussμ s l sl sB lB μ μB) idT (Int-id , Int-sq) ≃ ι (Is-* sB sB)
```

The parameters are finite `s`, its inverse `l` (`s l ≈ 1`) and a finite `μ`. The half-normal is in
`Inference.HalfNormal`.

**Variance, entropy, KL divergence.** `Continuous.SignedVar` defines `Var f = E[f²] − (E f)²` for a probability
distribution, and proves the centred form. `Continuous.Entropy` and `Continuous.KLDiv` use *densities*: a distribution
with density `p` against a base measure `Q` is `densPre Q p`, and no Radon–Nikodym theory is needed. KL values live in
`(−∞, ∞]`.

```agda
-- from: src/QBS/Continuous/KLDiv.agda
    KL-nonneg : ∀ p (i : KLInt p) → ∫ᴹ {X} Q (constW {X} 1#) ≈ 1# → ∫ᴹ {X} Q p ≈ 1# → fromPos 0# ≤∞ KL p i
```

This is Gibbs' inequality: `KL ≥ 0` when `Q` and `p·Q` are probabilities. `Continuous.InfoProduct` proves that KL
divergence and entropy add over independent products (`KL-⊗`, `Ent-⊗`), for normalised, positive, finite densities.

**Exponential families, random vectors and sample estimators.** `Continuous.ExpFamily` builds the natural exponential
family with base measure `h` and statistics `T` as `h` reweighted by `e^{⟨η, T⟩}`, normalised by the partition function
`Z(η)`; `Continuous.ExpFamilyPost` proves conjugate updating: the prior `priorPre (χ, ν)` reweighted by the likelihood of
`N` observations with summed statistic `ΣT` is `priorPre (χ + ΣT, ν + N)`. `Continuous.RandomVector` gives mean vectors
and covariance matrices of square-integrable signed tests, with `Cov (A X + b) = A Cov(X) Aᵀ`, and `Continuous.SgSample`
proves that the sample mean and the sample variance are unbiased.

## 6. Estimators and inference

- **Where to start** : Bayes' rule is `Inference.CoinPosterior`
  (`posterior`, `bayes`) and `Example.Bayes`; conjugacy for exponential families is `Inference.ExpFamily` (discrete) and
  `Continuous.ExpFamilyPost` (continuous); `Inference.CondIID` and `CondIIDCoin` give conditionally iid observations;
  `Inference.IIDLaw` and `WeakLaw` give the moments of iid sums, Chebyshev and the weak law of large numbers.
- **Frequentist** (`Inference.Frequentist`): an `Experiment Θ` gives observations for each parameter; a statistic is a
  ring term in them; `bias`, `variance` and `mse` use the signed expectation. `sample-mean-unbiased` and
  `sample-variance-unbiased` hold generically. `Inference.UniformExperiment` and `Inference.Sampler`
  (`UniformSampler`) are instances. Everything is division-free: unbiasedness is stated as `E t = k τ`.
- **Bayesian** (`Inference.Bayesian`, discrete): sequential updating, evidence, exchangeability for the Bernoulli
  model. `Inference.CoinBias` is a worked example with numbers.
- **Continuous posteriors**: `Inference.CoinUniformPrior` and `CoinPosterior` (a coin with a uniform prior on θ).
- **Both views on one model**: `Inference.BernoulliCompare`, and the Bayes risk of two estimators in
  `Inference.CoinBayesRisk`.

## 7. Not available yet

| Missing | Notes |
|---|---|
| Random vectors: finite products `Xⁿ` as one space, mean vectors, covariance, Gaussian vectors | proposed in `plans/03-bayesian-frequentist.md`, "Directions"; not started |
| Fisher information | needs derivatives beyond the difference quotients of `SignedLimits.deriv-Ex` |
| KL between Gaussians, differential entropy of a Gaussian | the first needs `exp` of a signed argument on `RQ`, the second needs a value for π |
| Data-processing inequality, conditional KL | need disintegration |
| Value of π, the closed form of the Gaussian normaliser | the library works with an abstract inverse of `Z` |
| Sub-probability measures in Riesz, `restrictM` as a morphism | see [TODO.md](../TODO.md) |
| Constructive foundations | removing `lem`: [ConstructiveLit.md](ConstructiveLit.md) |
