# Public interface

The names a user imports, with the module they live in and one line of meaning. Types are shown where short; open the
module for the rest. `scripts/doccheck.py` verifies that every module path below exists and every name still
occurs in it. Conventions: `ℓ` universe level, `S` a `RandomSource`, `Hom S X Y` morphisms in `QBSCat S`.

## Abstract layer

### `QBS.Core`
- `idH` — `idH S {X}`: the identity morphism (`S` explicit).
- `RandomSource` — the sample space "reals" with measurable endomorphisms and partitions `R → ℕ`, assembled from `Measurability` (a setoid `Rˢ` with carrier `R` and equality `≈ᴿ`, `Meas`, its closure, and `meas-resp`: measurable maps respect `≈ᴿ`), `Partitions` (`Idx`, `idx-resp`, gluing) and `NatPairing` (`pair`/`unpair`) plus `idx-glue`; their fields are re-exported.
- `QBS` — a quasi-Borel space: a setoid `Carrier` with `Random` elements `R → X`, closed under constants, precomposition, gluing, and respecting `≈ᴿ` (`random-cong`). The core never assumes `≡` on `R`: each source chooses its equality.
- `Hom` — a setoid map `map` preserving random elements (`map-random`).

### `QBS.Category`, `QBS.Limits`, `QBS.Colimits`, `QBS.Complete`, `QBS.Exponential`
- `QBSCat` — `QBSCat S`, the category (agda-categories `Category`).
- `QBS.Exponential`: `cartesianClosed` — `CartesianClosed (QBSCat S)`; `QBS.Limits`: terminal object and products; `QBS.Colimits`: coproducts.
- `QBS.Complete`: `countableProduct`, `countableCoproduct` — indexed products and coproducts.

### `QBS.Probes`
- `ℛQ` — the probe object, the space of random sources; random elements of `X` correspond to morphisms `ℛQ ⇒ X`.

### `QBS.Probability`
- `ProbabilityInterface` — an abstract commutative strong monad of probability measures over a cartesian closed category with probe object `ℛ`, assembled from the monad (`ProbMonad`), `ProbLaws` and `Fubini` (fields re-exported).
- `Measure` — the type of probability measures on `ℛ`; `measure μ : ⊤ ⇒ T ℛ` embeds a measure as a global element of the monad, and `law a μ = T a ∘ measure μ : ⊤ ⇒ T X` (derived) is the distribution of a probe `a : ℛ ⇒ X` under `μ`.
- `measure-push` (pushforward is `T m`), `measure-total` (mass one), `law-surjective` — the axioms linking measures to the monad; `law-resp`, `law-map`, `law-pre`, `law-return` are derived from them; `split`, `tensor`, `measure-tensor` (`T split.from ∘ measure (tensor μ ν) ≈ ψ ∘ ⟨measure μ, measure ν⟩`, with `ψ` the monoidal structure of the commutative monad) — the Fubini axiom; `kernel`, `kernel-law`, `law-join` are derived from it.

### `QBS.Statistical`
`StatisticalInterface` on top of a `ProbabilityInterface`, assembled from five small structures (their fields are re-exported, so `open StatisticalInterface St` still gives every name), plus `scaled-laws` (every measure is a countable sum of scaled laws):
- `CommutativeMonoidWithZero` (`weights`): `W`, `mulW`, `oneW`, `zero⇒`, and `mul-assoc`, `mul-comm`, `mul-one`, `mul-zero`.
- `SubMonad` (`measures`): `commutativeMonad` (the measure monad `M`), `inclusion` (Prob into `M`), `inclusion-strong`.
- `Score` (`scoring`): `zero` (zero measure), `score : W ⇒ M 1`, `score-zero`, `score-one`, `score-mul`, `zero-bind`.  It *defines* `scaleM a t = μ ∘ M t ∘ score ∘ a` and proves `scale-one`, `scale-mul`, `scale-return`, `scale-nat`, `scale-join`.
- `CountableSums` (`sums`): `sumK` (sums of kernels), `sumK-point`, `bind-sumK`, `sum-nat`, `sum-join`; `sumM` is `sumK` on global measures.  `scale-sum` is derived from `bind-sumK`.
- `Normalization` (`normalization`): `normalize : ∀ X → M X ⇒ Prob X + 1`, `normalize-prob`, `normalize-zero`, `normalize-scale`.

### `QBS.StatisticalLemmas`
- `bind-sum`, `bind-scale` — bind preserves countable sums and scaling of the measure argument.

### `QBS.IsQBSLike`, `QBS.IsStatisticalQBSLike`, `QBS.Instance`
- `IsQBSLike`, `IsStatisticalQBSLike` — the minimal structure for probability, resp. soft conditioning.
- `isQBSLike S P`, `isStatisticalQBSLike S P St` — package any random source with a (hypothesised) monad.

## Discrete model

### `QBS.Model.Semiring`
- `CompleteSemiring` — a commutative semiring with countable sums `∑` (fields `_+_`, `_*_`, `0#`, `1#`, `∑`).
- `NormalizableSemiring` — a complete semiring with inverses for normalisation (`complete` is the underlying semiring).

### `QBS.Model.Monad`
- `Measures` — `module Measures A K`: measures over `A` of weight class `K`.
- `Pre` — a discrete pre-measure: probe `α`, weights `μ`, proof `μ-ok`; `mk` builds one.
- `∫` — `∫ p f`: the expectation `∑ r. μ r * f (α r)`.
- `ηPre`, `mapPre`, `joinPre`, `∫-η`, `∫-join` — unit, map, join and their integral rules.

### `QBS.Model.WeightClasses`
- `probClass`, `allClass` — total mass 1 / arbitrary weights; `QBS.Model.SubProb`: `subClass` — total mass ≤ 1.

### `QBS.Model.Discrete`, `QBS.Model.StatInstance`
- `discreteStatisticalQBSLike` — `NormalizableSemiring → IsStatisticalQBSLike`, the discrete model.
- `discreteStat` (`StatInstance`) — its `StatisticalInterface`, with `normalize`.

### Concrete semirings: `QBS.Model.BoolSemiring`, `QBS.Model.ViterbiSemiring`, `QBS.Model.AdditiveSemiring`, `QBS.Model.AdditiveModel`, `QBS.Model.BoolModel`, `QBS.Model.ViterbiModel`
- `boolComplete`, `additiveComplete`, `additiveNormalizable` — complete / normalisable semirings (Boolean, additive `[0,∞]`); models `QBS.Model.BoolModel`, `ViterbiModel`, `AdditiveModel` (`additiveStatisticalQBSLike`).

## Continuous model

### `QBS.Borel.Source`
- `cantorSource` — Cantor space `2^ℕ` as a `RandomSource`.

### `QBS.Continuous.Sample`, `QBS.Analysis.CoinIntegral`, `QBS.Analysis.Omega`
- `UnitInterval` (`Sample`) — `module UnitInterval A`: the unit interval as a QBS `AQ`; `S` — the Cantor random source used by the continuous model.
- `lemOf` (`CoinIntegral`) — turns `lem₁` into the `lem` the lower-cut construction needs; `LowerRealsOmega (lemOf lem₁)` is the value semiring.
- `OmegaSemiring` (`Omega`) — the value-semiring record (`_≈_`, `1#`, order, suprema).

### `QBS.Analysis.Measure`, `QBS.Analysis.Fun`
- `Integration` (`Measure`) — `module Integration A`: `probClass` (probability measures of the continuous model; not the discrete `WeightClasses.probClass`).
- `Measure` — a sub-probability measure as a Daniell functional on measurable functions; `IsProb` — total mass 1.
- `Fun` — the inductive class of measurable `[0,1]`-valued functions on Cantor space.

### `QBS.Analysis.CoinIntegral`, `QBS.Continuous.FairCoin`
- `fairCoin` — the fair-coin measure on Cantor space; `fairCoin-cyl` — its value on cylinders.

### `QBS.Analysis.Meas`, `QBS.Analysis.Lebesgue`
- `Meas` — threshold measurability of `[0,∞]`-valued functions; `Lebesgue`: `J m φ` — the integral of a `Meas` function (unbounded).

### `QBS.Analysis.Signed`, `QBS.Analysis.SignedOmega`, `QBS.Analysis.SignedIntegral`, `QBS.Analysis.Variance`
Signed values and signed integrals (plan 2, step 1). No cancellation or classical principle in `Signed`.
- `SubSemiring` (`Signed`) — a subsemiring of "finite" elements; `Signed` — `module Signed R F`: the ring of differences of finite elements (Grothendieck construction).
- `Sg` — a signed value `pos − neg` with finite parts; `_≃_` equality (`p + n′ + k ≈ p′ + n + k` for finite `k`); `_+S_`, `_*S_`, `-S_`, `0S`, `1S`, `ι` (embedding), `signedRing` (a `CommutativeRing`), `ι-+`, `ι-*`.
- `Bounded` (`SignedOmega`) — `module Bounded A`: finite = bounded by a natural number (`Bnd`, `nat`); re-exports `Signed` at that subsemiring.
- `Var pm f b`, `var-formula` (`Variance`) — variance `E[(f−E f)²]` of a bounded signed function, and `Var f ≃ E[f²] − (E f)²` (`_*SF_[_]` multiplies bounded signed functions).
- `SF m` (`SignedIntegral`) — a signed integrable function against `m`: measurable parts `f⁺`, `f⁻` with bounded integrals; `E` — its signed integral; `_≈SF_`, `E-cong`.
- `_+SF_`, `E-+` — sum and additivity; `-SF_`, `E-neg`; `scaleSF`, `E-scale` — scaling by a signed constant; `constSF`, `E-const`, `J-const` — constants against a probability measure.

### `QBS.Continuous.Monad`, `QBS.Continuous.ProbInstance`, `QBS.Continuous.SubProb`, `QBS.Continuous.RealModel`
- `Continuous` (`Monad`) — `module Continuous A lem K` (value semiring, `lem`, measure class such as `Integration.probClass`): the probability monad: `Pre`, `mk`, `∫`, `joinPre`, `∫-join`.
- `ContinuousProb` (`ProbInstance`) — it is a `ProbabilityInterface`; `continuousQBSLike`; `RealModel`: `realQBSLike`.
- `ContinuousSub` (`SubProb`) — the sub-probability monad; `scoreH` — soft conditioning by a measurable likelihood in `[0,1]`.

### `QBS.Continuous.SFinite`, `QBS.Continuous.SFiniteStat`
- `∫ᴹ`, `_≈ᴹ_` (`SFinite`) — weighted integral and equality of s-finite measures.
- `continuousStat` (`SFiniteStat`, `module SFiniteStat lem`) — the complete `StatisticalInterface` for the continuous model.

### Distributions: `QBS.Continuous.Uniform`, `QBS.Continuous.UniformMean`, `QBS.Continuous.UniformMoment`, `QBS.Continuous.UniformVariance`, `QBS.Continuous.UniformCDF`, `QBS.Continuous.SubModel`
- `uniformSub` (`QBS.Continuous.SubModel`), `cdfTest` (`UniformCDF`) — the sub-probability form of `uniform` and the CDF's test function.
- `uniform` — `U[0,1]` as a `Pre AQ` (`module Uniform lem₁`).
- `mean` — `E[u] = ½`; `cdf` — `P(u ≤ t) = t` (`module UniformMean lem₁`, `UniformCDF`).
- `second-moment` — `E[u²] = ⅓`, stated as `m + m + m ≈ 1` for `m = I fairCoin (u·u)` (`module UniformMoment lem₁`).
- `variance` — `Var u = 1/12`, stated as `x12 (Var u) ≃ 1S` (twelve copies sum to one; `module UniformVariance lem₁`).

## Examples and generic calculations

### `QBS.Example.Program`
- `Programs` — `Prog`, `pure`, `_>>=_`, `_>>_`, `test`, `∫-pure`, `∫-bind` for `do`-notation programs.
- `Flip` — `flip`, `∫-flip`, `∫-flip->>=`, `both`, `∫-both`; `BoolDemo` — the Boolean instance.

### `QBS.Example.Recipes`, `QBS.Example.Conditioning`, `QBS.Example.HardConditioning`, `QBS.Example.Bayes`, `QBS.Example.Probability`
- `reject`, `guard`, `∫-guard` — rejection in programs.
- `condition`, `∫-condition`, `condition-split` — conditioning as a measure transformer; total expectation.
- `posteriorU`, `evidence`, `posterior`, `bayes` — Bayes' rule.
- `isTrue`, `flip-mean`, `UniformSetup` (`QBS.Example.Recipes`) — checked copy-and-paste set-ups: the Bernoulli coin (module `Bernoulli`) and the uniform distribution (`uniform`, `∫`, `AQ`, `half` in scope).
- `Calculation` — `both-true`, `both-mass`: real-valued probabilities; `Additive` — its additive `[0,∞]` instance.
