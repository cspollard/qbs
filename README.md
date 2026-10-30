# Quasi-Borel spaces

An extrinsic formalisation of the category **QBS** (Heunen, Kammar, Staton, Yang,
[*A Convenient Category for Higher-Order Probability Theory*](https://arxiv.org/abs/1701.02547)).

## Documentation

| Read | For |
|---|---|
| [docs/Guide.md](docs/Guide.md) | task-oriented tour: which model to use, write a program, condition, continuous integrals, what is missing |
| [docs/Interface.md](docs/Interface.md) | the public names, by module, with one-line meanings |
| [docs/Architecture.md](docs/Architecture.md) | layers, dependencies, hypotheses, compile time, where to add things |
| [docs/Modules.md](docs/Modules.md) | one line for each of the 124 modules (generated) |
| [docs/Classical.md](docs/Classical.md), [docs/ConstructiveLit.md](docs/ConstructiveLit.md) | where `lem`/`funext` are used; literature for a constructive version |
| [plans/](plans/) | plans: documentation, uniform-distribution moments and estimators, Bayesian and frequentist inference |
| [TODO.md](TODO.md) | open work |

`make doccheck` keeps these in step with the code (header comments, module index, excerpts, listed names).
The sections below are the construction history, layer by layer.

## Library

`qbs.agda-lib` (name `qbs`, depends on `standard-library` and `agda-categories`; sources in `src/`, modules
`QBS.*`). To use it, add the path of `qbs.agda-lib` to `~/.agda/libraries` and `qbs` to your own `.agda-lib`
dependencies. File paths below are relative to `src/QBS/`.

## Map

| Layer | Where | What |
|---|---|---|
| Abstract | `Core` … `Instance`, `Statistical`, `IsStatisticalQBSLike` | QBS as a category (complete, cocomplete, cartesian closed); `IsQBSLike` / `IsStatisticalQBSLike`: the minimal structure for probability and soft conditioning, with a probability monad as a hypothesis |
| Discrete model | `Model/` | measures as weighted countable families over a complete semiring (Boolean, Viterbi, `ℕ∞`, additive `[0,∞]`), probability and sub-probability classes, the statistical instance with `normalize` |
| Continuous model | `Borel/`, `Analysis/`, `Continuous/` | Cantor space as the random source; measures as Daniell functionals on measurable functions; the fair coin, independence of even/odd bits, the uniform distribution, sub-probability monad with scoring and restriction; Riesz round trips; integration of unbounded `[0,∞]`-valued functions by dyadic truncation (`Analysis/Unbounded`) |
| Programs | `Example/` | `do`-notation programs, conditioning (`guard`, `condition`), Bayes' rule, real probabilities |

Start with the discrete model and `Example/Program.agda` for a working probabilistic program, or with
"The fair-coin measure" for the continuous construction.

- `Core.agda` – `RandomSource S` (the "reals": a type `R`, measurable maps `R → R`, measurable
  countable partitions `R → ℕ`, kept abstract but with the closure laws the constructions
  use), `QBS S` (a *setoid* with random elements `R → X` respecting its equality), `Hom`
  (setoid maps preserving random elements), identity and composition.
- `Category.agda` – `QBSCat S`, an `agda-categories` `Category` (morphisms equal when
  pointwise equal).
- `Limits.agda` – terminal object, binary products, equalizers: `FinitelyComplete (QBSCat S)`.
- `Colimits.agda` – initial object, binary coproducts, coequalizers (the carrier is the
  equivalence closure of the generating relation): `FinitelyCocomplete (QBSCat S)`.
- `Complete.agda` – indexed products and coproducts over any `I : Set ℓ`; with equalizers and
  coequalizers the library's constructions give `Complete ℓ ℓ ℓ` and `Cocomplete ℓ ℓ ℓ`
  (all small limits and colimits).
- `Exponential.agda` – `Y^X` (random elements are the maps `R → Y^X` that uncurry to a
  morphism `ℛ × X ⇒ Y`), and the canonical `CartesianClosed (QBSCat S)`. No `R ≅ R × R`
  split is needed.
- `Probes.agda` – the space `ℛQ` of random sources, and the correspondence between random
  elements and probes `ℛQ ⇒ X`.
- `Probability.agda` – `ProbabilityInterface`, an *abstract* probability monad over a cartesian
  closed category with a probe object `ℛ`: a commutative strong monad; probability measures on
  `ℛ`; `law a μ`, the distribution of a probe, as a global element of the monad, with
  naturality/return/surjectivity axioms; and the bind (Fubini) axioms over a splitting
  `ℛ ≅ ℛ × ℛ` with a product of measures. Stated with the terminal object, not a forgetful functor.
- `IsQBSLike.agda` – the minimal structure for doing probability the QBS way: a probe object `ℛ`,
  cartesian closure, binary and countable coproducts, countable products, and a
  `ProbabilityInterface`.
- `Instance.agda` – `isQBSLike S : ProbabilityInterface … → IsQBSLike ℓ (QBSCat S)`, for every
  random source `S`. The probability monad is a hypothesis until a concrete one exists.

- `Statistical.agda` – `StatisticalInterface`, abstract soft conditioning on top of a
  `ProbabilityInterface`: a commutative monoid object `W` of weights (absorbing zero); a
  commutative strong measure monad `M` with a strong monad morphism `Prob ⇒ M`; a zero measure on `1` (not on every space: a measure on an empty space has no probe); `score : W ⇒ M 1`,
  multiplicative, with weight 0 the zero measure; countable sums and scaling of global
  elements of `M` (every measure is a countable sum of scaled laws, i.e. s-finite); and
  `normalize : M X ⇒ Prob X + 1`, homogeneous under invertible weights.
- `StatisticalLemmas.agda` – bind is linear in the measure argument: it preserves countable sums
  (`bind-sum`) and scaling (`bind-scale`).
  `StatisticalInterface` also has countable sums of kernels `sumK` (pointwise sums of measures) with
  `sumK-point` and the axiom `bind-sumK` (bind is linear in the kernel); `discreteStat` proves them by
  gluing the random-family witnesses through the Cantor pairing (`sumKH`).
- `IsStatisticalQBSLike.agda` – `IsQBSLike` plus a `StatisticalInterface`.
- `Instance.agda` also has `isStatisticalQBSLike S` (the measure monad is again a hypothesis).

`QBSCat S` has more than `IsQBSLike` asks for: equalizers, coequalizers, an initial object,
and all small limits and colimits (`Limits`, `Colimits`, `Complete`). They are theorems about
`QBSCat S`, not requirements, since probability does not need them.

All files check under `--safe --without-K`, with no postulates.

## Towards a concrete model (`Model/`)

- `Model/Pairing.agda` – Cantor's pairing function `ℕ × ℕ ≅ ℕ`, with `unpair-pair` and
  `pair-unpair` proved (the standard library has none); this is what `RandomSource.pair` needs.
- `Model/DiscreteSource.agda` – the discrete random source `R = ℕ`, every function measurable.
  QBS over it are sets with a σ-ideal of countable subsets, and probability on them is
  countable-support probability, so it is the first concrete model to validate the interfaces.
- `Model/Semiring.agda` – complete commutative semirings (Golan): sums over arbitrary index sets,
  associative over partitions, distributive. Measures will take values in an arbitrary one
  (the extended non-negative reals are the motivating example), so the discrete model needs no
  construction of ℝ.

- `Model/Sums.agda` – derived sum algebra: additivity, Tonelli-style swapping, push-forward of
  weights along a function, Dirac masses.
- `Model/Monad.agda` – the measure monad on QBS over the discrete source, for a class of admissible
  weights (`WeightClass`). A measure is `[α, μ]` (a random element and a weight function) up to
  equal integrals against every test function `X → A`, the equivalent form of HKSV's push-forward
  equality that needs no quotients. `TM : Monad (QBSCat S)`.
- `Model/Strong.agda` – its strength and commutativity (Fubini for double sums).
- `Model/WeightClasses.agda` – probability measures (total mass 1) and all measures.
- `Model/ProbInstance.agda` – `discreteProb A : ProbabilityInterface …` for every complete
  semiring `A`: the first concrete model of the probability interface, so its axioms (law,
  push-forward, return, surjectivity, the splitting `ℛ ≅ ℛ × ℛ`, `tensor`, `kernel`, Fubini bind)
  are consistent.

- `Model/Cantor.agda` – reindexing sums over `R = ℕ` through the Cantor pairing.
- `Model/SubProb.agda` – the weight class `subClass A` of sub-probability measures (`∑ μ + d ≈ 1`). Since
  `Model/Monad.agda` is generic in the weight class, `Sub = Measures A subClass` is a monad of
  sub-probability measures, and `SubStrength = Strength A subClass` its strength and commutativity,
  with no further proofs.
- `Model/BoolSemiring.agda`, `Model/BoolModel.agda` – the Boolean semiring `({false,true}, ∨, ∧)` as a
  `NormalizableSemiring` (sums are classically decided `∃`), and the resulting concrete
  `IsStatisticalQBSLike`: possibilistic weights. Degenerate but non-vacuous.
- `Analysis/CutSum.agda` – sums of lower cuts over an arbitrary `I : Set₁`. `Mem f q` is an inductive
  predicate (no lists) saying that `q` is below a finite sum of members of `f i` over *distinct*
  indices: a step picks `i` and `r ∈ f i` and continues with any `g` below `f` away from `i` and below
  zero at `i`. With classical `lem₁` the sum cut `sumC f` is `Mem` resized to `Set`; the file proves
  the `CompleteSemiring` laws about it: empty, unit, disjoint unions (`Sum.split`, `Sum.join`),
  reindexing along a bijection (`Reindex.reidx`), `sum-distribˡ` (multiplication distributes over
  sums) and partition associativity `sum-Σ` (via `row-add`, `split1`, `nested⇒flat`,
  `flat⇒nested`). Excluded middle for `Set₁` also gives decidable equality and hence proof-irrelevant
  identity (`uip`), which is what makes pairs `(i , j)` injective in `j` without axiom K.
- `Model/AdditiveSemiring.agda`, `Model/AdditiveModel.agda` – `([0,∞], +, ×)` as a
  `NormalizableSemiring` (`additiveNormalizable`: `invertible?` is just `lem₁`) and the resulting
  `additiveStatisticalQBSLike`: the discrete statistical model with ordinary additive real weights.
- `Model/ViterbiSemiring.agda`, `Model/ViterbiModel.agda` – the Viterbi semiring `([0,∞], max, ×)` on
  lower cuts as a `NormalizableSemiring` (sums are unions, classically resized with `lem` at
  `Set₁`; weights are real and invertibility is non-trivial), and the resulting
  `IsStatisticalQBSLike`: best-path weights, not additive probability.
- `Model/StatInstance.agda` – `discreteStat N : StatisticalInterface …` for every normalisable
  complete semiring `N`: weights object, strong inclusion `Prob ⊆ M`, `zero`, `score`, scaling,
  countable sums, `scaled-laws`, and `normalize : M X ⇒ Prob X + 1`
  (case analysis on invertibility of the mass, which is a classical decision, hence the field
  `NormalizableSemiring.invertible?`).
- `Model/Discrete.agda` – `discreteStatisticalQBSLike N : IsStatisticalQBSLike ℓ (QBSCat (discreteSource ℓ))`
  with no remaining hypotheses on the monads: the discrete model validates every axiom of both interfaces.

Building the model exposed a bug in `StatisticalInterface`, fixed above: a zero measure cannot
exist on an empty space (a measure needs a probe into it), so `zero` is asked for at `1` only.
The semiring also had to be nontrivial (`0 ≠ 1`) for `normalize` of the zero measure to fail.

## Borel structure on Cantor space (`Borel/`)

- `Borel/Core.agda` – the Borel σ-algebra on Cantor space `2^ℕ`, inductively generated by the sets
  `{x | x n = b}` (closed under complement, countable union and intersection, and pointwise
  logical equivalence, so no classical logic or extensionality is needed); measurable maps,
  preimages, composition, constants, countable measurable partitions and gluing.
- `Borel/Source.agda` – `cantorSource : RandomSource 1ℓ`: every `RandomSource` axiom (including
  gluing along measurable partitions through the Cantor pairing) holds for the Borel structure.
- `Borel/Category.agda` – the category of quasi-Borel spaces over it, with completeness,
  cocompleteness and cartesian closure obtained from the general theorems.

- `Borel/Measure.agda` – measures on the Borel σ-algebra, valued in a complete semiring: a
  σ-additive map on Borel sets, independent of the derivation of the set (`Borel` is proof-relevant);
  push-forward along measurable maps, with its functoriality.

So `QBSCat cantorSource` is the category of quasi-Borel spaces of HKSV (Def. 7; by their remark
after Def. 11 any uncountable standard Borel space serves as the sample space), and all the
constructions above apply to it.

The continuous model built on this source is described under *Continuous model* below.

## Analysis on Cantor space (`Analysis/`)

The measure theory for a continuous model, in the functional (Daniell) form, so the Giry-monad
operations are plain composition and no extension theorem is needed to build them.

- `Analysis/Omega.agda` – `OmegaSemiring`: values for measures. A commutative semiring with a
  compatible partial order (an abstract field, so no subtraction is needed in general), suprema of
  increasing sequences preserved by `+` and `×`, cancellation of elements `≤ 1`, and complements
  below 1 (`c ≤ 1 ⇒ ∃ d, c + d = 1`). The extended non-negative reals are the intended instance.
- `Analysis/LowerReals.agda` – `[0,∞]` as lower cuts of the rationals (`LowerRealsOmega lem`): a
  non-degenerate `OmegaSemiring`. Order is inclusion, suprema are unions, `+` and `×` are the usual
  cut operations (`0·∞ = 0` falls out), and `lem` is used for the near-supremum lemma behind
  complements below 1 and cancellation (Archimedean property of `ℚ`). `Analysis/RationalLemmas.agda`
  collects the ordered-field facts about the unnormalised rationals, without instance arguments.
  `Continuous/RealModel.agda` instantiates the continuous model with it (`realQBSLike`).
- `Analysis/ExtNat.agda` – the extended naturals `ℕ∞` as an `OmegaSemiring` (suprema of chains via `lem`).
  A degenerate instance (probability measures are `{0,1}`-valued) that shows the hypotheses are
  satisfiable; `Continuous/ExtNatModel.agda` instantiates the whole continuous model with it. Note
  that idempotent semirings such as `{0,1}` are *not* instances: cancellation below 1 fails.
- `Analysis/Series.agda` – countable sums `∑ᶠ a = ⨆ (psum a)` in any `OmegaSemiring` (module `Series A`):
  congruence, monotonicity, `∑ᶠ-+`, `∑ᶠ-scale`, `∑ᶠ-shift`, `∑ᶠ-single`, and Tonelli: `∑ᶠ-swap`
  (iterated sums commute) and `∑ᶠ-pair` (an iterated sum is the sum along the Cantor enumeration).
  The enumeration comparison is a counting argument by peeling off one index at a time with masks.
- `Analysis/Fun.agda` – measurable `[0,1]`-valued functions on Cantor space: the class generated from
  weighted Borel indicators by sums, increasing suprema and complements `1 - h`, with every constructor
  relational (no membership decisions). Closure under precomposition with measurable maps, restriction
  to a decidable Borel set, and gluing along a measurable countable partition.
- `Analysis/Measure.agda` – a (sub-probability) measure is an integration functional on those functions:
  monotone, additive, homogeneous, continuous along increasing sequences, of mass `I 1 ≤ 1`
  (`IsProb`: mass exactly 1). Dirac, push-forward and bind (for a kernel whose integrals are
  measurable) are defined by composition, and preserve `IsProb`. A `MeasureClass` (`probClass`,
  `subClass`) is a predicate on measures closed under those operations; the continuous monad is
  parametrised by it, as the discrete one is by its weight class. The analysis below
  (`Indicators`, `Param`, `Uniqueness`, `Tensor`) works for sub-probability measures: complements use
  the defect `1 − mass`, and uniqueness / Fubini compare measures of equal mass.

- `Borel/PiLambda.agda` – Dynkin's π–λ theorem for the Borel sets of Cantor space (classical: a `lem`
  parameter): any class containing finite cylinder intersections and closed under complement and
  countable disjoint unions contains every Borel set.
- `Borel/Merge.agda` – bit interleaving `merge`, measurability of its sections, and the decomposition of a
  finite cylinder as a rectangle `C₁ × C₂` (no function extensionality needed).
- `Analysis/Indicators.agda` – classical indicator functions; the measure of a disjoint union is the
  supremum of the partial sums.
- `Analysis/Uniqueness.agda` – two probability measures agreeing on the finite cylinders agree on every
  measurable function.
- `Analysis/Param.agda` – parametric measurability: for a kernel `g`, `r ↦ ∫ g(r)(s ↦ h(merge r s))`
  is measurable (Dynkin on sets with rectangles as the base case, then induction on `h`).
- `Analysis/Tensor.agda` – the product of two measures, integrated in either order, and **Fubini's
  theorem**: the two iterated integrals agree (both are Daniell functionals agreeing on rectangles).

## Continuous model (`Continuous/`)

The probability monad of `QBSCat cantorSource`, parametrised by an `OmegaSemiring`, a classical
`lem`, and (only for the splitting isomorphism `ℛ ≅ ℛ × ℛ`) function extensionality.

- `Continuous/Sample.agda` – bit splitting `evens`/`odds`, the isomorphism `fromH`/`toH`, and the
  unit interval `𝕀` as a QBS whose random elements are the measurable `[0,1]`-valued functions.
- `Continuous/Monad.agda` – `Pre X`: a probe with a Daniell measure on `ℛ`, identified when all
  integrals of test functions `X ⇒ 𝕀` agree. Random families of measures are those given by a joint
  probe and a measurable kernel. Functor, `η`, `μ` (join via interleaving + parametric
  measurability) and all monad laws.
- `Continuous/Strong.agda` – strength and **commutativity**, the latter by Fubini.
- `Continuous/ProbInstance.agda` – `continuousProb : ProbabilityInterface`, with
  `tensor = tensor₁`, and `continuousQBSLike : IsQBSLike`.

## The fair-coin measure (`Analysis/`, `Continuous/FairCoin.agda`)

A `Measure` (Daniell functional on all `Fun h`, values in `[0,∞]` as lower cuts of ℚ) with `I(χ_C) = 2⁻ⁿ`
on every finite cylinder C of length n; by `Uniqueness.agda` it is the only one. Classical
throughout: one parameter `lem₁ : (P : Set₁) → P ⊎ ¬P`. The pipeline (Carathéodory extension of the
dyadic premeasure by compactness, then a Lebesgue-style integral from simple functions):

Stage 1, compactness and premeasure (no Arch assumptions except where noted):
- `Clopen.agda` – clopen sets as finite binary trees (`Cl`), Boolean semantics `eval`, `∪ ∩ ∁ᶜ`, and
  the **fan theorem** `Fan.fan`: a decreasing sequence of clopens with empty intersection is
  eventually empty (König's lemma by classical choice of a path).
- `Archimedean.agda` – `Arch A`: the structure of `[0,∞]` beyond `OmegaSemiring` that the extension
  needs (`half`, tolerances `hp n` with `hp (n+1)+hp (n+1) ≈ hp n`, Archimedean closure `arch`,
  order cancellation `cancel≤`, series tails `way-below`), and geometric-sum lemmas.
- `ClopenMeasure.agda` – the dyadic premeasure `μ0` on trees (modular, monotone, complements).
- `OpenMeasure.agda` – opens as increasing chains of clopens; `ν = ⨆ μ0`; compactness gives `ν`
  independent of presentation, monotone, modular, `ν-cover : O ∪ P = R ⇒ 1 ≤ ν O + ν P`,
  σ-subadditive unions `⋃ᵒ`, finite intersections `finI` with `ν-finI`.

Stage 2, Carathéodory by regular sets:
- `Regular.agda` – `Meas U m` (opens `O ⊇ U`, `P ⊇ Uᶜ` with `ν O ≤ m + 2⁻ⁿ`, `ν P + m ≤ 1 + 2⁻ⁿ`):
  unique values, clopen sets, complements and countable disjoint unions (`Union.meas-union`), hence by
  Dynkin every Borel set. Exports `μ`, `μ-meas`, `μ-unique`, `μ-resp`, `μ-compl`, `μ-⋃`, `μ-cyl`, `μ-≤1`.
- `LowerRealsArch.agda` – `lowerRealsArch lem : Arch (LowerRealsOmega lem)` (tolerances `2⁻ⁿ` as
  rational cuts; uses `near-sup` and `cancel-⊑` of `LowerReals`).
- `CoinSets.agda` – `CoinSets lem`: the fair-coin measure of Borel sets valued in lower cuts.

Stage 3, the integral:
- `CoinFacts.agda` – `μ-⊤`, `μ-⊥`, `μ-null`, `μ-part` (countable partitions), `μ-add`, `μ-mono`.
- `SeriesSup.agda` – countable sums commute with suprema of increasing sequences (`∑ᶠ-⨆`).
- `CoinCont.agda` – continuity from below `μ-cont` and completion `complete`/`∫-complete` of a partial
  simple function.
- `CoinSimple.agda` – simple functions `Sf` (countable Borel partitions with values in A), their
  integral `∫`, `∫-mono` (under any two partitions), `sadd`/`∫-sadd` (common refinement),
  `sconst`, `sscale`.
- `LevelSets.agda` – `LS`: the strict level sets `{x | q < h x}` of every `Fun h` are Borel.
- `CoinGrid.agda` – `rC` (rational cuts), `rC-add-⊑`, and the dyadic grid simple function `grid`
  of a function with Borel level sets: `grid-minor` (below h) and `grid-upper` (h below the next
  grid point).
- `CoinIntegral.agda` – `Daniell lem₁`: `L h` = supremum of `∫ s` over simple minorants `s` of `h`
  (resized to `Set` by the classical axiom at `Set₁`); `L-ub`, `L-lub`, `L-mono`, `L-cong`, `L-one`;
  `Add.L-add` (additivity, via grids and `Arch.arch`); `Scale.L-scale` (`L (c·h) ≈ c · L h` for every
  `c`: grids when `c` is bounded by a rational, vanishing of `h` when it is not); `SupLaw.L-sup`
  (monotone convergence, via grid cells, `μ-cont`, `∑ᶠ-⨆` and `complete`).

Result:
- `Continuous/FairCoin.agda` – `FairCoin.fairCoin : Measure` (fields from the lemmas above) and
  `fairCoin-cyl : I fairCoin (χ U) _ ≈ μ0 (tree of c)` for every finite cylinder `c : Cyl U`
  (`Ind.L-ind : L (χ U) ≈ μ bU`).

## Borel measures and the Daniell integral (`Analysis/BorelMeasure.agda`, `Analysis/Functional.agda`)

The coin-integral pipeline is generic in the Borel measure it integrates against. `BM.BorelMeasure`
(over `LowerRealsOmega lem`) is an abstract σ-additive probability set function: `μ`, `μ-resp`
(respects `≐`), `μ-⋃` (countable disjoint additivity as `∑ᶠ`), `μ-⊤ ≈ 1`, `μ-⊥ ≈ 0`; `coinBM` is the
fair coin. `CoinFacts` (`Facts lem B`), `CoinSimple` (`Simple lem B`), `CoinCont` (`Cont lem B`),
`CoinGrid` (`Grid lem B`) and `CoinIntegral` (`DaniellB lem₁ B`) take `B`; `Daniell lem₁` is
`DaniellB` at `coinBM`, so downstream modules are unchanged. `Functional.agda` gives
`functional : Measure` (the Lebesgue integral of `B`, a Daniell functional) with
`functional-ind : I functional (χ U) ≈ μ bU`; `Continuous/FairCoin.agda`'s `fairCoin` is `functional`
at `coinBM`. This is the direction set function → functional of the Riesz–Daniell correspondence; the
other direction (functional → set function) is `Indicators.I-⋃`. `Analysis/Riesz.agda` closes the
loop: `setFun m pm` (a probability functional restricted to indicators is a `BorelMeasure`),
`functional-setFun : I (functional (setFun m pm)) h f ≈ I m h f` for every measurable `f` (by the
uniqueness theorem), and `setFun-functional : μ (setFun (functional ν) _) bU ≈ μ ν bU`. Only
probability measures are covered; sub-probability measures would need `μ-⊤ ≤ 1` in `BorelMeasure`.

Performance note: `Daniell` no longer exports a `lem` alias; every module writes `lemOf lem₁`. Mixed
spellings of the same argument (`DaniellB.lem lem₁ B` against `lemOf lem₁`) made Agda eta-expand the
`OmegaSemiring` records when comparing the types of two measures: `Riesz.agda` took 70 minutes and
checks in 4 seconds with one spelling.

## Independence of the even and odd bits (`Analysis/Interleave.agda`, `Continuous/CoinIndep.agda`)

- `Interleave.agda` – `interleave t₁ t₂`, the clopen tree of `{merge a s | a ∈ t₁, s ∈ t₂}` (with the
  auxiliary `stutter`), `eval-interleave : eval (interleave t₁ t₂) (mergeC a s) ≡ eval t₁ a ∧ eval t₂ s`,
  and in `module Product`, `μ0-interleave : μ0 (interleave t₁ t₂) ≈ μ0 t₁ * μ0 t₂`.
- `CoinIndep.agda` – `indep-cyl` (the interleaved product of two fair coins and the fair coin agree on
  every finite cylinder, via `Tensor.lhs-cyl`, `fairCoin-cyl` and the two lemmas above) and
  `fairCoin-indep : I (tensor₁ fairCoin fairCoin) h f ≈ I fairCoin h f` for every measurable `f`
  (by `Uniqueness`): the even and odd bits of a fair coin are independent fair coins.

## Uniform distribution on [0,1] (`Analysis/BinaryExpansion.agda`, `Continuous/Uniform.agda`)

- `BinaryExpansion.agda` – given `half` with `half + half ≈ 1#`, the binary expansion
  `expansion r = ⨆ₙ Σ_{k<n} rₖ 2^{-(k+1)}` of a point of Cantor space is measurable (`Fun-expansion`:
  a `supF` of finite `sumF`s of weighted bit indicators) and `≤ 1`.
- `Uniform.agda` – `uniform : Pre AQ`, the fair coin pushed forward along the expansion probe: the
  uniform distribution on the unit interval as an element of the continuous probability monad.
- The CDF `P(u ≤ t) = t` for every `t ≤ 1` (`UniformCDF.cdf : ∫ uniformSub (cdfTest t) ≈ t`). Steps:
  `Analysis/Mixture.agda` (the mixture `½μ₁ + ½μ₂` is a measure), `Continuous/FirstBit.agda`
  (`firstBit-fun`: `∫h dμ = ½∫h(true::·)dμ + ½∫h(false::·)dμ` for the fair coin, by `Uniqueness`, since
  `cons b` pulls cylinders back to cylinders and `μ0` of a tree is the average of its children),
  `Analysis/ExpansionCons.agda` (`expansion (b :: r) = b/2 + expansion r/2`), `Analysis/Threshold.agda`
  (`{x | h x ≤ t}` is Borel for measurable `h`, hence `cdfTest t` is a morphism; `½` is comparable with
  every real), and `Analysis/SelfSimilar.agda`: in any `Arch` semiring, a monotone `F` with
  `F(½s) = ½Z(s) + ½F(s)` (`Z(s) ≤ F(0)`, `Z(0) = 0`), `F(½+½s) = ½F(s) + ½` and `F(1) = 1` is the
  identity (`F(0) = 0` follows; the fixed points contain 0, 1 and are closed under the two maps, so every
  `t` is squeezed between fixed points `2⁻ⁿ` apart). No dyadic numerals or null-set argument is needed.

## Moments and estimation for the uniform distribution

Signed values (`Analysis/Signed*`) give `E[u] = ½`, `E[u²] = ⅓` and `Var u = 1/12` (`Continuous/Uniform{Mean,Moment,Variance}`).
`Continuous/CoinCoords` takes the coordinates `coordᵢ x = evens (oddsⁱ x)` of the fair coin: each has the law of the coin
and any two are independent (`J-split` is `CoinIndep.fairCoin-indep` combined with `J-fubini`; `E-indep` is its signed form).
`Analysis/Estimator` is the generic estimator theorem over an abstract ring of random variables with an additive
expectation; `Analysis/BoundedRing` instantiates it with bounded signed functions (equality is pointwise equality of the
signed values; the ring laws are those of `Sg`, and `BoundedCancel` cancels bounded elements by halving). For the draws
`Xᵢ = u ∘ coordᵢ` and `Sₙ = X₀ + … + X_{n−1}`, `Continuous/UniformSample` proves, without division:
`E Sₙ + E Sₙ = n` (the sample mean is unbiased), `12 · Var Sₙ = n` (`Var x̄ = σ²/n`) and `12 · E (n Qₙ − Sₙ²) = n² − n`
(`Qₙ = ΣXᵢ²`; the sample variance `(n Qₙ − Sₙ²)/(n(n−1))` is unbiased).
`Continuous/UniformInterval` transfers this to `Yᵢ = a + c·Xᵢ` (the interval [a, a + c]) with `Estimator.Affine`
(`E Tₙ + E Tₙ = n(a + a + c)`, `12 · Var Tₙ = n c²`, `12 · E (n Qₙ − Tₙ²) = (n² − n) c²`).

## Worked example (`Example/Program.agda`)

Probabilistic programs in Agda's `do`-notation on the discrete model, generic in the weight
semiring (`module Programs (A : CompleteSemiring zero)`): `Prog T` (a countable-support measure on
Agda values of type `T`), `pure`, `_>>=_` and `_>>_` taking arbitrary Agda functions as
continuations (in the discrete model every function is a morphism; `kernel` proves it by gluing
constants), and the expectation rules `∫-pure` and `∫-bind`. `Flip half` gives a fair coin
(`∫-flip`, `∫-flip->>=`); `both` is a `do`-block conjoining two coins, with `∫-both` its
expectation `½(½ g true + ½ g false) + ½(½ g false + ½ g false)`. `BoolDemo lem` instantiates the
Boolean semiring: `true-possible` and `false-possible` are `refl`-style computations. To write
your own program, `open Programs A` and `open Flip half half+half`, then use `do`.

## Conditioning example (`Example/Conditioning.agda`)

`Example/Program.agda` is generic in the weight class and in the universe level (`Programs A K ok1`, with
`A : CompleteSemiring ℓ`; `Flip` takes the coin's outcome type `B`, its two elements and a conjunction,
so the Boolean instances use `Bool` and a level-1 semiring can use `Lift ℓ Bool`). `Conditioning` instantiates
it with `subClass`: `reject` (the zero measure, defect 1) and `guard : Bool → Prog ⊤` discard runs
(`∫-guard`, `∫-guard-pure`), so the lost mass is the rejection probability and `∫` is the unnormalised
expectation. `atLeastOne` (two fair coins conditioned on at least one `true`, returning the first) has
`∫-atLeastOne g ≈ ½(½ g true + ½ g true) + ½(½ g false + ½ 0)`; normalising needs the `normalize`
of the statistical interface (a normalisable semiring).

`Example/HardConditioning.agda` does the same as a measure transformer: `condition p c` keeps the
runs where a Boolean observation `c` holds (`∫-condition`), the rejected mass is added to the defect,
and `condition-split` is the law of total expectation over `c` and `negate c`.

`Example/Bayes.agda` is Bayes' rule, generic in a `NormalizableSemiring`: `posteriorU p w` reweights the
prior by a likelihood `w`, `evidence p w = ∫ p w`, and, given an inverse `n` of the evidence,
`posterior` is a probability measure with `∫ posterior f ≈ n · ∫ p (w · f)` (`bayes`).

`Example/Probability.agda` computes real probabilities with the `do`-notation of `Example/Program.agda`.
`Calculation` is generic in a complete semiring with `half + half ≈ 1`: for two fair coins,
`both-true : ∫ both (test isTrue) ≈ half * half` and `both-mass : ∫ both 1 ≈ 1`. `Additive lem₁`
instantiates it at the additive semiring `([0,∞], +, ×)` with `half` the cut of rationals below ½
(the algebra is done generically because at the concrete semiring Agda unfolds the cuts).

`Analysis/Restrict.agda` is hard rejection in the continuous model: `Fun-χ·` shows measurable functions
are closed under multiplication by an indicator (by induction on `Fun`; the complement case uses
`χ U h′ + χ ¬U` as the complement of `χ U h`), and `restrictM bU m` has `I h = I m (χ U · h)`, with
`mass-restrict : mass (restrictM bU m) ≈ I m (χ U)` and `restrict-split` (total expectation over `U`
and its complement). It is a plain `Measure`; promoting it to a `Pre` of the continuous monad needs the
random-element bookkeeping of `scoreH` and is not done.

## Sub-probability monad of the continuous model (`Continuous/SubProb.agda`, `SubModel.agda`)

`Continuous/Monad.agda` and `Strong.agda` take a `MeasureClass`. With `probClass` (`ProbInstance`) they
give the probability monad; with `subClass`, `ContinuousSub` gives the commutative strong monad of
sub-probability measures (commutativity is Fubini, which holds for any masses). It adds `zeroM`,
`scaleM c` (`c ≤ 1`), `failPre` (the zero measure), and soft conditioning: `scoreH : 𝕀 ⇒ Sub 1` (a
measurable likelihood in `[0,1]` gives a random measure; `∫-score`). `SubModel.agda` instantiates it
over `LowerRealsOmega` and soft-conditions the uniform distribution: `softUniform` (draw
`u ~ U[0,1]`, weight the run by `u`) with `∫-softUniform` and its total mass `mass-softUniform = ½`.
`UniformMean.agda` proves `E[u] = ½` (`mean`): monotone convergence over the partial sums of the binary
expansion, the bit probability `P(rₖ = true) = ½` (`μ0-bitT`) and `Σ 2^{-(k+1)} = 1` (`geom-sum`, via the
Archimedean property; `Arch` now also records `hp 0 ≈ 1`). `Uniform.agda` restates it in the monad as
`∫-uniform-id : ∫ uniform id ≈ half`.

## Checked against the literature

- Heunen–Kammar–Staton–Yang, [*A Convenient Category for Higher-Order Probability Theory*](https://arxiv.org/abs/1701.02547)
  (HKSV): Def. 7 (`QBS`), Props. 16–17 (products, coproducts), the exponential, Def. 10,
  Thm. 21 and Prop. 22 (`Prob`, `η`, `>>=`, functorial action, commutativity).
- Hirata–Minamide–Sato, *Semantic Foundations of Higher-Order Probabilistic Programs in
  Isabelle/HOL* (ITP 2023): the s-finite measure monad `M` on QBS (elements `[α, μ]` with `μ`
  s-finite, equivalence by push-forward, commutative and strong; `Prob` is the sub-space of
  probability measures), `density` and `normalize`.

Where the formalisation deliberately differs:

- **Coproducts** are over any index set, not only countable ones. A random element must locally
  (on a countable measurable partition) lie in one summand, so it has countable image; the
  universal property is proved in `Colimits`/`Complete`.
- **Bind** is axiomatised through a kernel with a fixed measure `ν` (`kernel`, `law-join`).
  HKSV allow an arbitrary kernel `g : R → G(R)`; the two agree because every kernel on a standard
  Borel space is `h(r, –)` pushed forward from a fixed measure.
- **Conditioning** uses `score : W ⇒ M 1`, the constant-density case of the papers' `density`
  (reweighting by `f : X ⇒ W` is `m >>= λx. score (f x) >> return x`, via strength).
- **`normalize`** returns `Prob X + 1` (failure on the zero measure) where the papers return the
  null measure; the infinite-mass case is left unspecified.
- `sumM`/`scaleM` and their axioms are not in the papers verbatim; they encode s-finiteness
  (every measure is a countable sum of scaled laws) and are only validated by the intended model.

## Checking

`make check` is strict: it typechecks every module and fails on any
Agda output, postulate or unsolved hole. Planned results are stated as skeleton modules with holes
(`?`) at their final paths (load one with the Agda MCP `agda_load_and_goals` to see the goals), so
strict mode fails while any remain (there are none at present). `make progress` tolerates unsolved holes,
failing only on other errors or postulates, and lists the files with holes. Agda reuses the
`.agdai` interfaces between runs; `--clean` deletes `_build/` first for a from-scratch check. There is no skeleton at present, so strict mode passes. It needs Agda 2.7.0.1 with
`standard-library` v2.3 and `agda-categories` at c2e7c13e registered. `.github/workflows/qbs.yml`
has a `progress` job (the gate) and a `continue-on-error` strict job (manual trigger; untested).

A from-scratch check takes about 6–10 minutes (interfaces are in `_build/`). Slowness pitfalls: give
every definition an explicit type (an unsolved `z₀ : _` once cost 30 minutes), and do not restate
a big proof term repeated in two places (conversion compares whole `Measure` records: naming the
kernel proof once as `kernel₁` took `IsProb-tensor₁` in `Analysis/Tensor` from 108s to 0.2s). An
error also makes a run fast, so check the output. Profile with
`agda --profile=definitions`, after changing the file's content (unchanged files are skipped).
Slowest remaining: `Model/StatInstance.discreteStat` (45s).

## Unbounded integration

`Analysis/Unbounded` extends the bounded integral `I` to `[0,∞]`-valued measurable functions. With
`pw k = 2ᵏ` and `tr k a = 2⁻ᵏ · min (a, 2ᵏ)` (a `[0,1]`-valued truncation), `FunInf h` says that every
`tr k ∘ h` is a `Fun`, and `Iinf m h = ⨆ₖ 2ᵏ · ∫ (tr k ∘ h) dm`. Because `FunInf` is a predicate on
values and `I-cong` ignores the measurability proof, `Iinf` is independent of representation. Proved:
`Iinf-bounded` (extends `I`), `Iinf-mono`, `Iinf-add`, monotone convergence `Iinf-sup`, and
`FunInf-bounded`, `FunInf-sup` (closure). The module is abstract in an `Arch` semiring with a `Min`
(`Analysis/Min`: glb, continuity along suprema, `min (a+b, c) ≤ min (a,c) + min (b,c)`); lower cuts
use intersection (`Analysis/LowerRealsMin`; `Analysis/UnboundedLowerReals` instantiates it).
`Analysis/Meas` characterises measurability by thresholds (`Meas h`: every `{x | q ∈ h x}` is Borel),
closed under `⊕`, `⊗`, `⊓`, constants and countable suprema by direct formulas on cuts; `Analysis/MeasFun`
proves that every `Meas` function bounded by 1 is a `Fun` (running maxima of the enumerated rationals
below `h x`), so `Fun` = bounded `Meas`, and `FunInf` = `Meas` (`Analysis/Lebesgue`). There `J m φ`
(`Iinf` of a `Meas` function) is proved independent of the measurability proof, monotone, additive,
homogeneous for every constant in `[0,∞]` (`Linear` in `Analysis/Unbounded`: `Iinf-scale`, via
`Iinf-pw` and `Min.mn-sup`), and monotone-convergent. `Analysis/Tonelli` gives `Meas-J` (`r ↦ J (g r) φ` is `Meas` for a kernel `g`) and
`J-bind : J (bind m g) φ ≈ J m (r ↦ J (g r) φ)` for unbounded `φ`. Plan for the s-finite monad (see `TODO.md`):
measures `[α, m, w]` with `m` a probability measure and `w : R → [0,∞]` a `Meas` density.
Decision: truncation by `2⁻ᵏ` needs only halves, so no division by naturals; a dyadic scale is also
what makes the approximations `[0,1]`-valued, as `Fun` and `I-scale` require.

## The s-finite monad

A measure on `X` is a pre-measure on `W × X` (`W = [0,∞]` with `Meas` as its random elements,
`Continuous/Weights`): a probe `α : R → W × X` and a probability measure `m`. The weighted integral
of a test function `f : X → W` is `J m (r ↦ w(α r) · f(x(α r)))`, and two measures are equal when all
these agree (`Continuous/SFinite`: `∫ᴹ`, `≈ᴹ`, `TQ`, `TH`, `ηM`, `∫ᶠ`, `joinPre` with Tonelli
`∫ᴹ-join`); `Continuous/SFiniteMonad` has the join witness and the monad `TM`,
`Continuous/SFiniteStrong` the strength, `Continuous/SFiniteCommute` commutativity (done)
(`Analysis/JFubini`: Fubini for unbounded integrands, `Analysis/JParam`, `Analysis/MixtureN`).
Performance pitfalls found here (each cost hours): `J` is `abstract` in `Analysis/Lebesgue` (use
`J-def`) and so are `mapM`, `joinPre`; `QBS` is `no-eta-equality`, and `TQ`, `_×Q_` are defined by
copatterns, so that comparing two objects compares their arguments instead of unfolding the
records (a conversion between `Functor.F₀ TF (Functor.F₀ TF X)` and `TQ (TQ X)` took minutes
otherwise); pass implicit arguments explicitly only where Agda cannot invert them (`Meas ?φ`,
`XW ?X`), but leave nested ones to unification (`mm4` vs `mm5` in the history); make measurability
witnesses `abstract`.

## Not done

- (done) The s-finite measure monad: `Continuous/SFiniteStat.continuousStat` is a complete
  `StatisticalInterface` for the continuous model (`TM`, strength, commutativity, `score`, `scaleM`/`sumM`/`sumK`,
  `scaled-laws` via `SFiniteDecomp`, `normalize` via `SFiniteNorm`).  `make check` is strict and passes.
- Other distributions (Gaussian: see `plans/`); the sample mean/variance statements are division-free.
- `restrictM` as a morphism of the continuous monad (like `scoreH`); disintegration along a
  continuous observation.
- Riesz for sub-probability measures.
- Signed values, higher moments, iid products, Gaussian, statistical models and estimators: see `plans/`.
