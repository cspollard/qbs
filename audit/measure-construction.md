# Audit: measure-construction

This is a read-only audit: the agent used grep and file reads and did not run Agda. Its report came back as a message and was saved here unchanged.

## 1. Summary

The domain builds measure theory on Cantor space 2^ℕ, with values in lower-cut reals.

1. `Borel/*` defines the Borel σ-algebra as an inductive predicate on sets. It adds Dynkin's π–λ theorem, cons/merge/lead/cells maps and a category of QBS over Cantor space.
2. `Clopen`, `ClopenMeasure`, `OpenMeasure` and `Regular` give clopen sets as finite trees, with the fan theorem (compactness). They also give the dyadic premeasure, open sets as chains of clopens, and a Carathéodory-style extension to all Borel sets by two-sided open approximation (`IsRegular`). The result is `coinBM`, a σ-additive set function (`BorelMeasure.agda`).
3. `CoinFacts`, `CoinSimple`, `CoinCont`, `CoinGrid` and `CoinIntegral` build the Daniell integral. A `Sf` is a simple function: a countable Borel partition with values. `L h` is the supremum of the simple minorants' integrals. `Functional.functional` shows it is a `Measure` (monotone, additive, homogeneous, sup-continuous, mass ≤ 1).
4. `Measure` defines sub-probability measures as Daniell functionals on `Fun` (bounded measurable functions).
   - `dirac`, `push` and `bind` are plain composition.
   - `Uniqueness` proves that measures agreeing on cylinders are equal (π–λ).
   - `Riesz` proves the round trips set function ↔ functional.
   - `Param`, `Tensor`, `Tonelli`, `JParam` and `JFubini` give kernels, products and Fubini, for bounded and then for `Meas` (threshold-measurable, [0,∞]-valued) integrands.
   - `Lebesgue` gives the unbounded integral `J`.
   - `Density`, `Restrict`, `Mixture`, `MixtureN` and `JSum` give density measures, restriction, and finite and countable mixtures.
   - `DigitAlg`, `DyadicAlg`, `ExpansionCons` and `BinaryExpansion` hold the binary-expansion and dyadic arithmetic used by the continuous model.

The mathematics is sound and well commented. The problems are findability and naming:

- The genuine theorems sit under module names that do not say what they are.
- The coin pipeline is generic in the measure, yet everything is called "Coin".
- There is dead duplicate code (`Borel/Measure`).
- Three tree/dyadic helper families and three π–λ applications look like one pattern repeated.

Top recommendations:

1. Rename and re-document the Coin* modules, which are generic Daniell-integral construction, and add a "Measure construction roadmap" entry to Interface.md/Guide.md (the headline theorems are currently unindexed).
2. Delete the unused generic `QBS.Borel.Measure.BorelMeasure` record and move `Disjoint` out (it duplicates `BM.BorelMeasure`).
3. Factor one "Dynkin class" combinator for the three π–λ applications (Regular, Uniqueness, Param).
4. Merge or move the dyadic algebra (`DyadicAlg`, `DigitAlg`, the `hp`/`tp`/`th`/`natE` families) into one `Dyadic` module, and fold `Mixture` into `Cone`.
5. Document, or categorically package, the measure operations as an algebra for a Giry-style monad. This is only worth it as documentation, not as code (§5).

## 2. Main results

Legend: Easy = findable in Interface.md or Guide.md. Doc = crisp header or comment.

| Name (file:line) | Plain statement | Easy | Doc |
|---|---|---|---|
| `Borel` / `dynkin` (`Borel/Core`, `Borel/PiLambda.agda:224`) | π–λ: a class containing cylinders and closed under complement and disjoint union contains every Borel set | no (PiLambda is not in Interface.md's measure entries) | header good |
| `Fan.*` (`Analysis/Clopen.agda:164`) | a decreasing sequence of clopens with empty intersection is eventually empty (compactness) | no | good |
| `Opens.compact`, `ν` modular (`OpenMeasure.agda:118`, `:253`) | clopen covering of an open set is finite; opens have a well-defined modular measure | no | good |
| `Regularity.borel-meas` (`Regular.agda:283`) | every Borel set is regular, i.e. Carathéodory extension of the dyadic premeasure | no (only through `CoinSets`, an 11-line alias) | header excellent |
| `BM.BorelMeasure`, `coinBM` (`BorelMeasure.agda:31`, `:41`) | σ-additive probability on Borel sets; the fair coin | partly (History.md) | ok |
| `DaniellB.L`, `L-sup`, `L-add`, `L-scale` (`CoinIntegral.agda:94`, `:440`, `:181`, `:335`) | integral of any measurable `h` as sup of simple minorants is a Daniell functional | no (Interface lists `fairCoin` under `CoinIntegral`, but it is defined in `Continuous/FairCoin.agda:38`) | header ok; names `L`, `Minor`, `Lmem` opaque |
| `Functional.functional`, `functional-ind` (`Functional.agda:~35`) | any Borel probability measure gives a `Measure` with `I (χ U) ≈ ν U` | no | good |
| `Measure`, `IsProb`, `dirac`, `push`, `bind` (`Measure.agda:25`, `:55`, `:63`, `:73`, `:98`) | sub-probability measures as Daniell functionals, closed under Giry operations | yes (Interface.md) | good |
| `Uniqueness.agree-fun` (`Uniqueness.agda:~67`) | probability measures agreeing on cylinders agree on all `Fun` | no | good |
| `Riesz.setFun`, `setFun-functional`, `functional-setFun` (`Riesz.agda:~30-62`) | Riesz–Daniell correspondence | no (not in Interface.md) | good |
| `Tensor.tensor₁/₂`, Fubini (`Tensor.agda:~42`) and `JFubini.J-fubini` (`JFubini.agda:63`) | product of measures; iterated integrals commute; unbounded version | no | header good |
| `Tonelli.J-bind` (`Tonelli.agda:~30`) | `∫ φ d(bind m g) = ∫ (r ↦ ∫ φ dg r) dm` for `Meas` φ | no | good |
| `Lebesgue.J` and its laws (`Lebesgue.agda:27`) | unbounded integral of `Meas` functions: monotone, additive, homogeneous, MCT | yes (Interface.md "Meas, Lebesgue") | good |
| `Meas`, `MeasFun`, `LevelSets` | `Meas h ⇔ Fun h` for h ≤ 1 (threshold vs inductive measurability) | partly | good |
| `Density.densM`, `J-dens` (`Density.agda:55`, `:108`) | measure with density v, scaled by d | partly | good |
| `JSum`, `MixtureN` | `J (∑ aₙ) = ∑ J aₙ`; countable mixtures | no | ok |
| `SelfSimilar` | self-similar CDF is the identity (uniqueness of uniform) | no | good, long header |
| `Restrict.restrictM`, `restrict-split` (`Restrict.agda:85`, `:108`) | restriction to a Borel set (conditioning event); total expectation | partly | good |

Not findable: nearly everything except the `Measure` interface and `Meas`/`Lebesgue`. There is no entry that says "the construction of the coin integral lives in …".

## 3. Documentation

1. **Roadmap entry (Interface.md or Guide.md), proposed text:**
   > *Measure construction on Cantor space.* `Borel.Core`/`Borel.PiLambda`: Borel σ-algebra and π–λ. `Analysis.Clopen`/`ClopenMeasure`/`OpenMeasure`/`Regular`: fan theorem, dyadic premeasure and its Carathéodory extension (`borel-meas`), giving `BM.coinBM`. `Analysis.CoinIntegral` (generic in any `BorelMeasure`): Daniell integral by simple minorants; `Functional.functional` turns a `BorelMeasure` into a `Measure`. `Analysis.Measure`: measures as Daniell functionals, with `dirac`/`push`/`bind`. `Analysis.Uniqueness`, `Riesz`: measures agreeing on cylinders coincide; set functions and functionals correspond. `Analysis.Tensor`/`Tonelli`/`JFubini`: products and Fubini. `Analysis.Lebesgue`: unbounded integral `J`.
2. **Fix the `fairCoin` pointer.** Interface.md's `CoinIntegral`/`FairCoin` section lists `fairCoin`, but `Analysis.CoinIntegral` only exports `Daniell` (`:444`) and `DaniellB`. Say "`fairCoin` is in `QBS.Continuous.FairCoin`, built as `Functional.functional` of `coinBM`".
3. **Header of `CoinIntegral.agda`** says "integral against the fair-coin measure". Replace with: "Daniell integral of an arbitrary measurable `h` against any Borel probability measure `B`, as the supremum of the integrals of simple minorants; `Daniell` is the fair-coin instance. Proves `L-add`, `L-scale`, `L-sup`, `L-one`."
4. **Rename opaque identifiers or document them:** `L`, `Minor`, `Lmem` (`CoinIntegral.agda:87-94`), `rC`, `th`, `tp`, `Sf`, `Pt`. Add a one-line glossary comment at the top of each module.
5. **`CoinSets.agda`** (11 lines) is just `Regularity (lowerRealsArch lem) lem`. Say so in the header and consider inlining into `BorelMeasure`.
6. **Module names that mislead:**
   - `CoinFacts`, `CoinSimple`, `CoinCont`, `CoinGrid`: all take an arbitrary `B : BorelMeasure`. Suggest `Daniell/Facts`, `Daniell/Simple`, `Daniell/Continuity`, `Daniell/Grid` (or `BorelMeasure*`).
   - `Fun` (class of bounded measurable functions) vs `Meas`: header of `Fun` should say "bounded by 1, inductive; `Meas` is the unbounded threshold class".
   - `Analysis.Functional` is ambiguous; suggest `DaniellFunctional`. `Analysis.Measure` clashes with `Probability.Measure` and `Borel.Measure.BorelMeasure.Measure`. Interface.md already warns about the `probClass` clash; renaming `Analysis.Measure` to `Daniell` (module `DaniellMeasure`) is cleaner.
7. **`Borel/Measure.agda`** header advertises measures valued in a complete semiring, but see §4.1: only `Disjoint` is used.
8. `Analysis/Riesz`, `Uniqueness`, `Tensor`, `JFubini`, `Regular` need Interface.md lines, with the statements above.

## 4. Simplification

1. **Dead duplicate measure record.** `Borel/Measure.agda:26-63` defines a generic `BorelMeasure A` with `pushforward`, `IsProbability`, `pushforward-id/∘`. Only `Disjoint` (`:23`) is imported anywhere (grep: every importer uses `using (Disjoint)`). The live version is `BM.BorelMeasure` (`BorelMeasure.agda:31`, fixed to `LowerRealsOmega`, `∑ᶠ`). Proposal: delete the record and pushforward code (or make `BM.BorelMeasure` an instance of it if generic semiring values matter), and move `Disjoint` to `Borel.Core`. Gain about 50 lines and one overlapping concept; risk is nil for dependents (they import only `Disjoint`). The pushforward functoriality lemmas are the only content with value; if kept, they would justify a functor presentation (§5).
2. **Three π–λ applications with the same shape.** `Regular.agda:283`, `Uniqueness.agda:67`, `Param.agda:161` each define a `Good`/`Agree`/`DP` class with `*-resp`, `*-cyl`, `*-compl`, `*-disj`. Introduce a `DynkinClass` record (`resp`, `cyl`, `compl`, `disj`) in `PiLambda` and an `Agree` helper for "two functionals agree on U" used by `Uniqueness` and `Param`. Gain: a shared checklist and about 30 lines; the `Agree-compl`/`Agree-disj` proofs in `Uniqueness` look generic over any pair of additive set functions with equal mass. Cost: modest.
3. **Dyadic and digit arithmetic scattered.**
   - `DyadicAlg` (`dbl`, `two`, `tw`, `cons-alg`, `∑ᶠ-dbl`), `DigitAlg` (`mN`, `dy-dbl`, `dy-succ`, `dy-scale`, `dy-le`, `dy-ge`, `dbl-*2`) and `Half` (`hp`, `hp-double`) overlap.
   - `LowerRealsArch` has `tp`, `hpC`; `CoinGrid` has `th`, `th-suc`.
   - `two` is defined in 4 other modules (`GeometricNorm`, `GeometricMoment2`, `RealShiftNull`, `GaussRealAbs`); `natE` lives in `Exp`.
   - `DigitAlg` opens `DyadicAlg`, and `dbl-*2` (`DigitAlg.agda:122`) recovers `dbl m = m * 2` after `DyadicAlg` defines `dbl` structurally.
   - Proposal: one `Dyadic` module with `natE`, `two`, `hp`, `dbl`, `dy-*` stated once over `OmegaSemiring` with a half, and a pointer to `th`/`tp` in the ℚ model. Gain: one place for "n·2⁻ᵏ" arithmetic. Risk: the `*Alg` split exists for compile time and memory (the project's convention); keep the split by merging only `DyadicAlg`+`DigitAlg` (both header "algebra behind …") into one `*Alg`, and check timings.
4. **`Mixture` is a 53-line wrapper** (`mix = addM (scaleM half …) (scaleM half …)`), used by 2 modules. Fold into `Cone` or `MixtureN` (binary case as `MixtureN` with two coefficients), or keep only `mix-bound`/`mix-one`. `Restrict` (1 importer, 113 lines) and `Pieces` (1 importer) could live next to their user rather than as top-level files, but this is cosmetic.
5. **Two parallel integrals, `I` and `J`, and two measurability classes, `Fun` and `Meas`.** The `Fun`↔`Meas` equivalence for h ≤ 1 is proved (`MeasFun`, 221 lines), plus `LevelSets` (168). Evidence of cost: every bounded-then-unbounded result is stated twice (`Tensor` vs `JFubini`, `Uniqueness` vs `UniquenessWeighted`, `Density.densM` vs `J-dens`, `JParam` and `Param`). Better: state the main laws once for `Meas` and obtain `Fun` versions by the equivalence. Risk is large (the `Fun` induction principle is used in `Param`), so recommend this as a long-term aim, not a refactor now.
6. **`UniquenessWeighted` (143 lines)** extends `Uniqueness` by scaling and truncation; its header cites a "plan 03" that outsiders cannot read. Replace with the actual statement (`uniqW`: two weighted pushforwards with equal finite mass that agree on cylinders agree on every `Meas` function).
7. **`CoinSets`** is an alias module (see §3.5); inlining removes a file and one import hop.
8. **`Indicators.PS`, `I-PS`, `PS-sup`** (`Indicators.agda:109-157`) re-prove monotone convergence for partial sums of indicators; `Series`/`SeriesSup` already provide `∑ᶠ-⨆`. Check if `PS` can be `psum (χ ∘ V)` plus the existing lemma.
9. **`CoinIntegral.smallprod`** (`:46`) is a pure ℚ inequality; move it to `RationalLemmas` with the others.
10. **Long proofs.** `CoinIntegral` (444 lines) splits cleanly into `Add` (143-181), `Scale` (186-335, about 150 lines, the longest, containing `cle`, `allc-from`, `memk`) and `Sup`/`SupLaw` (347-440). Candidate: move `Scale` and `Sup` to their own modules, which clarifies the headline theorem and reduces re-typechecking when editing one law. `Scale`'s classical decision lemmas (`allc-from`, `memk`) look like reproving that a cut equals ⋂ over enumerated rationals; a general lemma in `LowerReals` would shorten it.

## 5. Categorical language

- **Measures as algebras of the Giry monad.** The ingredients are already there as the `dirac`/`push`/`bind` of `Measure.agda:55-110` and `MeasureClass` (`:112`). `Measure.bind` has a `KernelOk` side condition because measurability of `r ↦ I (g r) h` is not automatic. That is a *relative* monad on the subcategory of kernels, not an ordinary monad on a category of spaces. A genuine monad needs the Giry σ-algebra on measures, which the library avoids on purpose (header of `Measure`: "no extension theorem needed"). The monad is realised abstractly in `QBS/Probability.agda`/`IntegralMonad.agda` (outside this domain). Verdict: do not recast the records as `Monad` structures; instead document that `Measure` plus `dirac`/`push`/`bind` is the concrete model of `ProbabilityInterface`, and that the monad laws for `bind` hold by `I-cong` (a `Monad` from `Categories.Monad` would need the setoid-enriched category of measurable maps, high cost, little gain).
- **Pushforward as a functor.** `Borel/Measure.pushforward-id/-∘` (dead code, §4.1) and `Measure.push` are functorial in `f` (`push-id`/`push-∘` are not stated for `Measure`). Statement as a functor `Measurable → Measure` would need a category of measurable maps with setoid-based hom equality; that exists as `Borel.Category` (32 lines). Worth adding `push-id`/`push-∘` as plain lemmas, not as `Functor`.
- **Daniell integral as a left Kan extension / colimit.** `L h = ⨆ {∫ s | s ≤ h}` is a supremum over the poset of simple minorants (a directed colimit in the poset category). `Categories.Diagram.Colimit` would not help: the poset is Set₁-large, and the construction relies on `lem₁` (hence `lemOf`). Bespoke is better.
- **Countable additivity, sup-continuity** as ω-continuous functors: the semiring is already an `OmegaSemiring`; the `I-sup` field is exactly ω-chain continuity. Using `Categories` (`ωCPO`-style) offers no extra lemma. Skip.
- **Product of measures as a monoidal structure.** `tensor₁` is `bind m (pushMerge (λ _ → n))`; `Tensor` proves commutativity (Fubini) by uniqueness. A commutative monoidal structure with `merge : Cantor × Cantor ≅ Cantor` is what `Probability.agda` axiomatises. Say in `Tensor`'s header that `tensor₁ ≈ tensor₂` is the commutativity of the strength; no code change.
- **Cone structure.** `Cone.agda` (`zeroM`, `scaleM`, `addM`) is an ad hoc semimodule structure on measures with total mass ≤ 1. A bundled `Semimodule` over `OmegaSemiring` is unrealistic (partiality constraints `c ≤ 1`, `mass ≤ 1`); the bespoke cone is the right choice.
- **Reasoning combinators.** Heavy use of the `SetoidReasoning` begin/∎ chains is fine; the `Fun`-proof arguments (`I-cong m e f f′`) repeated everywhere could be wrapped as a `≈ᵐ`-style `_≈ₘ_` setoid reasoning on `Measure` (equality: same `I` on all `Fun`). Since `I-cong` already establishes proof irrelevance, introduce `_≈ₘ_` and `Measure` setoid with `IsEquivalence`, to reuse `Relation.Binary.Reasoning`. Cost low; gain readability in `Tensor` (mass₁/mass₂ chains), `Restrict`, `Density`.

## 6. Open questions

1. Is `QBS.Borel.Measure.BorelMeasure` intentionally kept for generality (other semiring values, sub-probability measures; History.md mentions needing `μ-⊤ ≤ 1`)? If so it should be wired to `BM.BorelMeasure`; otherwise delete it.
2. Is renaming `Coin*` to a generic name acceptable given downstream imports (`Continuous.FirstBit`, `CoinIndep`, `FairCoin`)? Only 3 outside modules import them, so churn is small.
3. Can `Param`'s parametric-measurability proof be restated for `Meas` only, dropping `Fun` induction at the top level?
4. Is the `Fun`/`Meas` duality permanent, or is `Fun` intended as scaffolding?
5. Is the intended outsider entry point `Analysis.Measure` (the interface) or `Regular` (the construction)? The roadmap in §3.1 assumes both.
6. Should `Analysis.Cone` and `Mixture` join `Measure.agda` as "operations on measures"?

## Implementation status (2026-11-07)

- A, roadmap entry (§3.1): done, in `Interface.md` ("Measure construction on Cantor space").
- A, `fairCoin` pointer (§3.2): done.
- A, `CoinIntegral` header and glossary for `L`, `Minor`, `Lmem`, `Sf` (§3.3, §3.4): done. `Pt`, `rC`, `th`, `tp` not glossed.
- A, `Interface.md` lines for Riesz, Uniqueness, Tensor, JFubini, Regular (§3.8): done.
- A, `UniquenessWeighted` "plan 03" header (§4.6): done.
- B, `Borel.Measure` record (§4.1): done earlier by agent 0.
- B, `CoinSets` (§3.5, §4.7): done, inlined as `Regularity (lowerRealsArch lem) lem` in `BorelMeasure`, `FairCoin`, `CoinIndep`, `FirstBit`; module deleted, `Classical.md` updated (`History.md` left as history).
- B, fold `Mixture` (§4.4): skipped for budget. B, `Indicators.PS` (§4.8): not examined.
- C: nothing recommended.
- D, `push-id`/`push-∘` (§5): done as plain lemmas in `Analysis.Measure`, with `_≈ₘ_` (equality of measures).
- D, using `_≈ₘ_` to shorten existing chains: skipped.
- D, `DynkinClass` record (§4.2), `Cone`/`Threshold` move, dyadic merge (§4.3): skipped for budget.
- E, `Coin*` renames, `CoinIntegral` split, `Analysis.Measure` rename (§3.6, §4.10): skipped for budget.

## Implementation status, round 2 (2026-11-07)

- D, `DynkinClass` record (§4.2): skipped, not worthwhile. `dynkin` already takes `resp`, `cyl`, `compl`, `disj` as its four arguments, and each application (`Regular`, `Uniqueness`, `Param`) proves exactly those four. A record would add a declaration and a wrapper without shortening any application.
- B, `Mixture` (§4.4): done. Folded as `module Mixture` at the end of `Analysis/Cone`; `Analysis/Mixture.agda` deleted; `Continuous/FirstBit` and the `MixtureN` header updated.
- B, `Indicators.PS` (§4.8): partly done. `PS V N x` is definitionally `psum (λ n → χ (V n) x) N`, so it is now defined as that and `PS-inc` is `psum-inc`. `PS-sup` stays: it is a pointwise argument, not `∑ᶠ-⨆`.
- E, renames: `Analysis.CoinFacts` → `Analysis.Daniell.Facts`, `CoinSimple` → `Daniell.Simple`, `CoinCont` → `Daniell.Continuity`, `CoinGrid` → `Daniell.Grid`. Importers: `CoinIntegral`, `Functional`, and the Daniell modules themselves. `scripts/longdecls.baseline` and the docs were updated.
- E, `CoinIntegral` rename and Add/Scale/Sup split: skipped. 179 modules import it (156 only for `lemOf`), so a rename or a split would mean editing and re-checking all of them by hand. A tidier route is to move `lemOf` into a tiny module first.
