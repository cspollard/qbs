# Plan: simplify onto known structures

A library-wide audit, done 2026-10-31 on the `probes-site` branch (after `d8e9b5f`).  It looks for places where the
library reinvents a structure from the stdlib, agda-categories, or the literature, or duplicates its own
definitions.  Stage 1 of "Suggested order" is done on branch `simplify-stage1` (see "Stage 1 outcome" at the end); the rest is not.  Items specific to `Core`/probes (QBSCat as a `SubCategory` of `Setoids`,
`refineₛ`, the `random-cast` casts, `⇑`, `reassoc`, `Wit` indexing, `ℕQ`) are in `plans/04-equality.md`, "Further
simplifications noticed during the sweep", and are not repeated here.

Guiding rule: when a structure is standard, name it as the literature does and use the library's bundle if one
exists.  When no library has it (an ordered semiring, a continuation monad on setoids), keep a local record but
shape it like the standard one, and cite the source in the module header.

Paths are relative to `src/QBS/`.  Stdlib paths are relative to `agda-stdlib/src/`.  Line numbers are as of the
audit.  Each item gives the payoff and then the risk.  Items are ranked by payoff within each section, and the
sections are in suggested order of work.

## A. Algebra and order (Analysis)

1. **One sequence of powers of ½, and one `½(x+x) ≈ x`.**
   - ½ⁿ is defined five times:
     - `BinaryExpansion.hpow` (:30)
     - the `Arch` fields `hp`/`hp-zero`/`hp-double` (`Archimedean.agda:22-24`)
     - `LowerRealsArch.tp` (:48)
     - `Unbounded.pw`/`hp-pw` (:44)
     - `BoundedCancel.pow2`, the ℕ-valued 2ᵏ (:24)
   - `Continuous/UniformMean.hp≈hpow` (:57) exists only to prove that two of these agree.
   - The geometric sum is proved twice: `BinaryExpansion.geom` (:41) and `ArchLemmas.geo` (`Archimedean.agda:46`).
     `JSum.hp-geo`/`∑hp≤1`/`∑hp≈1` (:71-85) is the same fact again, proved at the concrete cuts.
   - `½·(x+x) ≈ x` is proved four times:
     - `HalfOrder.half-twice` (:22)
     - `Interleave.half-double` (:117)
     - `BoundedCancel.double-half` (:38)
     - the local `two` in `ClopenMeasure` (:84)
   - `½·hp n ≈ hp (suc n)` is proved twice: `SelfSimilar.hp-half` (:43) and `Unbounded.half-hp` (:102).
   - Standard: `_^_` (`Algebra/Definitions/RawSemiring.agda:47`), with laws in `Algebra.Properties.Semiring.Exp`.
     `x ^ suc n` unfolds to `x * x ^ n` (it is `Mult._×_` over the multiplicative monoid, so check that `hpow`
     recurses the same way).  For ℕ, `pow2 k` is `2 ^ k`.
   - Do: one `Half` module over `OmegaSemiring` with `half`, `half+half`, `hp = half ^_`, `half-twice`,
     `hp-double` and the geometric sum.  Remove the `hp*` fields from `Arch`.
   - Payoff: about 100 lines, and `hp≈hpow` disappears.
   - Risk: the one `Arch` instance (`LowerRealsArch.agda:181`, `hp = qC (tp n)`) needs a new lemma, `qC` commutes
     with `*`.
2. **Build `OrderedSemiring` on `IsPartialOrder`.**
   - Now: `Omega.agda:22-38` has loose fields `≤-reflexive`, `≤-trans`, `≤-antisym`, plus a local `≤-resp` (:69).
   - Do: replace them with a field `isPartialOrder : IsPartialOrder _≈_ _≤_` (`Relation.Binary.Structures`) and
     expose a `Poset`.  `≤-resp` becomes `≤-resp-≈`.
   - Payoff: chains can use `Relation.Binary.Reasoning.PartialOrder` with mixed `≤⟨⟩`/`≈⟨⟩` steps.  The Analysis
     tree has 67 `≤-trans (≤-reflexive …)` idioms, e.g. `Unbounded.agda:301-310`, `Regular.agda:202-213`,
     `JSum.agda:77-85`.
   - Follow-on: `Min.mn-≤l/mn-≤r/mn-glb` (:29-31) is `Infimum _≤_ mn`
     (`Relation/Binary/Lattice/Definitions.agda:32`), i.e. `IsMeetSemilattice`.  The local
     `Unbounded.mn-mono` (:64) is then `Relation.Binary.Lattice.Properties.MeetSemilattice.∧-monotonic`.
   - Stdlib 2.3 has no ordered-semiring bundle, so keep the record.  Cite `OmegaSemiring` as an ω-continuous
     semiring (Kuich; Ésik–Kuich).
   - Risk: low.  The record has two instances (`LowerReals.agda:405-417` and `Min`).
3. **`Indicators.fsum` is `Series.psum`.**
   - Now: `Indicators.agda:105-110` is the same text as `Series.agda:28-33`.  `Uniqueness.fsum-cong` (:36-38)
     copies `psum-cong`, and `Riesz.Bridge` (:35-42) exists only to prove `fsum ≈ psum`.
   - Do: import `Series` (there is no cycle).
   - Payoff: the bridge, the copy and `Param.agda:98-106`'s use of them all go.
   - Risk: none.
4. **`Measure.I-cong` is derivable.**
   - It follows from `I-mono` and `≤-antisym`/`≤-reflexive`; `Unbounded.agda:303` already derives `Iinf-cong`
     this way.
   - Do: make it a lemma with the same name.
   - Payoff: removes an obligation from 10 instances: `Measure.agda:58/72/91`, `Functional:48`, `Restrict:88`,
     `Mixture:67`, `MixtureN:74`, `Density:62`, `Continuous/SubProb:48/60`.
5. **`RationalLemmas` re-proves stdlib.**
   - About 40 lines (:28-100) are one-line aliases of `Data.Rational.Unnormalised.Properties`.  Use
     `open … public using/renaming` instead.
   - Some "new" lemmas already exist:
     - `*-mono-<-posʳ` (:221) is `*-monoˡ-<-pos` (`Properties:1307`).
     - `*-mono-≤-nnʳ` (:224) is `*-monoˡ-≤-nonNeg` (:1270).
     - `*-pos` (:111) is `pos*pos⇒pos` (:1364).
     - `CutSum.pos-add` (:278) and `LowerRealsArch.pos+` (:121) are `pos+pos⇒pos` (:907).
     - `LowerRealsArch.≤-+ʳ′` (:93) is `p≤p+q` (:874).
   - The idiom `≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< …)` recurs 14 times (LowerInverse ×7, LowerRealsArch ×4,
     LowerReals, Pieces, CutSum).  Wrap it once.
   - `0 ≤ nat k` is proved twice: `LowerRealsArch.nat-nonneg` (:63) and `Pieces.nat-0≤` (:56).
   - `nat` monotone is proved three times: `Pieces.nat-mono` (:60), `CoinGrid.nat-mono′` (:80),
     `Continuous/SFiniteDecomp.nat-mono` (:237).  Keep one copy in `RationalLemmas`.
   - `LowerRealsArch.hf` (:33-46) builds ½ as `inv 0<2` and proves `0<hf` by contradiction.  Stdlib has `½`
     (`Data/Rational/Unnormalised/Base.agda:130`).  Check that `½ + ½ ≃ 1` is `*≡* refl`.
   - Use `≤-Reasoning` (`Properties:613`) for the long `≤-trans` chains.
   - Payoff: moderate.  Risk: low.  The positivity-to-instance adapters `pos`/`nonneg` (:105-108) already
     cover the "no instances" rationale.
6. **Commutative-semigroup lemmas re-proved locally.**
   - `x * (y * z) ≈ y * (x * z)` is proved at least six times:
     - `Model/Strong.fubini.mid` (:155)
     - `SFiniteCommute.Fub.swap3`
     - `SFiniteNorm`, `Analysis/JSum`, `MixtureN`, `Density`

     Use `Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz` (:45).
   - `Series.+-interchange` (:39) and `ClopenMeasure.swap4` (:34) are `CommutativeSemigroup.interchange` (:28).
   - `Variance.agda:47-48,232` proves `(-x)·x = -(x·x)` by hand; that is
     `Algebra.Properties.RingWithoutOne.-‿distribˡ-*` (:39).
7. **`Bayesian.pow` (`Inference/Bayesian.agda:39`) is `_^_`**, with `x ^ suc n = x * x ^ n`.
   `likSeq-counts` can then use `Algebra.Properties.Semiring.Exp`.
8. **Finite sums against `Algebra.Properties.CommutativeMonoid.Sum`** (uncertain).
   - `psum-+`, `psum-scale` and `psum2-flip` are `∑-distrib-+`, `*-distribˡ-sum` and `∑-comm`.  But stdlib sums
     over `Fin n` with `foldr`, while `psum` adds on the right.
   - Worth a bridge `psum a N ≈ ∑[ i < N ] a (toℕ i)` only if more finite-sum algebra is coming.

## B. Measures and monads: one construction instead of three

1. **The monad presented by its integral (the largest single item).**
   - In all three models, measure equality is "all integrals agree" (`_≈ᵖ_`, `_≈ᴹ_`, `Model/Monad.PreS`).  Every
     functor, monad and strength law is then the same `trans` chain over five equations: `∫-cong`, `∫-map`,
     `∫-η`, `∫-join`, `∫-σ`.  Commutativity is one Fubini equation in about 60 lines of plumbing.
   - Sites:
     - `Model/Monad.agda:257-308`
     - `Continuous/Monad.agda:365-417`
     - `SFiniteMonad.agda:62-76, 231-297`
     - the `strength` records in `Continuous/Strong:111-123`, `SFiniteStrong:120-177`, `Model/Strong:110-123`
     - `commutative` in `Continuous/Strong:150-161`, `SFiniteCommute:188-251`, `Model/Strong:162-167`
   - Standard notion: ∫ : T X → ((X → V) → V) is a monad morphism into the continuation (expectation) monad, and
     T X carries exactly the kernel of that map.  So the laws transport from the continuation monad, and
     commutativity of T is Fubini (Kock, *Commutative monads as a theory of distributions*, TAC 2012; Jacobs'
     expectation monad; Ścibior et al. 2018 present the QBS monad this way).
   - Do: add a local `QBS/IntegralMonad.agda` (no library has a continuation monad on setoids).
     - Parameters: tests `Test X` with precomposition, `TQ`, `TH`, `ηH`, `joinH`, `σH`, the five integral
       equations, and `fubini` for the commutative part.
     - Output: `TM`, `strength`, `strongMonad`, `commutative`.
   - Payoff: about 300 lines become about 120, and every future model gets the laws free.
   - Risk: implicit inference through a generic module.  Take `X`/`Y` explicitly, keep `mapM`/`joinPre`
     `abstract` model-side, and re-time `SFiniteStat` and `ProbInstance`.  `Model/Strong` gains little, since its
     strength laws are `refl`.
2. **`WitM` duplicates `Continuous.Wit`.**
   - Sites: `SFinite.agda:126-182` (`WitM`, `TQ-resp/const/pre/glue`) against `Continuous/Monad.agda:116-123,
     150-169, 193-226`.  The only difference is `≈ᴹ` instead of `≈ᵖ`.
   - Do: parameterise `Wit` and the probes of `TQ` by an equivalence `_≋_` on `Pre X` with `≈ᵖ ⊆ ≋`.  Do this
     together with plan 4's "index `Wit` by `Func`".
   - Payoff: about 60 lines; `fromWit` goes.
   - Risk: keep the `abstract` blocks for compile time.
3. **Colimits are one construction written three times.**
   - Sites: `_+Q_` (`Colimits.agda:73-101`), `CoeqQ` (`Colimits.agda:180-205`) and `ΣQ` (`Complete.agda:109-133`)
     each hand-write "α is random iff it is locally a piece".  The `random-resp`, `const-random`, `pre-random`
     and the `glue-random`/`unpair-pair` proof are identical in all three.
   - Do: one constructor from (setoid `Z`, pieces `P`, `ev : P → R → Z`, `pre` with an `ev-pre` law, a constant
     piece) to `Probes` plus `glue-random`.
   - In site terms, this is the sheaf generated by a presheaf of pieces.  In HKSV (LICS 2017), it is the QBS
     structure generated on coproducts and quotients.
   - Payoff: about 60 lines.
   - Risk: low to moderate.  `_+Q_` needs a case split for `ev-pre`.
4. **Measures form a cone.**
   - Now: `Mixture.agda:25-77` proves all six `Measure` laws for `½m₁ + ½m₂` by hand.  `MixtureN`, `Density`,
     `Restrict` and `SubProb` repeat the scaling pattern.
   - Standard: valuations form a cone, a module over [0,∞] (Jones–Plotkin 1989; Keimel–Plotkin).
   - Do: generic `scaleM c m` (with `c ≤ 1` for `I-sub`) and `addM` (with a mass bound).  Then
     `mix = addM (scaleM ½ m₁) (scaleM ½ m₂)`.
   - Risk: moderate, from the side conditions; `MixtureN` must stay countable.
5. **The codiscrete QBS is built three times.**
   - Sites: `Example/Program.Disc` (:51), `Model/StatInstance.WQ` (:63), `Limits.1Q` (:34).
   - It is the right adjoint of the forgetful functor (HKSV 2017).  One `codiscrete : Setoid → QBS S` would cover
     all three.

## C. Categorical naming and agda-categories reuse

1. **Strength names are swapped.**
   - `Probability.agda:100-103` calls the left strength `τ` and the right one `σ`.  agda-categories does the
     opposite (`Monad/Strong/Properties.agda:76-79` `σ` left, `:227-230` `τ` right), and so does
     `Model/Strong.agda:160-167` (`RS.τ`).
   - Do: swap the names, and say that `ψ` (:106-107) is Kock's double strength.
2. **Export the cartesian aliases once.**  `cartesian`/`V`/`braided` are rebuilt privately in:
   - `Model/Strong:105`
   - `Continuous/Strong:101-147`
   - `SFiniteStrong:141`
   - `SFiniteCommute:68-80`

   `Model/DiscreteSource.agda:43-46` records that separate aliases cost about 30 s per conversion, so exporting
   them once (e.g. from `QBS.Exponential`) may also help compile time.  This is unmeasured.
3. **Small agda-categories reuses.**
   - `Model/Monad.agda:277-288`: the `sym-commute`/`sym-assoc` fields come for free with `ntHelper`
     (`Categories/NaturalTransformation/Core.agda:57`).
   - `Statistical.agda:99-101` `rw` is `MR.extendʳ` (`Categories/Morphism/Reasoning/Core.agda:172`).
   - `Probability.agda:118-123` `⟨id,!⟩∘π₁`/`⟨!,id⟩∘π₂` are the `isoˡ` of `A×⊤≅A`/`⊤×A≅A` in
     `Categories.Category.Cartesian.Monoidal` (already imported as `CM`).
4. **`Limits.EqS` (:75-86) is `Relation.Binary.Construct.On.setoid (Carrier X) proj₁`.**
5. **Keep local, but cite.**
   - `Statistical.CommutativeMonoidWithZero`: agda-categories' `Object.Monoid` is not commutative.
   - `Model/Monad.PreS`: the pullback of the pointwise setoid along `∫` (`On.setoid`).  Naming it so makes B.1
     self-explanatory.

## D. Model semirings and classical logic

1. **Name excluded middle once.**
   - The hypothesis `∀ (P : Set ℓ) → P ⊎ (P → ⊥)` is spelled out 57 times.
   - `Model/BoolSemiring.agda:59-105` and `Model/ViterbiSemiring.agda:91-112` both define `dec`, `dec-true`,
     `dec-false`, `from-true` and `exfalso`.
   - Standard: `Axiom.ExcludedMiddle.ExcludedMiddle ℓ` (`{P} → Dec P`), with `isYes`, `toWitness`,
     `dec-true`/`dec-false` from `Relation.Nullary.Decidable`.
   - Do: first, a local `LEM ℓ` alias for the current form, used everywhere.  Then decide whether to move to
     `Dec`.
   - Risk: stdlib's `¬` uses level-0 `⊥`, while the semirings use `⊥ {ℓ}`.
2. **Invertibility is `Algebra.Definitions.RightInvertible 1# _*_ m`.**  Sites: `Model/Semiring.agda:42`
   `invertible?`, and `Model/StatInstance.agda:266, 289-290` (`InvDec`, inline in `normC′`).  Define `InvDec`
   once in `Semiring`.

## E. Cantor space, streams and Bool/ℕ helpers

1. **Cantor reindexing is copied across the discrete model.**
   - `φ`/`ι`/`ρ` are defined in `Model/Monad.agda:106-116`, `Model/Strong.agda:52-59` and
     `Model/Cantor.agda:22-27`.
   - The push-along-`φ n` proof (`push-∑`, `unpair-pair`) is repeated in `Model/Monad:133-147`, `Model/Strong:77-90`
     and `Model/ProbInstance:81-84`.  `ProbInstance.split` (:105-120) rebuilds `Cantor.cantorIso`.
   - Do: one `push-pair-∑` lemma in `Model/Cantor`.
   - Payoff: about 40 lines.
   - Risk: `RandomSource.pair` and `Model.Pairing.pair` are equal only through `DS`'s INLINE alias; watch the
     conversion cost.
2. **Interleaving.**
   - Now: `Borel/Merge.mergeC` (:24-39) indexes by parity (`ev`, `hf`).  That needs `Analysis/Interleave.agda:37-67`
     and `Continuous/Sample.agda:40-90` (`dbl`, `ev-dbl`, `hf-dbl`, `even-split`, `odd-split`).
   - Cheap option: `hf` is `⌊_/2⌋` (`Data/Nat/Base.agda:280`), `hf-dbl` is `sym (n≡⌊n+n/2⌋ n)`
     (`Data/Nat/Properties.agda:1996`), and `mergeBit b x y` is `if b then x else y`.
   - Full option: `merge a s 0 = a 0`, `merge a s (suc n) = merge s (tl a) n`, as in
     `Codata.Guarded.Stream.interleave` (:156).  Then `tl-merge` is `refl`.  But `measurable-merge₁/₂` and
     `Cyl-rect` must be redone, and 26 files import `mergeC`.
   - Start with the cheap option.
3. **Bool/Sum/ℕ helpers that exist in stdlib:**
   - `Clopen.agda:80-92` `∨-idʳ`/`∧-idʳ`/`∧-zeroʳ`/`∨-zeroʳ` are the `Data.Bool.Properties` `*-identityʳ`/`*-zeroʳ`
     lemmas.
   - `Clopen.¬true⇒false` (:176) is `¬-not`.
   - `Interleave.if-same` (:84) is `if-eta`, and `pick′-id` (:79) is `if-cong₂`.
   - `Merge.bool-dec` (:46) is `toSum (x ≟ y)`.
   - `Lead.decBool` is `isYes`; `Lead.¬<0` (:44) is `n≮0`; `Lead.pred<` (:73) is `s<s⁻¹`.
   - `CutSum` `Sum.copair` is `[_,_]`, and `inl-inj`/`inr-inj` are `inj₁/₂-injective`.

## F. Examples and inference

1. **`UniformMean` by self-similarity.**
   - Now: `Continuous/UniformMean` (133 lines) sums the bits with monotone convergence.
   - Do: reuse `UniformMoment`'s argument (:157-179): `expansion-cons` plus `FirstBit.firstBit-fun` give
     M = ½(½ + ½M) + ½(½M), so M ≈ ½ by `cancel`.  This is the self-similar characterisation of Lebesgue measure,
     as `Analysis/SelfSimilar` already uses for the CDF.
   - Payoff: about 90 lines, and one proof pattern for all moments.
   - Uncertain: check `cancel`'s hypotheses at this step.
2. **`Frequentist` copies `Estimator`.**
   - `Eval.natR` (:44-46) and `natS` (:132-134) copy `Analysis/Estimator.agda:40-46`.
   - `natS-eq`, `natR-eq`, `sum-eq`, `sq-eq` and `ss-eq` (:145-166) exist only to bridge the copies, and
     `Moments` (:117) restates `Estimator.Moments`.
   - Do: hoist `natS` out of `Estimator`'s ring module and reuse it.
   - Payoff: about 40 lines and the `subst` chains.

## G. Naming and documentation

- `Regular.Meas U m` (:63) means "U is ν-regular with measure m", and clashes with `Analysis.Meas`.  Rename it
  `Regular`.
- `ExtNat` is the classical `fin | ∞` encoding, not Escardó's ℕ∞; the docs should not suggest otherwise.  `Lead`
  needs `lem` only for the all-true sequence; with Escardó's ℕ∞ it would be constructive up to ℕ∞ → ℕ.  This
  deserves a doc remark, not a refactor.
- `Borel/Core.agda:28-40` could use `Relation.Unary` (`Pred`, `∁`, `⋃`, `⋂`).  Keep the local pointwise `_≐_`,
  which is not stdlib's.

## Checked and already standard

- `LowerReals.cutSemiring` builds a stdlib `CommutativeSemiring` via `Algebra.Structures.Biased`.
- `Signed` is the Grothendieck construction, built as a stdlib `CommutativeRing`.
- `SignedOmega.nat` uses `Algebra.Properties.Semiring.Mult`.
- `ViterbiSemiring` uses `Biased`.
- The monads, strengths and commutativity are agda-categories records, and the inclusion Prob ⇒ M is
  `Monad⇒-id`.
- `Exponential` uses `CartesianClosed.Canonical`; the non-canonical form would cost more.
- `Continuous/SubProb` reuses `Continuous/Monad` through `MeasureClass`.
- `Model/Pairing` (no stdlib Cantor pairing) and `BoolSemiring`'s `Lift` semiring have no library counterpart.

## Suggested order

1. Do A.3, A.4, A.6, C.1, C.4, D.1 (alias only) and E.3 first.  They are mechanical, local and low-risk.
2. Then A.1 and A.2 together: one `Half` module, then the `Poset` record.  This is the biggest readability gain in
   Analysis.
3. Then A.5 together with the `nat` and `½` cleanup.
4. Then B.3 and B.5 (colimits, codiscrete), and E.1.
5. Then B.1 and B.2, after plan 4's `Wit` item.  Time the canaries before and after (see plan 4, "To do: canary
   timings").
6. B.4, E.2 (full option), F.1 and F.2 as time allows.

Each step ends with `make check`, `make longcheck` and `make doccheck`.  Regenerate `docs/Modules.md` and update
`docs/Interface.md` when public names change.

## Stage 1 outcome (A.3, A.4, A.6, C.1, C.4, D.1, E.3)

`make check` (141 files, 0 holes, 0 failures), `make longcheck` and `make doccheck` pass; one commit per item.

* **A.3 done.**  `Indicators` imports `Series.psum`/`psum-inc`; `fsum`, `fsum-inc`, `Uniqueness.fsum-cong` and
  `Riesz.Bridge` are gone (`Fun-fsum` became `Fun-psum`).  `Riesz.μ-⋃` is now just `I-⋃`.
* **A.4 done.**  `I-cong` is a lemma in `Integration` (`I-mono` both ways, `≤-antisym`), with `m` still the first
  explicit argument; the field is dropped from all `Measure` instances (eight modules, ten records).
* **A.6 done, partly.**  `swap`/`mid`/`swap3`/`swap*` in `JSum`, `MixtureN`, `Density`, `Model/Strong`,
  `SFiniteCommute`, `SFiniteNorm` are `Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz` over
  `*-commutativeSemigroup`; `Series.+-interchange` and `ClopenMeasure.swap4` are `interchange` over
  `+-commutativeSemigroup` (`swap4` is re-exported, `OpenMeasure` uses it).  Not done: `Variance`'s `(-x)·x`, which
  is proved in the Grothendieck ring `Signed` via a solver on its parts, not by a `RingWithoutOne` lemma.
* **C.1 done.**  In `Probability`, `σ` is now the left strength and `τ` the right (`σ-unit`, `τ-point`, … swapped with
  them); `ψ` is documented as Kock's double strength.
* **C.4 done.**  `Limits.EqS` is `On.setoid (Carrier X) proj₁`.
* **D.1 done, alias only.**  New `QBS.Classical`: `LEM₀` (`Set`), `LEM₁` (`Set₁`, refuting into level-0 `⊥`) and
  `LEM ℓ` (refuting into `⊥ {ℓ}`).  `LEM ℓ` at `ℓ = zero` is *not* `LEM₀`: Polymorphic `⊥` is `Lift ⊥`.  So the
  `⊥ {L.zero}` hypothesis in `Example/Program.BoolDemo` and the `Set (L.suc L.zero)` hypotheses in
  `Model/{Viterbi,Additive}Model` stay as written.  `dec`/`from-true`/`exfalso` in `BoolSemiring`/`ViterbiSemiring` are
  untouched.
* **E.3 done, partly.**  `Clopen`'s `∨-idʳ`/`∧-idʳ`/`∧-zeroʳ`/`∨-zeroʳ` and `¬true⇒false` are stdlib
  (`∨-identityʳ`, …, `¬-not`); `Merge.bool-dec` is `toSum (x ≟ y)`; `Lead` uses `isYes`, `n≮0`, `s<s⁻¹`; `CutSum`
  uses `[_,_]′`, `inj₁-injective`, `inj₂-injective`.  Not done: `Interleave.if-same`/`pick′-id`, because stdlib 2.3 has
  no `if-eta`/`if-cong₂`.
