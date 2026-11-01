# Plan: simplify onto known structures

A library-wide audit, done 2026-10-31 on the `probes-site` branch (after `d8e9b5f`).  It looks for places where the
library reinvents a structure from the stdlib, agda-categories, or the literature, or duplicates its own
definitions.  Status (2026-11-01): Stages 1, 1a, 2 (A.1, A.2, B.3, B.5, E.1) 3 (A.5, A.7, B.2, C.3, D.2, E.2 cheap, F.1, F.2) and 4 (B.1 partly, B.4, G partly) are complete and merged; everything else is open.  See
"Status at a glance" below, and the outcome sections at the end for details.

Guiding rule: when a structure is standard, name it as the literature does and use the library's bundle if one
exists.  When no library has it (an ordered semiring, a continuation monad on setoids), keep a local record but
shape it like the standard one, and cite the source in the module header.

Paths are relative to `src/QBS/`.  Stdlib paths are relative to `agda-stdlib/src/`.  Line numbers are as of the
audit.  Each item gives the payoff and then the risk.  Items are ranked by payoff within each section, and the
sections are in suggested order of work.

## Status at a glance

**Done (merged):**
- Stage 1: A.3, A.4, A.6, C.1, C.4, D.1 (alias only), E.3.
- Stage 1a: items 1, 2 (as theorems, see below), 3, 4, 5 (first half), 6.  Items 7 and 8 were tried or examined and closed.
  - Item 1 is *not* a redefinition: `QBSCat` stays a hand-built category over a record `Hom`.  `QBS.Category.Concrete`
    proves `QBSCat ≃ SubCategory Setoids …`, `Disc ⊣ Forget ⊣ Codisc`, and that `Forget` is continuous and cocontinuous.
    The direct `SubCategory` definition makes `SFiniteStat` run for over 19 minutes (tag `sigma-wip`).
  - Item 2 is a direct one-object `SubCategory` (`QBS.Category.Measurable`) with a full and faithful `yoneda` embedding.
- Stage 2: A.1, A.2, B.3, B.5, E.1 (see the "Stage 2 outcome" sections).
- Stage 3: A.5, A.7, B.2, C.3, D.2, E.2 (cheap option), F.1, F.2 (see the "Stage 3 outcome" sections).
- Stage 4: B.1 (monad and strength laws; commutativity and `Model/Strong` left), B.4, G (rename and doc remarks; `Borel/Core` left).  See the "Stage 4 outcome" sections.

**Open:**
- A.8 (uncertain).
- B.1 remainder: commutativity is not generic, and the Continuous model keeps its own `TM` and strength (see the Stage 4 follow-up).
- C.2, C.5; E.2 (full option only); G: `Borel/Core` onto `Relation.Unary` (judged not worth it).
- Stage 1a item 5, second half: `measₛ`/`idxₛ` (`Borel/Source`) and `witₛ` are still separate constructors.
- Stage 1a item 4: 2 `random-cast` sites remain (`Exponential`, `Continuous/Monad`); B.2 removed the `SFinite*` ones.

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
5. **[done]** **`RationalLemmas` re-proves stdlib.**
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
7. **[done]** **`Bayesian.pow` (`Inference/Bayesian.agda:39`) is `_^_`**, with `x ^ suc n = x * x ^ n`.
   `likSeq-counts` can then use `Algebra.Properties.Semiring.Exp`.
8. **Finite sums against `Algebra.Properties.CommutativeMonoid.Sum`** (uncertain).
   - `psum-+`, `psum-scale` and `psum2-flip` are `∑-distrib-+`, `*-distribˡ-sum` and `∑-comm`.  But stdlib sums
     over `Fin n` with `foldr`, while `psum` adds on the right.
   - Worth a bridge `psum a N ≈ ∑[ i < N ] a (toℕ i)` only if more finite-sum algebra is coming.

## B. Measures and monads: one construction instead of three

1. **[monad and strength laws done]** **The monad presented by its integral (the largest single item).**
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
2. **[done]** **`WitM` duplicates `Continuous.Wit`.**
   - Sites: `SFinite.agda:126-182` (`WitM`, `TQ-resp/const/pre/glue`) against `Continuous/Monad.agda:116-123,
     150-169, 193-226`.  The only difference is `≈ᴹ` instead of `≈ᵖ`.
   - Do: parameterise `Wit` and the probes of `TQ` by an equivalence `_≋_` on `Pre X` with `≈ᵖ ⊆ ≋`.  Do this
     by parameterising on the raw family (Stage 1a item 7, re-indexing by `Func`, was tried and does not help).
   - Payoff: about 60 lines; `fromWit` goes.
   - Risk: keep the `abstract` blocks for compile time.
3. **[done]** **Colimits are one construction written three times.**
   - Sites: `_+Q_` (`Colimits.agda:73-101`), `CoeqQ` (`Colimits.agda:180-205`) and `ΣQ` (`Complete.agda:109-133`)
     each hand-write "α is random iff it is locally a piece".  The `random-resp`, `const-random`, `pre-random`
     and the `glue-random`/`unpair-pair` proof are identical in all three.
   - Do: one constructor from (setoid `Z`, pieces `P`, `ev : P → R → Z`, `pre` with an `ev-pre` law, a constant
     piece) to `Probes` plus `glue-random`.
   - In site terms, this is the sheaf generated by a presheaf of pieces.  In HKSV (LICS 2017), it is the QBS
     structure generated on coproducts and quotients.
   - Payoff: about 60 lines.
   - Risk: low to moderate.  `_+Q_` needs a case split for `ev-pre`.
4. **[done]** **Measures form a cone.**
   - Now: `Mixture.agda:25-77` proves all six `Measure` laws for `½m₁ + ½m₂` by hand.  `MixtureN`, `Density`,
     `Restrict` and `SubProb` repeat the scaling pattern.
   - Standard: valuations form a cone, a module over [0,∞] (Jones–Plotkin 1989; Keimel–Plotkin).
   - Do: generic `scaleM c m` (with `c ≤ 1` for `I-sub`) and `addM` (with a mass bound).  Then
     `mix = addM (scaleM ½ m₁) (scaleM ½ m₂)`.
   - Risk: moderate, from the side conditions; `MixtureN` must stay countable.
5. **[done]** **The codiscrete QBS is built three times.**
   - Sites: `Example/Program.Disc` (:51), `Model/StatInstance.WQ` (:63), `Limits.1Q` (:34).
   - It is the right adjoint of the forgetful functor (HKSV 2017).  One `codiscrete : Setoid → QBS S` would cover
     all three.
   - Update: `QBS.Category.Concrete.CodiscQ` now exists with the adjunction `Forget ⊣ Codisc` proved; reuse it or move it down.

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
3. **[done]** **Small agda-categories reuses.**
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
2. **[done]** **Invertibility is `Algebra.Definitions.RightInvertible 1# _*_ m`.**  Sites: `Model/Semiring.agda:42`
   `invertible?`, and `Model/StatInstance.agda:266, 289-290` (`InvDec`, inline in `normC′`).  Define `InvDec`
   once in `Semiring`.

## E. Cantor space, streams and Bool/ℕ helpers

1. **[done]** **Cantor reindexing is copied across the discrete model.**
   - `φ`/`ι`/`ρ` are defined in `Model/Monad.agda:106-116`, `Model/Strong.agda:52-59` and
     `Model/Cantor.agda:22-27`.
   - The push-along-`φ n` proof (`push-∑`, `unpair-pair`) is repeated in `Model/Monad:133-147`, `Model/Strong:77-90`
     and `Model/ProbInstance:81-84`.  `ProbInstance.split` (:105-120) rebuilds `Cantor.cantorIso`.
   - Do: one `push-pair-∑` lemma in `Model/Cantor`.
   - Payoff: about 40 lines.
   - Risk: `RandomSource.pair` and `Model.Pairing.pair` are equal only through `DS`'s INLINE alias; watch the
     conversion cost.
2. **[cheap option done]** **Interleaving.**
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

1. **[done]** **`UniformMean` by self-similarity.**
   - Now: `Continuous/UniformMean` (133 lines) sums the bits with monotone convergence.
   - Do: reuse `UniformMoment`'s argument (:157-179): `expansion-cons` plus `FirstBit.firstBit-fun` give
     M = ½(½ + ½M) + ½(½M), so M ≈ ½ by `cancel`.  This is the self-similar characterisation of Lebesgue measure,
     as `Analysis/SelfSimilar` already uses for the CDF.
   - Payoff: about 90 lines, and one proof pattern for all moments.
   - Uncertain: check `cancel`'s hypotheses at this step.
2. **[done]** **`Frequentist` copies `Estimator`.**
   - `Eval.natR` (:44-46) and `natS` (:132-134) copy `Analysis/Estimator.agda:40-46`.
   - `natS-eq`, `natR-eq`, `sum-eq`, `sq-eq` and `ss-eq` (:145-166) exist only to bridge the copies, and
     `Moments` (:117) restates `Estimator.Moments`.
   - Do: hoist `natS` out of `Estimator`'s ring module and reuse it.
   - Payoff: about 40 lines and the `subst` chains.

## G. Naming and documentation

[done except `Borel/Core`; see the Stage 4 outcome.]

- `Regular.Meas U m` (:63) means "U is ν-regular with measure m", and clashes with `Analysis.Meas`.  Rename it
  `Regular`.
- `ExtNat` is the classical `fin | ∞` encoding, not Escardó's ℕ∞; the docs should not suggest otherwise.  `Lead`
  needs `lem` only for the all-true sequence; with Escardó's ℕ∞ it would be constructive up to ℕ∞ → ℕ.  This
  deserves a doc remark, not a refactor.
- `Borel/Core.agda:28-40` could use `Relation.Unary` (`Pred`, `∁`, `⋃`, `⋂`).  Keep the local pointwise `_≐_`,
  which is not stdlib's.

## Stage 1a: simplifications in `Core` and the probes site

Moved here from `plans/04-equality.md` ("Further simplifications noticed during the sweep").  **Status: complete; see "Stage 1a outcome", "Stage 1b outcome" and "Stage 1c outcome".**  Items 4, 5, 6 and 7 touch compile-critical code, so time the canaries (plan 4, "Canary timings") before and after.  Ordered by payoff; suggested execution order is 6, 5, 3, 4, then 1 and 2 together, then 7, then 8.

Ordered by payoff.  Each one swaps a local definition for a standard structure, or removes a repeated idiom.

1. **[done as an equivalence, Stage 1c]** **`QBSCat` as an agda-categories `SubCategory` of `Setoids`.**  A `Hom` is a setoid map plus a property
   (`map-random`) that is closed under `id` and `∘`.  That is exactly `Categories.Category.SubCategory.SubCat`:
   take `U = Carrier`, `R f = ∀ {α} → Random X α → Random Y (f ∘ₛ α)`, `Rid = id`, and `_∘R_` = composition.
   `Category.agda` would then get `assoc`/`identity`/`equiv`/`∘-resp-≈` for free.  It would also get the faithful
   forgetful functor to `Setoids`, which is the "concrete" in concrete sheaf.  `_≈H_` would become
   `Function.Relation.Binary.Setoid.Equality._≈_` on `map`.
2. **[done, Stage 1c]** **`Measurability` as the same construction, with one object.**  `Meas` with `meas-id`/`meas-∘` is
   `SubCat ⊤` of `Setoids` with `U _ = Rˢ`: the site's single-object category, i.e. a submonoid of
   `Function.Relation.Binary.Setoid.Equality.setoid Rˢ Rˢ`.  `meas-ext` is the statement that `R` respects that
   setoid.  `Probes M X` is then a subfunctor of `Hom(−, X)` restricted to that category: a sub-presheaf of the
   representable, as the comment in `Core` already says in words.  Doing (1) and (2) together makes `probe`/`unprobe`
   literally Yoneda in agda-categories terms.
3. **[done]** **Name the composite cover.**  `glueₛ j (λ n → pairₛ n ∘ₛ i n)` is written out four times (`Core.idx-glue`,
   `Colimits` ×2, `Complete`).  A `refineₛ j i` in `Core` (the composite cover of `j` by the `i n`) would make
   `idx-glue : Idx j → (∀ n → Idx (i n)) → Idx (refineₛ j i)` read as the coverage axiom it is.
4. **[done; 4 sites left]** **Remove the `random-cast X (λ _ → refl)` casts (22 sites, 11 files).**  Every one has a `refl` proof: the two
   `Func`s share `to` and differ only in `cong`.  There are two root causes:
   * Gluing under a projection.  `glue-random` returns `glueₛ i (λ n → g ∘ₛ α n)` where `g ∘ₛ glueₛ i α` is
     wanted (`×Q`, `EqQ`, `ΠQ`, `glueRX`).  One naturality lemma, `random-glue-∘ : Random (glueₛ i (g ∘ₛ α n)) →
     Random (g ∘ₛ glueₛ i α)`, stated once in `Core`, would replace them.
   * The discrete model's `⇑` versus a composite (`Model/Monad`, `Strong`, `ProbInstance`, `StatInstance`).  These
     would disappear if `Model` stored `Pre.α` as a `Func`, as `Continuous/Monad` now does, instead of a raw `α`
     with `α-random : Random X (⇑ α)`.
   The alternative is to index `Random` by `to` alone and keep `Func` only at the interface.  That would kill both
   the casts and the "implicit `Func` is not inferable" pitfall, but it reintroduces a `cong` field.  It is worth
   trying only if the two fixes above do not clear most sites.
5. **[first half done]** **One raw-function-to-`Func` constructor.**  `⇑` (`Model/Monad`, for `≡`-discrete `R`), `measₛ`/`idxₛ`
   (`Borel/Source`) and `witₛ` (`Continuous/Monad`) all have the shape "`to` plus a proof that it respects `≈`".
   `⇑` is the stdlib's `→-to-⟶`, which is deprecated with no `Func` successor.  So keep `⇑`, but move it to `Core`
   next to `constₛ`.
6. **[done]** **`reassoc` is defined twice** (`Continuous/Monad`, `SFiniteMonad`): `(r , s) ↦ (merge r (evens s) , odds s)`.
   Export it once from `Continuous/Sample`, next to `mergeR`/`evensR`/`oddsR`.
7. **[tried, closed]** **Witness indexing.**  `Wit β` is indexed by the raw family, while `Wit-cong`/`witₛ` show that every witness
   already yields a `Func`.  Once (4) lands, try indexing `Wit`/`WitM` by `Func Rˢ (PreS X)`.  The earlier attempt
   failed only because `C.PreS` and `PreMS` put different equalities on one carrier.  Indexing by the carrier map
   `Func Rˢ (Carrier X)`, with `≈ᵖ` kept separate, may avoid that.
8. **[closed, nothing to collapse]** **`Idx` is the probes of a discrete QBS.**  `Partitions` is `Probes M ℕˢ` plus gluing, which is `glue-random` for
   the coproduct `∐ℕ 1`.  The circularity (a `QBS` needs `Idx`) prevents defining it as a QBS in `Core`.  But
   `Colimits` could expose `ℕQ` with `probes = partitions` and `glue-random = idx-glue`-derived, so countable
   coproducts and `idx-*` lemmas share one source.

Kept local on purpose: `constₛ` (stdlib `Function.Construct.Constant.function` requires both setoids to have the same
equality level, and `Rˢ`/carriers differ); `glueₛ` (no stdlib counterpart); setoid products are already the
stdlib's (`Data.Product.Function.NonDependent.Setoid`: `<_,_>ₛ`, `proj₁ₛ`, `swapₛ`, `_×-function_`).

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

Status: steps 1–6 are done (B.1 without generic commutativity); in step 7, B.4, F.1, F.2 and E.2 (cheap) are done, and the full E.2 is open.

1. Do A.3, A.4, A.6, C.1, C.4, D.1 (alias only) and E.3 first.  They are mechanical, local and low-risk.
2. Stage 1a (the `Core`/probes items above; partly done, see "Stage 1a outcome"): B.3 then builds on `refineₛ` and the
   cleaned casts, (item 7 was tried and closed).
3. Then A.1 and A.2 together: one `Half` module, then the `Poset` record.  This is the biggest readability gain in
   Analysis.
4. Then A.5 together with the `nat` and `½` cleanup.
5. Then B.3 and B.5 (colimits, codiscrete), and E.1.
6. Then B.1 and B.2 (Stage 1a item 7 turned out not to be a prerequisite).  Time the canaries before and after (see plan 4, "To do: canary
   timings").
7. B.4, E.2 (full option), F.1 and F.2 as time allows.

Each step ends with `make check`, `make longcheck` and `make doccheck`.  Regenerate `docs/Modules.md` and update
`docs/Interface.md` when public names change.

## Stage 1 outcome (A.3, A.4, A.6, C.1, C.4, D.1, E.3)

`make check` (141 files, 0 holes, 0 failures), `make longcheck` and `make doccheck` pass; one commit per item.

* **A.3 done.**  `Indicators` imports `Series.psum`/`psum-inc`; `fsum`, `fsum-inc`, `Uniqueness.fsum-cong` and
  `Riesz.Bridge` are gone (`Fun-fsum` became `Fun-psum`).  `Riesz.μ-⋃` is now just `I-⋃`.
* **A.4 done.**  `I-cong` is a lemma in `Integration` (`I-mono` both ways, `≤-antisym`), with `m` still the first
  explicit argument; the field is dropped from all `Measure` instances (eight modules, ten records).
* **A.6 done.**  `swap`/`mid`/`swap3`/`swap*` in `JSum`, `MixtureN`, `Density`, `Model/Strong`,
  `SFiniteCommute`, `SFiniteNorm` are `Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz` over
  `*-commutativeSemigroup`; `Series.+-interchange` and `ClopenMeasure.swap4` are `interchange` over
  `+-commutativeSemigroup` (`swap4` is re-exported, `OpenMeasure` uses it).  `Variance.neg-mul` is `-‿distribˡ-*`
  from `Algebra.Properties.Ring` on `Signed.signedRing`, and `AlgNeg` is gone.
* **C.1 done.**  In `Probability`, `σ` is now the left strength and `τ` the right (`σ-unit`, `τ-point`, … swapped with
  them); `ψ` is documented as Kock's double strength.
* **C.4 done.**  `Limits.EqS` is `On.setoid (Carrier X) proj₁`.
* **D.1 done, alias only.**  New `QBS.Classical`: `LEM₀` (`Set`), `LEM₁` (`Set₁`, refuting into level-0 `⊥`) and
  `LEM ℓ` (refuting into the level-polymorphic `⊥ {ℓ}`).  `LEM ℓ` at `ℓ = zero` is *not* `LEM₀`, because the
  polymorphic `⊥` is `Lift ⊥`, so the three aliases are kept apart and each hypothesis keeps its original form.
  `LEM ℓ` is used in `Model/{Bool,Additive,Viterbi}{Semiring,Model}`, `Example/{Program,Probability}` and
  `Inference/CoinBias`.  Not touched: `dec`/`from-true`/`exfalso` in `BoolSemiring`/`ViterbiSemiring`, and the
  decision *arguments* (`pick*`, `borel-const`), which are not hypotheses.
* **E.3 done.**  `Clopen`'s `∨-idʳ`/`∧-idʳ`/`∧-zeroʳ`/`∨-zeroʳ` and `¬true⇒false` are stdlib
  (`∨-identityʳ`, …, `¬-not`); `Interleave.if-same`/`pick′-id` are `B.if-eta`/`B.if-cong₂` (the two branch proofs swap
  places); `Merge.bool-dec` is `toSum (x ≟ y)`; `Lead` uses `isYes`, `n≮0`, `s<s⁻¹`; `CutSum` uses `[_,_]′`,
  `inj₁-injective`, `inj₂-injective`.

## Stage 1a outcome (items 3, 5, 6 and half of 4; 1, 2, 7, 8 deferred at the time; superseded by the Stage 1b and 1c outcomes)

`make check` (141 files, 0 holes, 0 failures), `make longcheck` (36 flagged, unchanged from stage 1) and `make doccheck`
pass; one commit per item.  Canaries (forced recheck, `--profile=modules`, warm interfaces, two runs each, on `main`
before vs this branch after): `Probability` 4.86 vs 5.07 s, `Exponential` 2.59 vs 2.81 s, `Continuous/Monad` 3.36 vs
3.57 s, `SFiniteMonad` 4.42 vs 4.57 s, `SFiniteNorm` 6.28 vs 6.49 s, `SFiniteStrong` 4.89 vs 5.03 s, `StatInstance`
10.55 vs 10.49 s; memory within 10 % (`SFiniteMonad` 516 vs 567 MB).  Re-timed on the same machine state, the baseline had itself drifted up 2–3 %.  Stage 1b's run then showed `Exponential` back at 2.64 s without `Exponential` or `Core` changing, so the residual 5–6 % seen on `Exponential`/`Probability` here was drift, not a cost of the `Core` additions.  Moving `Forget` into its own module made no difference either.

* **6 done.**  `reassocR` is exported from `Continuous/Sample`; both local copies are gone.
* **5 done, first half.**  `⇑` now lives in `Core` next to `constₛ`, for any `≡`-setoid.  The second half (one
  constructor for `measₛ`/`idxₛ`/`witₛ`) is skipped: each is already just `record { to ; cong }` with its own `cong`
  proof, so no lines would be saved.
* **3 done.**  `refineₛ` (in `NatPairing`) names the composite cover; `idx-glue` and the three `glue-random` proofs use it.
* **4 half done.**  `Probes.random-glue-∘` replaces the four glue-under-projection casts (`×Q` ×2, `EqQ`, `ΠQ`).  The
  second root cause (the discrete model's raw `α : R → ∣X∣`) is deferred: making `Pre.α` and `Wit.wα` `Func`s rewrites
  `α p r` into `α p ⟨$⟩ r` throughout `Model/{Monad,Strong,ProbInstance,StatInstance,SubProb}` (about 12 casts), and those
  modules are compile-time sensitive.  The `Exponential` and `Continuous/Monad` casts are precomposition, not
  projection, patterns and remain (18 `random-cast` sites left).
* **1 and 2 partly done, rewrite deferred.**  80 `map-random =` sites in 28 files build `Hom` records, so redefining
  `QBSCat` as a `SubCat` (a Σ-typed hom) would touch all of them and change the normal forms the CCC and monad
  conversions rely on.  Instead the new module `QBS.Category.Forget` has `Forget : Functor (QBSCat S) (Setoids ℓ ℓ)` and `Forget-faithful`.
  `Measurability` as a one-object `SubCat` is untouched.
  *Superseded by the Stage 1c outcome below.*
* **7 deferred**, since it follows the unfinished half of 4.  **8 deferred**: a `ℕQ` in `Colimits` would need the
  circular `Idx`/`QBS` dependency broken first and was not attempted.

## Stage 1b outcome (item 4, second half; 7 and 8 closed)

`make check` (142 files, 0 holes, 0 failures), `make longcheck` (36 flagged) and `make doccheck` pass.

* **4b done.**  The `Exponential:63` and `Continuous/Monad:153` casts look alike but are not: `Exponential`'s map is a bespoke
  record rather than `glueₛ`, so a precomposition lemma (`random-glue-pre`, tried and reverted) clears only one site.
  The `SFinite`/`SFiniteMonad` casts belong with B.2.  In `Model/Monad`, `Pre.α` and `Wit.wα` became `Func`s, `αₛ` and `wαₛ`; `α p r` and `wα w r` remain as
  functions defined from them, so most uses are unchanged.  Constructing a `Pre` now takes a `Func` (`map f ∘ₛ αₛ p`,
  `constₛ x`, `< constₛ x , αₛ q >ₛ`, `⇑ face`), and the discrete model's `random-cast`s are gone (22 sites before,
  4 left, none in the discrete model).  Touched: `Model/{Monad,Strong,ProbInstance,StatInstance}`,
  `Example/{Program,Bayes,HardConditioning,Conditioning}` and `Inference/Bayesian`.
  Canaries, this branch vs the earlier Stage 1a run (labelled "main" here; not re-run in the same session) (two runs each): `Probability` 5.00 vs 5.25 s, `Exponential` 2.64 vs 2.81 s,
  `Continuous/Monad` 3.43 vs 3.57 s, `SFiniteMonad` 4.55 vs 4.56 s, `SFiniteNorm` 6.45 vs 6.44 s,
  `SFiniteStrong` 5.02 vs 5.04 s, `StatInstance` 9.32 vs 10.58 s (-12 %); memory unchanged.  The earlier 5 % Stage 1a
  cost on `Exponential`/`Probability` shows up as drift here, so treat the small differences as noise.
* **7 tried and reverted.**  I indexed `Continuous/Monad.Wit` by `Func Rˢ (PreS X)`; `Continuous/Monad` itself checked
  (16 lines added, 30 removed, with `Wit-cong` and `witₛ` deleted).  It then fails in `Continuous/SFinite.fromWit`
  (`β has type R₁ → Pre (XW X)` where `Func Rˢ (C.PreS (XW X))` is wanted) and in `SFiniteNorm:459`, the only user of
  `witₛ`.  Both start from a raw family plus a witness and need the congruence that `Wit-cong` proves, so the obligation
  moves to the use site rather than going away.  `WitM` cannot take a `Func` into `PreMS` instead, since `fromWit`
  would then compare two `Func`s with the same `to` and different `cong`.  Net: no line saving.  Item 7 is closed as
  not worthwhile.  B.2 should parameterise `Wit` by `_≋_` on the raw family, not re-index it.
* **8 closed, nothing to collapse.**  No discrete-ℕ QBS is rebuilt anywhere: `Colimits` and `Complete` use `idx-const` and
  `idx-pre` directly.  `ℕQ` would be a pure addition with no consumer.  (Not the circularity the first draft cited: the
  plan always put it in `Colimits`, not `Core`.)

## Stage 1c outcome (items 1 and 2, as a comparison)

* **Step 1 kept**: hom equality takes its point implicitly, matching `Setoids`; no canary cost (within 2-3 % of a same-session baseline).
* **Redefining `QBSCat` as a `SubCategory` (Σ homs) abandoned** (tag `sigma-wip`).  It compiled up to `Continuous/SFiniteStat`, which then ran over 19 minutes
  (an earlier full check, 39).  Hypothesis, not profiled: `Hom X Y` and `Category._⇒_` both unfold to a `Σ`, so Agda unifies
  `Carrier ?X` against nested carriers (`Carrier` is not injective), the cost the library already records for `QBSCat` conversions.
* **Done instead**: `QBS.Category.Concrete` keeps the record `Hom` and proves the subcategory form as a theorem.
  `QBSSub` is the `SubCategory` of `Setoids` with `R` = probe preservation; `QBS≃Sub` is a strong equivalence with both functors the identity on objects;
  `Sub ∘ ToSub = Forget` holds by `refl`.  `CodiscQ` (every sequence random) and `DiscQ` (random = locally constant along a measurable partition,
  glued with `idx-glue`) give `Disc ⊣ Forget ⊣ Codisc`; `rapl′`/`lapc′` then give `Forget` continuous and cocontinuous, `Codisc` continuous,
  `Disc` cocontinuous; `Disc` and `Codisc` are faithful.  No downstream module changed.
* **Item 2 done** (`QBS.Category.Measurable`): `MeasCat` is a direct one-object `SubCategory` (no comparison needed: no downstream users, nothing to unify).
  `yoneda : MeasCat → QBSCat S` sends the object to `ℛQ` and is full (`unprobe`) and faithful; `Forget ∘ yoneda` and the subcategory inclusion agree by `refl`.

## Stage 2 outcome (A.1, A.2)

`make check` (145 files, 0 holes, 0 failures), `make longcheck` (36 flagged, unchanged) and `make doccheck` pass.  Two commits on `simplify-half`; `src/` is +334/-262 lines
including the new 84-line `Half.agda` (net +72; -12 without it, so the payoff is clarity, not size).  No canary modules (`Model/`, `SFinite*`, `Probability`, `Exponential`) were touched, so none were timed;
the whole `make check -j4` took about 2 minutes either side.

* **A.2 done.**  `OrderedSemiring` has `isPartialOrder : IsPartialOrder _≈_ _≤_` and a `poset`; `≤-reflexive`, `≤-trans`, `≤-antisym`, `≤-refl` and `≤-resp-≈` are re-exported
  projections, so no user changed.  The two instances (`LowerReals`, `ExtNat`; the plan said "`Min`", but `Min` is not an instance) build the record.
  The 3-argument `≤-resp` was *not* renamed: stdlib's `≤-resp-≈` is a `Respects₂` pair and now holds that name, so `≤-resp` stays as a derived lemma.
  Header cites Kuich and Ésik–Kuich.  Skipped: `Min` as `Infimum`/`mn-mono` as `∧-monotonic` (`Min` is a separate record with 12 uses, `mn-mono` is two lines)
  and the `Relation.Binary.Reasoning.PartialOrder` conversion of the 67 idioms (not needed).
* **A.1 done.**  `QBS.Analysis.Half` (over `A`, `half`, `half+half`): `hp = half ^ n` (stdlib; `hp (suc n) = half * hp n` is `refl`), `half-twice`, `hp-double`, `hp-unique`,
  `geoF`/`geom`/`geo`/`geo-sum`.  `Arch` now has only `half`, `half+half`, `arch`, `cancel≤`, `way-below`, plus `open Half … public` and the generic
  `∑hp≤1`/`∑hp≈1` (moved from `JSum`).  Removed: `ArchLemmas`, `BinaryExpansion.hpow/geom`, `HalfOrder.half-twice`, `Interleave.half-double`, the `double-half` proof and
  `two` in `ClopenMeasure`, `SelfSimilar.hp-half`, `Unbounded.half-hp`, `JSum.hp-geo`, `UniformMean.hp≈hpow` and `geom-sum`.  `BoundedCancel.pow2` is now ℕ `2 ^ k`.
* **Different from the plan.**  `LowerRealsArch` needed no `qC`-commutes-with-`*` lemma: any sequence with `h 0 = 1` and `h (n+1) + h (n+1) = h n` equals `hp` (`Half.hp-unique`,
  using `half-twice`), so `hpC n ≋ hp n` follows from `hpC-double`.  The ℚ-valued `tp`/`hpC` stay because `CoinIntegral` and `arch-⊑` do rational ε-arguments with them;
  `Lebesgue` now uses `Arch.hp`.  `Unbounded.pw`/`Min.Pow.pw` (2ᵏ inside `A`) also stay: they are powers of 2, not of ½, and `hp-pw` ties them to `hp`.

## Stage 2 outcome (B.3, B.5)

`make check` (144 files, 0 holes, 0 failures), `make longcheck` (36 flagged, baseline) and `make doccheck` pass.  9 files, +76 −149.
Canary `StatInstance` 10.1 vs 10.0 s (concurrent builds; noise).

* **B.3 done.**  `Core.GluedQBS S Z P ev pre ev-pre pt` is the QBS generated by a presheaf of pieces (random = locally a piece
  along a countable partition; cites HKSV 2017), with the gluing proof written once via `refineₛ`.  `_+Q_`, `CoeqQ`, `ΣQ` and
  also `Concrete.DiscQ` are one-line instances; the random-element shape `(i , ii , c , q)` is unchanged, so `copair`,
  `coeq-hom`, `copairΣ` and the injections needed no edits.  `0Q` stays separate (no pieces).
* **B.5 done.**  `CodiscQ` moved from `Concrete` down into `Core` (since `Concrete` imports `Forget`); `Limits.1Q`,
  `Example/Program.Disc` and `Model/StatInstance.WQ` (each `Random = λ _ → ⊤`) are now `CodiscQ S …`.

## Stage 2 outcome (E.1)

`make check` (144 files, 0 holes, 0 failures), `make longcheck` (36 flagged, baseline) and `make doccheck` pass.  5 files, +31 −60.
Canaries (forced recheck, concurrent builds, so noisy; "before" taken right after a cold build): `Model/Monad` 3 vs 3 s, `Model/Strong`
22 vs 14 s, `Model/ProbInstance` 7 vs 5–6 s, `Model/StatInstance` 14 vs 7 s.  Treat the drops as mostly noise; nothing got slower.

* **E.1 done.**  `φ`, `ιR`, `ρR` are defined once in `Model/Cantor`; `Model/Monad` and `Model/Strong` no longer define their own or open
  `RandomSource`'s `pair`/`unpair`.  New `Cantor.push-pair-∑ n μ H : ∑ k. push (φ n) μ k * H (unpair k) ≈ ∑ m. μ m * H (n , m)` replaces the
  `push-∑` + `unpair-pair` chain in `Model/Monad` (`TQ` glue), `Model/Strong` (`σH`) and `Model/ProbInstance` (`kerH`; `kerEq` is gone).
  `ProbInstance.split` is built from `Cantor.cantorIso` (`Inverse.from`/`to`/`inverse`).  `Monad.ι : R → ℕ` stays, as `lower (ιR r)`,
  since `glueₛ` needs a ℕ index.  The `DS` alias concern did not materialise.  Saving is ~30 lines rather than ~40: the lemma takes an
  explicit `H` and the call sites keep their lambdas.  Skipped: moving `φ`/`ιR`/`ρR` out of `module Cantor A` (they do not use `A`).

## Stage 3 canaries (A.5, A.7, B.2, C.3, D.2, E.2, F.1, F.2)

Timed by the orchestrator after all merges, with no other builds running (macOS indexing still active): forced recheck (delete the
module's `.agdai`, rerun `agda`, warm dependencies), `1ddb9d4` (main before Stage 3) vs `7fc2fe5`+B.2 (after), interleaved, two runs each, in seconds.
Everything is within 3 %, slightly faster if anything; no regression from B.2's generic `WitProbes`.

| Module | before | after |
|---|---|---|
| `Probability` | 5.20 / 5.13 | 4.95 / 4.95 |
| `Exponential` | 2.75 / 2.75 | 2.66 / 2.68 |
| `Model/Monad` | 2.61 / 2.64 | 2.63 / 2.55 |
| `Model/ProbInstance` | 5.02 / 5.02 | 4.94 / 4.93 |
| `Model/StatInstance` | 6.98 / 6.97 | 6.90 / 6.89 |
| `Continuous/Monad` | 3.57 / 3.46 | 3.47 / 3.48 |
| `Continuous/SFiniteMonad` | 4.68 / 4.68 | 4.60 / 4.64 |
| `Continuous/SFiniteNorm` | 6.56 / 6.54 | 6.48 / 6.39 |
| `Continuous/SFiniteStrong` | 5.14 / 5.14 | 5.04 / 5.02 |
| `Continuous/SFiniteStat` | 6.49 / 6.47 | 6.31 / 6.33 |

Note: three of the four Stage 3 worktrees were first cut from a stale `main` (`7064e52`, before Stage 2); all were rebased or merged onto current
`main`, and the merged tree passes `make check` (145 files), `make longcheck` (36 flagged) and `make doccheck`.

## Stage 3 outcome (A.5, A.7)

`make check` (145 files after merge, 0 holes, 0 failures), `make longcheck` (36 flagged, unchanged) and `make doccheck` pass; one commit per item.
13 files, +99 −195.

* **A.5 done.**  The ~40 one-line aliases in `RationalLemmas` are two `open P public using/renaming (…)` blocks (renames `≤-≃`, `<-≤`,
  `≃-<ʳ`, `≃-<ˡ`, `dense`, `total`, `not-≤⇒<`; `≤-resp` stays local).  `*-mono-<-posʳ`, `*-mono-≤-nnʳ`, `*-pos`, `+-pos`, `≤-+ʳ` are thin
  wrappers over `*-monoˡ-<-pos`, `*-monoˡ-≤-nonNeg`, `pos*pos⇒pos`, `pos+pos⇒pos`, `p≤p+q` via the kept `pos`/`nonneg` adapters.
  `+-pos`/`+-neg` wrap the `≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< …)` idiom (11 sites in `LowerInverse`, `LowerReals`, `CutSum`, `LowerRealsArch`;
  `CutSum.pos-add`/`neg-add` and `LowerRealsArch.pos+` gone; `CoinIntegral:279` is a different shape and stays).  `nat-nonneg`/`nat-mono`
  live once in `RationalLemmas` (removed from `LowerRealsArch`, `Pieces`, `CoinGrid`, `SFiniteDecomp`).  `LowerRealsArch.hf` is stdlib `½`;
  `½+½ : ½ + ½ ≃ 1ℚᵘ` is `*≡* refl`, and `hf*2`, `0<hf` (by contradiction) and `0<2` are gone.  Not done: `≤-Reasoning` (no long chains
  at the edited sites).
* **A.7 done.**  `Bayesian.pow` is `_^_` from `Algebra.Properties.Semiring.Exp`; the false case of `likSeq-counts` is exactly
  `y*x^m*y^n≈x^m*y^[n+1]`, replacing the manual `*-assoc`/`*-comm` shuffle.
* The merge into `main` conflicted only in the
  generated `docs/Modules.md`.

## Stage 3 outcome (B.2)

`make check` (145 files, 0 holes, 0 failures), `make longcheck` (36 flagged, baseline) and `make doccheck` pass.  6 files, +99 −105.

* **B.2 done.**  `Continuous/Monad.Wit` takes an equivalence on `Pre X` (`Wit _≋_ β`), parameterised on the raw family, not re-indexed by
  `Func`.  The `TQ` probes (`TQ-resp/const/pre/glue`, with `pre-eq`/`glue-eq` folded in) are one generic module
  `WitProbes _≋_ ≋-sym ≋-trans (incl : ≈ᵖ ⊆ ≋)`; `C.TQ` uses it at `≈ᵖ`, `SFinite` at `≈ᴹ` (`WitM β = C.Wit _≈ᴹ_ β`, `module WitM = C.Wit`, so
  the `open WitM` in other `SFinite*` modules is unchanged).  `fromWit` became `Wit-mono` (a witness for a finer equivalence is one for a coarser).
  Both `SFinite*` `random-cast`s are gone (`SFinite.joinPre`, `SFiniteMonad`).
* **Smaller saving than planned** (net −6, not ~60): `WitProbes` is new, `Wit` gained an argument (`C.Wit.a {U} {_} {β}` at 12 sites in
  `SFiniteIncl`, `C.Wit {X} C._≈ᵖ_` at 2 in `SFiniteNorm`), and the `abstract` wrappers stay in `SFinite`.  `abstract` inside the generic module
  failed (it made `C.TQ`'s witnesses opaque; `ProbInstance.measure-tensor` then had unsolved metas at `joinPre`); the wrappers need eta-expanded
  implicits (`TQ-pre {X} {β} {f} = WP.TQ-pre {X} {β} {f}`).  `Wit-cong`/`witₛ` stay `≈ᵖ`-specific (they need `Fun-resp` on `≈ᵖ` integrals).

## Stage 3 outcome (C.3, D.2, E.2)

`make check` (145 files, 0 holes, 0 failures), `make longcheck` (36 flagged, baseline) and `make doccheck` pass.  10 files, +66 −86.

* **C.3 done.**  `Model/Monad.ηN`/`μN` use `ntHelper` (no `sym-commute` fields); `Statistical.rw` is gone (its two uses are
  `MR.extendʳ`); `Probability`'s `⟨id,!⟩∘π₁`/`⟨!,id⟩∘π₂` are the `isoˡ` of `CartesianMonoidal`'s `A×⊤≅A`/`⊤×A≅A` (first use of the `CM` import).
* **D.2 done.**  `InvDec m = RightInvertible _≈_ 1# _*_ m ⊎ (∀ n → m * n ≈ 1# → ⊥)` is defined once in `CompleteSemiring`; `invertible?`
  and `StatInstance` (local `InvDec`, inline type in `normC′`) use it.  `Continuous/SFiniteNorm` has its own `InvDec` over `Cut` (left alone).
* **E.2 (cheap) done.**  `Merge.hf` is `⌊_/2⌋` and `mergeBit` is `if_then_else_` (same clauses, so the rest stays `refl`);
  `Sample.hf-dbl` is `sym (n≡⌊n+n/2⌋ n)`; `hf-suc`/`hf-sdbl` renamed `half-suc`/`half-sdbl`; `Sample.dbl` stays.  Full stream-interleave option not attempted.

## Stage 3 outcome (F.1, F.2)

`make check` (145 files, 0 holes, 0 failures), `make longcheck` and `make doccheck` pass.  5 files, +109 −132.

* **F.1 done.**  `Continuous/UniformMean.mean` (statement unchanged) is now by self-similarity: `firstBit-fun` + `expansion-cons` give
  M = ½(½ + ½M) + ½(½M); a small `Alg.double` over an abstract `CommutativeSemiring` (the ring solver is slow on the concrete cut
  semiring) turns that into M + M ≈ ½ + M, and `cancel` (needing only M ≤ 1, via `I-mono` against 1) gives M ≈ ½.  The partial-sum
  machinery (`bitU`/`bitCyl`, `bit-scale`, `I-bit`, `I-part`, `I-sup`, bit probabilities, geometric sum) is gone; 133 → ~99 lines.
* **F.2 done.**  `Analysis/Estimator` has a top-level `NatIn R` with `nat`; `Estimator.natS`/`natR` and `Frequentist`'s copies are instances,
  so `natS-eq`/`natR-eq` and their `subst` chains are gone.  `Frequentist.Moments` is `∀ θ → Est.Moments …` (now in `Set₁`); `F.natS` no longer
  takes `moments`.  Kept: `sum-eq`/`sq-eq`/`ss-eq`, which relate `Term` evaluation to `Estimator.sumR`/`sq`/`SS` rather than bridging copies.

## Stage 4 canaries (B.1, B.4, G)

Forced recheck (delete the module's `.agdai`, warm dependencies), timed by the orchestrator on a quiet machine,
interleaved before/after, two runs each, in seconds.  Before = `2f35ffa`, after = main with B.1, B.4 and G merged.
`Continuous/Strong` was added as a canary because B.1 changes it.

| Module | Before | After |
|---|---|---|
| `Probability` | 5.04 / 5.03 | 4.96 / 4.96 |
| `Exponential` | 2.74 / 2.73 | 2.64 / 2.63 |
| `Model/Monad` | 2.60 / 2.58 | 3.00 / 2.97 |
| `Model/ProbInstance` | 5.03 / 5.00 | 4.96 / 4.94 |
| `Model/StatInstance` | 7.09 / 7.01 | 6.92 / 6.90 |
| `Continuous/Monad` | 3.49 / 3.51 | 3.55 / 3.56 |
| `Continuous/SFiniteMonad` | 4.67 / 4.75 | 4.76 / 4.79 |
| `Continuous/SFiniteNorm` | 6.56 / 6.55 | 6.42 / 6.39 |
| `Continuous/SFiniteStrong` | 5.15 / 5.16 | 4.44 / 4.44 |
| `Continuous/SFiniteStat` | 6.47 / 6.50 | 6.36 / 6.43 |
| `Continuous/Strong` | 41.65 / 41.29 | 48.59 / 48.43 |

`Continuous/Strong` is 17% slower (about 41.5 s to 48.5 s) and `Model/Monad` 15% slower (2.6 s to 3.0 s), both
from B.1.  `SFiniteStrong` is 14% faster.  The others are within 3%.

## Stage 4 outcome (B.1)

- New `QBS/IntegralMonad.agda` (229 lines), citing Kock (TAC 2012), Jacobs and Ścibior et al. 2018.  Records
  `Tests` (tests, `eval`, precomposition), `Integral` (`∫`, `∫-ext`, `∫-cong`), `MonadData` (`TH`, `ηH`,
  `joinH`, `∫-map`, `∫-η`, `∫-join`) and `IntegralStrength` (`σH`, `∫-σ`).  `module Laws` gives `TF`, `ηN`,
  `μN`, `TM`; `module StrongLaws` gives `σ-nat`, `strength`, `strongMonad`.  An 18-field single record pushed
  `longcheck` up by one, hence the split.
- Instantiated in `Model/Monad`, `Continuous/Monad`, `SFiniteMonad` (monad laws) and `Continuous/Strong`,
  `SFiniteStrong` (strength laws).  Downstream names are unchanged; `mapM`/`joinPre` stay `abstract`.
- Net +101 lines, not −180: the models lose about 235 and the generic module costs 229.  The gain is that a new
  model gets the monad and strength laws from about 40 lines of data.
- Left: `Model/Strong` (its strength laws are `refl`); commutativity everywhere (each proof is already
  `trans ∫-join (fubini …) (sym ∫-join)`, and a generic version needs the iterated integrals as `Test`s, which
  the Continuous models only have as raw integrals over R, with new measurability obligations).
- Cost: `Continuous/Strong` +17% and `Model/Monad` +15% (see the canaries).  The `INLINE` pragmas on `TM`/`TF`
  in `SFiniteMonad` went, since those are now definitions inside `Laws`.  Some unused imports remain.

## Stage 4 outcome (B.4)

- New `Analysis/Cone` (69 lines, citing Jones–Plotkin 1989 and Keimel–Plotkin): `zeroM`, `scaleM c (c ≤ 1#)`
  and `addM` with a mass bound.  `zeroM`/`scaleM` moved out of `Continuous/SubProb`.
- `Mixture.mix = addM (scaleM half half≤1 m₁) (scaleM half half≤1 m₂) (mix-bound …)`; the hand proofs and the ring
  solver go.  Net +87/−76 (the new module's header and citations); `longcheck` 36 → 35.
- Left: `MixtureN` is already the countable sum; `Density` scales a pre-measure without `I-sub`, so `scaleM` does
  not apply; `Restrict` composes with χ and does not scale; `Model/SubProb` has no `Measure` records.

## Stage 4 outcome (G)

- `Regular.Meas` is now `IsRegular` (no other module used the name).
- `ExtNat` and `Lead` headers say that `ExtNat` is the classical `fin n | ∞` encoding, not Escardó's ℕ∞, and that
  `Lead` needs `lem` only for the all-true sequence.
- Left: `Borel/Core` onto `Relation.Unary`.  54 modules import it, its `⋃`/`⋂` are constructors used in about 58
  places and clash with stdlib's names, and stdlib's `Pred A ℓ` differs from the local `Pred`.  No cheap partial
  adoption.
- C.4 was already done in Stage 1.

## Stage 4 follow-up (B.1: the `Continuous/Strong` slowdown)

- The 17% is spent checking `commutative` in `Continuous/Strong` (about 45 s of 48 s).  It appears whenever
  `Continuous.TM` is the generic `Laws.TM`, even if only the four monad-law fields are projections of it.  The
  mechanism is unknown.  `abstract` seals, `INLINE` on either side, and explicit implicit arguments in
  `commutative` did not help (several made it worse, up to 58 s).
- Fix: `Continuous/Monad` takes `TF`, `ηN`, `μN` from `Laws` but writes `TM` out with the original law proofs (with
  a comment saying why), and `Continuous/Strong` keeps its local `strength`/`strongMonad`.  About 47 lines stay
  model-side.  `Model/Monad`, `SFiniteMonad` and `SFiniteStrong` still use `Laws`/`StrongLaws`.
- Re-timed against `2f35ffa` the same way as above.  The machine was about 10% slower than for the Stage 4 table,
  so compare columns within this table only:

| Module | Before | After |
|---|---|---|
| `Deleted` | branch / (was | worktree-agent-adc866cd98e1b5a66 / ce63aed). |
| `Probability` | 5.56 / 5.54 | 5.45 / 5.45 |
| `Exponential` | 3.03 / 3.03 | 2.94 / 2.93 |
| `Model/Monad` | 2.87 / 2.87 | 3.29 / 3.28 |
| `Model/ProbInstance` | 5.50 / 5.51 | 5.43 / 5.42 |
| `Model/StatInstance` | 7.66 / 7.67 | 7.53 / 7.52 |
| `Continuous/Monad` | 3.87 / 3.87 | 4.14 / 4.11 |
| `Continuous/SFiniteMonad` | 5.17 / 5.16 | 5.27 / 5.27 |
| `Continuous/SFiniteNorm` | 7.27 / 7.34 | 7.11 / 7.15 |
| `Continuous/SFiniteStrong` | 5.69 / 5.75 | 5.02 / 4.96 |
| `Continuous/SFiniteStat` | 7.32 / 7.25 | 7.10 / 7.13 |
| `Continuous/Strong` | 44.94 / 44.81 | 44.54 / 45.03 |

`Continuous/Strong` is back to baseline.  `Model/Monad` (+14%, 0.4 s) and `Continuous/Monad` (+7%, 0.25 s) are
slower by small absolute amounts, the price of instantiating `Laws`; `SFiniteStrong` is 13% faster.  The rest are
within 3% or faster.
