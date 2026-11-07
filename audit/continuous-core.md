# Audit: continuous-core (43 modules in src/QBS/Continuous/)

Reading audit only; nothing was compiled.  Line numbers are from the working tree at the time of reading.

## 1. Summary

This domain builds the *continuous* probability model on quasi-Borel spaces over Cantor space.  A measure on X is a
pair [α, m] of a random element α : 2^ℕ → X and a probability measure m on 2^ℕ, identified when every [0,1]-valued
test integrates equally (`Monad`).  Random families of measures are witnessed by a *joint* probe (r, s) ↦ a(r, s) and a
measurable kernel; this is what makes `join` a morphism.  The same construction over a weight object `WQ = [0,∞]`
gives the s-finite monad (`SFinite*`), which is the model of `StatisticalInterface` (`SFiniteStat`).  On top sit
products and Fubini (`Product`, `SFiniteCommute`), n-fold products (`FinProd*`), independence, iid families and
exchangeability (`Independence`, `IID`, `Exchangeable`), and the coin-coordinate results (`CoinIndep`, `CoinCoords*`)
saying that the bits of the fair coin are iid.  The `Digit*` modules (code of [0,∞] into Cantor space) belong to the
uniqueness-of-measures programme and are really measure-construction material.

The categorical vocabulary is already used where it matters: `Monad.TM : Monad (QBSCat S)`, `Strong.strongMonad :
StrongMonad V`, `Strong.commutative : Commutative braided strongMonad`, `SFiniteIncl.inclusion : Monad⇒-id TM C.TM`
(all agda-categories).  The weak points are (a) readability of the very long, fully applied, implicit-argument
statements, (b) a duplicated two-layer structure (probability monad / s-finite monad) with copy-pasted witness
machinery, (c) products and independence stated on *pre-measures* with a hand-made `prodPre`/`prodⁿ` rather than as
the monoidal structure of the Kleisli category, and (d) a handful of exact duplicates.

Top recommendations:
1. Add one headline module/section ("what is the monad") and fix the Interface.md/Guide.md gaps: the s-finite
   monad, `Product`, `Independence`, `IID`, `Exchangeable`, `CoinCoordsJoint` are barely or not at all indexed.
2. Remove exact duplicates (`mapM-id` x2, `fixH`/`fixH₂` x3, `fst-law`/`snd-law`/`fst-pair`) and move `mapM-id` to `ProdMap`.
3. Share the `JoinWit` machinery between `Monad` and `SFiniteMonad` (about 140 + 70 lines of near-parallel proof).
4. State product/independence results once, generically, as the Kleisli-monoidal double strength of the commutative
   strong monad; keep the bespoke integral-level proofs as the engine (see section 5 for why not more).
5. Rename or relocate misfiled modules (`Digit*`, `FirstBit*`, `NatCancel`, `ExtNatModel`, `FairCoin`) and merge the
   `IndepAlg`/`IndepRing` pair.

## 2. Main results

| # | Result | Where | Plain statement | Easy to find? |
|---|---|---|---|---|
| 1 | `TQ`, `TH`, `ηH`, `joinH`, `TM : Monad (QBSCat S)` | Monad.agda:~150-426 | The probability monad on QBS. | Interface.md:121 lists `Pre, mk, ∫, joinPre, ∫-join` but not `TQ`/`TM`; no statement of the equality of measures (`_≈ᵖ_`). Not crisp. |
| 2 | `∫-join`, `∫-map`, `∫ᶠ` | Monad.agda | ∫ (join p) f = ∫ p (q ↦ ∫ q f). | Listed. |
| 3 | `strength : Strength V TM`, `strongMonad` | Strong.agda:~85-115 | Left strength (x, q) ↦ δₓ ⊗ q. | Not in Interface.md at all. |
| 4 | `commutative : Commutative braided strongMonad` | Strong.agda (last), via `Probes.fubini` | Fubini: order of sampling is irrelevant. | Not indexed; the header says it, but a reader looks for "Fubini". |
| 5 | `TQ`/`TM` of s-finite measures; `∫ᴹ`, `_≈ᴹ_` | SFinite.agda:73,185; SFiniteMonad:240 | s-finite measure = weighted pre-measure; ∫ᴹ p f = ∫ w(α r) f(x(α r)) dm. | Interface.md:159 gives `∫ᴹ`, `_≈ᴹ_` only; `TQ`/`TT`/`strongMonad` of the s-finite layer missing. |
| 6 | `SFiniteCommute.commutative`, `commA` (Tonelli/Fubini for [0,∞]) | SFiniteCommute.agda:174,235 | s-finite monad is commutative. | Not indexed. |
| 7 | `inclusion : Monad⇒-id TM C.TM` | SFiniteIncl.agda:166 | Probability monad embeds as a submonad (weight 1). | Not indexed. |
| 8 | `continuousStat : StatisticalInterface …` | SFiniteStat.agda:157 | The s-finite model satisfies all statistical axioms (sums, score, normalisation, scaled laws). | Indexed (Interface.md:161, Guide.md:131).  Good. |
| 9 | `prodPre`, `∫-prod`, `∫-prod′`, `∫-rect`, `marg₁/₂`, `prod-cong` | Product.agda (header 3-9) | Product of s-finite measures; Fubini both ways; rectangles. | Header is good; not in Interface.md or Guide.md. |
| 10 | `prodⁿ`, `∫-rectⁿ`, `margⁿ`, `prodⁿ-cong`, `pairⁿ` | FinProd.agda:74-122, FinProdPair.agda:96 | n-fold product measure and its marginals. | Not indexed. |
| 11 | `Indep₂`, `Indep`, `∫-indep`, `Ex-indep`, `Var-indep` | Independence.agda | Independence = law of the tuple is the product of laws; consequences. | Not indexed; strong definition (equality of laws) explained only in the header. |
| 12 | `IID`, `IIDSeq`, `IID-law`, `IID-map`, `IID-moments` | IID.agda | iid family; functions preserve iid; moments feed `SgMoments`. | Not indexed. |
| 13 | `Exch`, `prodⁿ-exch`, `Exch-mix`, `condIID-exch` | Exchangeable.agda:60-106 | Product laws and mixtures of them are exchangeable (easy half of de Finetti). | Not indexed. |
| 14 | `fairCoin-indep` | CoinIndep.agda:119 | evens/odds interleaving of two fair coins is the fair coin. | Header only. |
| 15 | `coins-iid`, `coins-iidSeq`, `draws-iid` | CoinCoordsJoint.agda:160-175 | Coordinates of the coin are iid; samplers' draws are iid. | Header good; not indexed.  `CoinCoords` (pairwise, `E-indep`) vs `CoinCoordsJoint` (mutual) is a confusing pair of names. |
| 16 | `continuousProb`, `continuousQBSLike` | ProbInstance.agda:117,128 | The monad is a `ProbabilityInterface` / QBS-like. | Indexed (Interface.md:122). |

## 3. Documentation

1. **Interface.md gaps.**  Add one section "Continuous core" after line 123.  Proposed text:
   > `QBS.Continuous.Monad`: `TQ X` (measures on X: probe α : ℛ → X plus a probability measure on ℛ, equal when all
   > [0,1]-tests integrate equally), `TM : Monad (QBSCat S)`; `QBS.Continuous.Strong`: `strongMonad`, `commutative`
   > (Fubini).  `QBS.Continuous.SFinite*`: the same with a weight in [0,∞]: `TQ`, `∫ᴹ`, `TT`, `strongMonad`,
   > `commutative` (Tonelli), `inclusion` (Prob is a submonad), `continuousStat`.  `Product`: `prodPre`, `∫-prod`,
   > `∫-rect`.  `FinProd`: `ΠQ`, `prodⁿ`, `∫-rectⁿ`.  `Independence`: `Indep₂`, `Indep`, `∫-indep`, `Var-indep`.
   > `IID`, `Exchangeable`, `CoinCoordsJoint`: `IID`, `Exch`, `coins-iid`.
2. **Monad.agda header** (5 lines) does not say that this file is *parametrised* by the measure class `K` and is
   reused for sub-probabilities (`SubProb`).  Proposed addition: "`module Continuous A lem K` is generic in the class K
   of admissible measures (probability: `Integration.probClass`; sub-probability: all mass ≤ 1, see `SubProb`;
   the s-finite monad `SFinite` reuses `Wit`/`Pre` with weights).  Section 1 defines pre-measures, section 2 the
   witness of a random family, section 3 the monad."
3. **Module names that mislead.**  `SubModel` (a soft-uniform example, not a model) -> `SoftUniform`; `ProbInstance`
   -> `ProbInstance` is fine but `SubProb` should say "SubProbMonad"; `NatCancel` (lower-real arithmetic) belongs with
   `Analysis.ExpLower`; `ExtNatModel` (22 lines, a satisfiability check) belongs next to `QBS.Instance` or in an
   `Example` folder; `FairCoin`, `FirstBit`, `FirstBitInf`, `CoinIndep` are measure-construction modules (Cantor
   measure facts) and the `Digit*` family is Uniqueness-programme material (UniquenessLit.md): all would be better in
   `Analysis.*`/`Borel.*` or a `Continuous/Coin/` and `Continuous/Digits/` subdirectory.  Only `Monad`, `Strong`,
   `SFinite*`, `Product`, `FinProd*`, `Independence`, `IID`, `Exchangeable*`, `ProdMap`, `ProdBridge`, `ProdReweight`
   are the true "core".
4. **`CoinCoords` vs `CoinCoordsJoint`.**  Add to the first header: "pairwise independence on the nose, for J and E;
   superseded for most uses by `CoinCoordsJoint.coins-iid`, which gives mutual independence".
5. **Helpers whose header says "helper for X"** (`IndepAlg`, `IndepRing`, `FinProdPair`, `ExchangeableSwap`,
   `ProdBridge`) are listed in Modules.md as independent modules; mark them with "(helper)" in the table so readers
   skip them.
6. **Buried results.**  `Strong.agda` mixes the strength, ~60 lines of `lhsEq/rhsEq/mid/hmerge` plumbing and the
   commutativity statement; the commutativity theorem should appear first with a one-line comment ("Fubini for
   probability measures: both double-strength composites integrate g to the iterated integral") and the plumbing
   moved into a `private` block below.

## 4. Simplification

1. **Exact duplicate `mapM-id`.**  `FinProdPair.agda:40` and `CoinCoordsJoint.agda:145` are the same statement
   (`mapM (idH S) p ≈ᴹ p`); both modules import `ProdMap`.  Move to `ProdMap` next to `mapM-comp` (and `mapM-cong`,
   `mapM-ext`).  Gain: removes ~6 lines and a naming collision when both modules are opened together.  Risk: none.
2. **Three `fixH`s.**  `Strong.fixH` (Strong:47, test values `AQ`), `SFiniteStrong.fixH` (:55, values `WQ`) and
   `SFiniteCommute.fixH₂` (:79, the symmetric one) are the same "partial application of a test on a product", each
   with the same cong and `map-random` proof.  Make a single `fixL`/`fixR` generic in the value QBS `V`
   (`Hom (X ×Q Y) V → ∣X∣ → Hom Y V`) in `QBS.Limits` or `Continuous.Sample`.  The `TQ`-side proof needs only
   `const-random` and `pairQ`.  Gain: ~30 lines; Risk: the module comments mention compile-time sensitivity
   (Strong.agda:97-99 and Monad.agda "TM written out"); keep the generic version `abstract`-free and measure.
3. **`Monad.JoinWit` vs `SFiniteMonad.JoinWit`.**  Monad.agda:~330-395 (about 65 lines) and SFiniteMonad.agda:57-200
   (about 140 lines) build the witness for a random family of joins by the same re-association `a′ = a₂ ∘ reassocR`,
   `K′ k = push merge (g w₂ k)`, `g′ r = bind (g w r) …`; the s-finite version differs by tracking the weight
   component.  Factor the weight-independent part (the `K′`, `g′`, `kK′`, `gok′`, `gpr′` family, which is purely about
   `Measure`) into `Continuous.Monad` and have `SFiniteMonad` instantiate it at `a = x ∘ …`.  Gain: ~50-70 lines and,
   more importantly, one proof of the hardest lemma of the domain.  Risk: medium; the `abstract` blocks in SFiniteMonad
   (130, 137) exist for compile time, so the shared lemma must be stated at the `Measure` level, not the `Pre` level.
4. **Marginal lemmas.**  `FinProd.fst-law` (95), `snd-law` (100), `FinProdPair.fst-pair` (44), `Product.marg₁/marg₂`
   and `FinProd.margⁿ` (113) all say "pushing s ⊗ t along a projection gives the mass-scaled factor".  After
   `Product.marg₁/marg₂`, `fst-law`/`snd-law` are the special case with mass 1; check that they can be deleted in
   favour of `Product.marg₁/₂` (they appear to be restatements specialised to `∫ 1 = 1`; if they are, replace by
   one-line corollaries).  Also `tl`/`tlμ` (106-109) and `tlp` (FinProdProb:54) are three copies of the "tail of a
   family" operation on three types (QBS family, s-finite family, probability family); a single `Fin`-level `tl` on
   an arbitrary family `A : Fin (suc n) → Set` would do.
5. **`prodPⁿ`/`prodⁿ` duplication.**  `FinProdProb` re-does the recursion of `FinProd.prodⁿ` for `⊗ᵖ`
   (`Inference.ExpectationProduct._⊗ᵖ_`, line 123) and then proves `ι-prodⁿ` that the two agree.  The two products
   (`_⊗ᵖ_` = strength then join; `prodPre` = double strength) exist because the probability monad's `⊗` predates the
   s-finite one.  Since `ProdBridge.ι-⊗` shows they agree, state everything (iid, Exch, Indep) on the s-finite
   side only (as is already done), and derive the probability-side facts through `ι`; `FinProdProb.prodPⁿ` then
   becomes necessary only for the `proj-iid` corollary.  Medium gain, low risk, but it needs a caller audit in
   `Inference.GaussVector*`.
6. **`IndepAlg` + `IndepRing` (44 + 46 lines) for two ring identities.**  Both are "one solver call" modules, transported
   via `SignedVarAlg`.  Merge into one `IndepRing` (the `IRing` module is parametrised over a commutative semiring
   so the algebra half is just the transport), or inline the two identities where `Var-indep` needs them.  Gain: two
   fewer modules.  Risk: none beyond compile-time of the signed ring (they are split deliberately for that, per the
   comments, so measure).
7. **`ProdReweight.rw-alg`/`sc-alg`** (51, 55) are one-line `*`-commutative-semigroup permutations
   (`x∙yz≈y∙xz`) as used in `SFiniteCommute.agda:140`.  Import the stdlib lemma instead of restating.
8. **`SFiniteStatBridge` (279 lines, ~20 near-identical `…-G`/`…-Pre` lemma pairs).**  Names such as `bindKPt`,
   `sumKPointG`, `scoreOneG`, `kScore-int` show the pattern "pre-measure statement, then global-element statement at
   `1Q S`".  The global-element form is a one-line corollary of the pre-measure form through `1Q S ≅ ⊤`; a generic
   transport lemma `∀ x : Hom 1 X → Pre (XW X)` would remove about a third of the file.  Medium effort, unknown
   compile impact (the header says unifying against the field type ran out of memory, so keep field-shaped statements).
9. **`DigitCut` (48 lines) and `NatCancel` (35 lines)** are tiny facts about lower reals; merge into
   `Analysis.ExpLower` or a `Continuous.Cuts` module (see section 3).
10. **`SFiniteDecomp` (436 lines) and `SFiniteNorm` (497 lines)** duplicate `densityM`/`normD`/`normM` (SFiniteDecomp:103,123,134)
    versus `normMeas` (SFiniteNorm:168) and `massM` vs `massP` (SFiniteDecomp:113, SFiniteNorm:97).  Make
    `SFiniteNorm.normMeas` use `SFiniteDecomp.normM` (the header of SFiniteNorm already says it does for pieces) and
    unify `massM`/`massP`; `Jmass` shows `massM ν` is `J ν 1`.  Medium risk (long proofs depend on defeq).
11. **Unused generality.**  `Wit` is parametrised by an arbitrary equivalence `≋` (Monad:~100) and instantiated
    at exactly two relations (`≈ᵖ`, `≈ᴹ`).  It is reasonable; keep, but add a comment on why it is a parameter (it is
    in the header comment of `Wit`).  `Wit-mono` seems to be used once; check and delete if so.

## 5. Categorical language

Current state: monad, strength, commutativity, braiding, monad morphism all use agda-categories records (`TM :
Monad (QBSCat S)`, `Strength V TM`, `StrongMonad V`, `Commutative braided strongMonad`, `Monad⇒-id`).  The generic
`QBS.IntegralMonad` (`Integral`, `MonadData`, `Laws`, `IntegralStrength`, `StrongLaws`) is an excellent device: a
monad on QBS is given by its integral equations and the laws are derived once.  Keep it; it explains why
`TM` has such short law proofs.  Specific points:

1. **`TM` written out instead of `Laws.TM`** (Monad.agda:~415 comment: generic `TM` made `Strong` 17 % slower).  Fine,
   but `SFiniteMonad` apparently does not repeat that and uses `StrongLaws.strongMonad`; check consistency.  Low value.
2. **Kleisli categories are not used** (only `StatisticalLemmas` mentions them).  Statements such as `kerH`,
   `bindKI`, `bindSumKI`, `bindKPt`, `Exch-mix`, `condIID-exch` (a kernel `Θ ⇒ TQ X` bound against a prior) are
   Kleisli morphisms composed with the prior.  The categorical statement would be "`Exch` is preserved by Kleisli
   composition with an exchangeability-preserving map", and `Categories.Category.Construction.Kleisli` gives
   composition and `Kleisli` laws.  Worth doing *for statements only* (one definition of `_>=>_` as Kleisli composition
   is already `bind`); the gain is readability for outsiders, not shorter proofs.  Cost: high (the integral-level
   lemmas `∫-join`, `∫ᴹ-join` are the working form and Kleisli composition unfolds to them in two steps through
   `Categories.Monad.Relative`/`Kleisli` definitions); I would not rewrite proofs, but I would expose a
   `bind`/`_>=>_` notation in one place (it appears as `joinPre (mapPre …)`, `∫-join (mapPre (σH A B) …)` etc. with
   explicit unfoldings throughout `Strong`, `SFiniteCommute:218-231`).
3. **Products as monoidal structure.**  `prodPre` is the double strength `s ⊗ t = μ ∘ T(τ) ∘ σ`, i.e. exactly the
   `Categories.Monad.Strong.Properties` composites `Left.Shorthands.σ`/`Right.Shorthands.τ` and the "monoidal functor
   (lax)" structure that a commutative strong monad has on `C` (agda-categories: `Categories.Monad.Commutative`,
   `Categories.Functor.Monoidal`, via `Strong.Properties`: `Commutative` gives `monoidal`?).  The statement
   "`TM` is a lax symmetric monoidal functor, `prodPre` its `⊗` natural transformation, `swapM` its symmetry,
   `prodⁿ` its n-fold iterate" would replace `ProdMap.map-prod`, `ProdMap.swapM` (naturality and symmetry) and
   half of `FinProdPair` by generic monoidal-functor lemmas, and `IID`/`Indep` could be stated as
   "the law is `⊗`-power".  Obstacles: (a) the integral-level formulation is what makes every proof possible
   (the categorical equalities live in setoid `Hom` modulo `≈ᴹ`, which is the correct setoid category structure
   so fine), (b) agda-categories' commutative-monad ⇒ monoidal-functor construction may not exist for the pair
   (I could not find it in `Categories.Monad.Commutative`; `Strong.Properties` only provides `τ` and the
   `commutes` field), so one would have to build it, and (c) compile time: `Strong.agda` already needs `private`
   tricks to avoid unifier blow-up on the categorical composites (comments at 97, 160).  Recommendation: build
   `ProdMap` generically over *any* `Commutative` monad whose integral laws you have, as a "double strength is
   natural and symmetric" module, and instantiate at both `TM`s; this removes the two copies of naturality proofs
   (`Strong`/`SFiniteStrong`, `SubProb`).  Not recommended: restating every `Indep*` in monoidal terms.
4. **Reasoning combinators.**  The proofs use `Setoid.trans Aˢ (Setoid.trans Aˢ …)` chains almost everywhere
   (Monad:~400-426, Strong:150-180).  `Relation.Binary.Reasoning.Setoid Aˢ` (`begin … ≈⟨ … ⟩ … ∎`) is imported in
   Monad.agda but used rarely.  Replacing the long `trans`/`sym` chains in `Monad.TM`, `Strong.σH`, `Strong.mid`,
   `Strong.μ-η-comm` by `begin` chains would make the key laws readable (a mathematician can follow "∫-join, then
   congruence, then Fubini").  Gain: readability, no compile cost (stdlib combinators are cheap); this is the
   single most effective readability improvement for the core.
5. **`Exchangeable` and the symmetric group.**  `Exch` is "invariant under adjacent transpositions" (Exchangeable.agda:60), a
   bespoke action of `Fin n` swaps on `ΠQ`.  Categorical alternative: invariance under the action of the symmetric
   group (a `Functor` from `Sym n` to `QBSCat`); worth nothing here: adjacent transpositions with a direct
   induction is the right (and simplest) choice.
6. **Bespoke records that are right:** `Pre`/`Wit`/`Joint` are not a monad-theoretic notion (they are the
   presentation of a QBS of measures); no agda-categories vocabulary fits.  `ΠQ n Xs` could be
   `Categories.Category.Cartesian`'s n-ary product, but there is no n-ary product in agda-categories for an index
   `Fin n`, and a right-nested pair gives definitional `tupleQ`; keep it.

## 6. Open questions

1. Is the probability monad `C.TM` still needed as a first-class object, or only as the source of `inclusion` and
   `ProbabilityInterface`?  If s-finite measures are the main object, `FinProdProb`, `_⊗ᵖ_` and `prodPⁿ` look like
   legacy.
2. Do you want the `Digit*`, `FirstBit*`, `CoinIndep`, `FairCoin`, `NatCancel` modules renamed or moved (this audit
   recommends `Analysis`/`Borel` placement) given the dependency graph is large?
3. Was the choice to write `TM` out (not `Laws.TM`) in `Monad` also made in `SFiniteMonad`/`SubProb`?  A comment
   should say so in each.
4. Is compile time a constraint on introducing a generic monoidal-functor module over `Commutative`?
5. Which of `CoinCoords` (pairwise) results are still used outside the module now that `CoinCoordsJoint` gives mutual
   independence?  If none, `CoinCoords` could shrink to the lemmas `CoinCoordsJoint` needs (`J-evens`, `J-odds`).

## Implementation status (2026-11-07)

Tier A (commit 383586d):
- Interface.md section "Continuous core" and Guide.md subsection: done.
- Monad header (parametrised by K, Wit's equivalence, why TM is written out): done.  CoinCoords/CoinCoordsJoint header pointers: done.
- "plan N" references removed from the headers of CoinCoordsJoint, DigitCode, DigitStream, Exchangeable, FinProd, FinProdProb, IID, Independence,
  NatCancel, ProdBridge, ProdReweight, Product, ProdMap, IndepAlg, IndepRing, FinProdPair, ExchangeableSwap (and the Contributing.md excerpt): done.
- "(helper)" marks in Modules.md: skipped (Modules.md is generated from the first header sentence; the headers already say "helper for").

Tier B:
- Generic `fixH`: done.  `Sample.fixL`/`Sample.fixR` (any value space V); `Strong.fixH`, `SFiniteStrong.fixH`, `SFiniteCommute.fixH₂` are now one-line instances.  Strong compile time unchanged (21 s before and after, cold interface).
- `fst-law`/`snd-law`: already one-line corollaries of `Product.marg₁/marg₂` plus `∫ᴹ-scale`; nothing to delete.  Skipped.
- `rw-alg`/`sc-alg`: four-step `trans` lemmas used at two places; the stdlib route needs a CommutativeSemigroup instance from the semiring record for no real gain.  Skipped.
- `Wit-mono`: wrong finding, used in `SFiniteIncl` and `SFinite`; kept.
- `tl`/`tlμ`/`tlp` unification, `SFiniteNorm`/`SFiniteDecomp` unification, `SFiniteStatBridge` pair reduction: not attempted (medium risk, budget).
Tiers D and E (JoinWit sharing, generic double strength, begin-chains in TM/Strong, IndepAlg/IndepRing merge, relocations): not done.
