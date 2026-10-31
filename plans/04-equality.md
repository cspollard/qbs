# Plan 4: equality — `rewrite`, standard setoids, `Measurability`, Cantor space

Status: audit and plan only; no code changed.  Four requests, each with a verdict.

| # | Request | Verdict |
|---|---|---|
| 1 | avoid `rewrite`; flag where required | **do it**: 26 uses, none required; all replaceable (§1) |
| 2 | ℕ and `Bool` use stdlib setoids | **partly**: a naming and reasoning change, not an equality change (§2) |
| 3 | `≡` in `Measurability` looks dangerous | **you are right**, but only for `R` itself; fix it together with 4 (§3) |
| 4 | remove `≡` from Cantor space | **do it, as a staged refactor of `Core`** (§4); it also removes `funext` |

## 1. `rewrite`

`rewrite` is sugar for `with` plus a `refl` match, so it is never *required*; what varies is how much a replacement
costs.  There are 26 uses in 12 files (a 27th grep hit, `Statistical.agda:98`, is a comment).

| group | sites | what it does | replacement |
|---|---|---|---|
| A. arithmetic on ℕ | `Continuous/Sample` 47, 51, 55, 59; `Model/Pairing` 35, 62, 63; `Analysis/ExtNat` 70, 74, 79, 307 | rewrites `+-suc`, `+-comm`, `*-zeroʳ`, `sub` inside an `≡` goal | `≡.cong` / `trans` / `begin … ∎` with `≡-Reasoning`; cheap, mechanical |
| B. `unpair (pair a b)` | `Analysis/LevelSets` 43, 46; `Analysis/Series` 430; `Model/ProbInstance` 70; `Model/Cantor` 38; `Continuous/Sample` 84, 87 (`ev-dbl`/`hf-dbl`) | contracts the pairing round trip inside a larger term | `≡.cong` / `cong₂` through the enclosing function, as `Model/Cantor.cantorIso` already does at lines 32–34; or one local lemma per use |
| C. `rewrite e`, `e : ev n ≡ b` | `Borel/Merge` 84, 87; `Analysis/Interleave` 55, 56 | `mergeC a s n` is `mergeBit (ev n) (a (hf n)) (b (hf n))`, so substituting the Bool unfolds it | `≡.cong (λ b → mergeBit b _ _) e`; `Interleave` is the same with the `if` of `hf-suc` |
| D. `rewrite p`, `p : x ≡ true` (or `d r ≡ inj₁ …`) | `Analysis/BinaryExpansion` 90; `Model/StatInstance` 347, 348; `Inference/Bayesian` 125 | unfolds a function that matched on the value | `≡.subst` with a one-line motive, or `with … in eq` (already used on the neighbouring lines, `BinaryExpansion:92`, `StatInstance:346`) |

**Required: none.**  Hardest are D (`StatInstance`: the goal sits under a `Setoid._≈_` of a sum setoid, so `subst` needs the
motive written out) and `Bayesian:125` (`rewrite hs | hf` on two hypotheses at once; replace by `cong₂`).  Neither is
blocked.  Method: one group per commit, warm `make check -j4`, and a `make longcheck` run, since `subst` motives can lengthen a
declaration.  Estimated effort: A and B an afternoon, C and D another.  Afterwards add a lint to `scripts/` that fails on the
word `rewrite` outside comments, so it stays gone.

## 2. Standard setoids for ℕ and `Bool`

The stdlib's setoid for each is `≡` in a different dress: `Data.Bool.Properties.≡-setoid = setoid Bool`
(`Relation.Binary.PropositionalEquality.setoid`), and `Data.Nat.Properties.≡-decSetoid` has `_≈_ = _≡_`.  So:

* **Worth doing**: wherever a *setoid* is wanted (the carrier of a `QBS`, `Func` between carriers, sums over ℕ-indexed
  families, `Relation.Binary.Reasoning.Setoid`), use `≡-setoid`/`≡.setoid ℕ` from the stdlib instead of local ad hoc
  records.  Today `Analysis/Series` writes `n ≡.≡ k → ⊥` and matches `yes ≡.refl` by hand; a shared import (and the stdlib
  `DecSetoid` API) would shorten it.  Stage 0 should grep for the same pattern elsewhere (`Model/Sums`, `Model/Semiring`
  are candidates; not checked).
* **Not possible, and not a loss**: removing `≡` itself from ℕ and `Bool`.  A `Setoid ℕ` whose relation is `≡` is the same
  relation; pattern matching on `refl`, `with … in eq` and `subst` need the real thing.  The setoid view helps only where
  the equality must be *swapped* (functions, quotients), and ℕ and `Bool` have no such need.
* **Rebuttal to the broader worry**: `≡` on inductive data is not the pain the setoid discipline of agda-categories avoids.
  That pain comes from `≡` on **functions and quotients** (§3, §4).

Deliverable: a small `QBS.Prelude` (or imports at use sites) exposing `ℕˢ`, `Boolˢ`, and the `Dec` bridges; migrate the
three modules above; leave the other ~70 files alone.

## 3. `≡` in `Measurability` (`Core.agda:24–33`)

`Measurability` has `R : Set ℓ` and `meas-ext : (∀ r → f r ≡ g r) → Meas f → Meas g`.  Your instinct is right: `R` is a
bare `Set`, so the library silently decides that equality of "reals" is `≡`, and it leaks in four ways:

1. `meas-ext` hypotheses are `≡` on `R` (4 uses).  For `R = Lift ℓ ℕ` this is exactly right.  For `R = Cantor`
   (`ℕ → Bool`) the proofs come from `evens-merge` and friends, which need `funext` to be stated as `≡`
   (`Continuous/Sample:130–136`).
2. `Random α` is only required to respect the equality of the *target* `X` (`random-resp`), not of `R`.  With `≡` that
   is automatic (functions respect `≡`); with any other equality on `R` it would be a gap.
3. `NatPairing.unpair-pair : unpair (pair n m) ≡ (n , m)` is `≡` on `ℕ × ℕ`: fine, inductive.
4. Every `cong` out of `R` or `R × R` is a `(≡.refl , ≡.refl)` match (`Continuous/Monad:127–151`).

So: harmless for the discrete model, and the root cause of `funext` for Cantor.  It is "dangerous" only in the sense that it
bakes in the wrong equality for the one model where `R` is a function space.  Defence of leaving it alone for the discrete
model is real (`Lift ℓ ℕ` really is a set with `≡`), which is why the fix in §4 keeps `≡` available as the default.

## 4. Removing `≡` from Cantor space

Goal: `Cantor` with pointwise equality, so `merge-evens`, `merge-odds`, `split-merge` are stated and proved with no `funext`,
and the 19 `Continuous/` modules lose their `funext` parameter (leaving `lem`).

**Stage 0 — measure first (a day).**  List every site that mentions `funext` or `≡` between Cantor values, and every
`meas-ext`/`(≡.refl , ≡.refl)` pattern on `R`.  26 modules mention `funext` (`docs/Modules.md`).  Output: a table, and a
go/no-go on the estimate below.

**Stage 1 — a setoid-valued random source (`Core`).**
```agda
record Measurability ℓ : Set (suc ℓ) where
  field
    Rˢ : Setoid ℓ ℓ
    ...
    meas-ext : ∀ {f g} → (∀ r → f ⟨$⟩ r ≈ᴿ g ⟨$⟩ r) → Meas f → Meas g
```
with `Meas : Func Rˢ Rˢ → Set ℓ` (measurable maps respect `≈ᴿ`), and probes `α : Func Rˢ ∣X∣` in `QBS.Random`
(closing the gap in point 2 above).  The stdlib's function setoid (`Function.Relation.Binary.Setoid.Equality`) and `_⇨_`
supply composition and identity (`Core` already uses `Comp.function`/`Id.function` for `Hom`).
`_≈H_` is unchanged, since `Hom` is already setoid-based.
No default: the core types and lemmas are parametric in `Rˢ` and never mention `≡` on `R`.  Only a concrete source chooses an equality: `discreteSource` supplies `≡.setoid (Lift ℓ ℕ)`, `cantorSource` supplies pointwise equality of sequences.

**Stage 2 — Cantor with pointwise equality.**  `Borel/Core` defines `Cantor = ℕ → Bool` and its measurable maps
as `Measurable f = ∀ n b → Borel (λ x → f x n ≡ b)`.  Change the carrier setoid to pointwise `≈` (Bool `≡-setoid`
pointwise, §2), keep `Borel` predicates as they are, and add the missing facts: every `Borel` set respects `≈`
(`resp` already exists in `Borel` for set-equality, the new part is respecting pointwise-equal points), and
`Measurable` respects `≈`.  `Borel/Merge`, `Lead`, `Source` then drop `≡` between sequences.

**Stage 3 — `Continuous/Sample`.**  Re-prove `split-merge`, `merge-evens`, `merge-odds` pointwise (they already are:
`merge-split`, `evens-merge`, `odds-merge` are the `funext` arguments) and delete `module Split (funext …)`.  This is the
payoff stage: `funext` leaves `Continuous/Sample`, `Monad`, `Strong`, the `SFinite*` family, `Uniform*`, `CoinCoords`, and the
`RealModel`/`ExtNatModel` instances take only `lem`.  `docs/Classical.md` §1 shrinks accordingly.

**Stage 4 — clean-up.**  The discrete model's `lift`/`lower` boilerplate (R = `Lift ℓ ℕ`) can then be reviewed (open
question: should `R` there be `ℕˢ` directly?).  Update `docs/Classical.md`, `docs/Architecture.md`, `TODO.md`.

**Risks.**
* `Core` is imported by everything, so stage 1 re-checks all 139 files; do it once, on a worktree, with the main `_build`
  copied in (warm), then sweep modules in dependency order with `make check -j4`.
* Stage 1 changes the type of `Random`, so `Exponential`, `Probes`, `Limits`, `Colimits`, `Complete` all change.  The
  discrete model's proofs will need `cong` of `lift`/`lower` through a setoid-valued `R`.  Expect this to be the bulk of the work.
* Typechecking cost: setoid `Func` application in `Random` may add elaboration time in the heavy modules
  (`Continuous/SFinite*`, `Analysis/CoinIntegral`).  Measure `Probability` and `Exponential` first as canaries.
* If stage 0 shows the discrete model dominating the cost with no benefit to it, the fallback is to make `R`'s setoid a
  *parameter with a default* (`≡.setoid`) so only Cantor pays; this keeps the discrete code untouched.

**Order of work.**  §1 (independent, low risk) and §2 first, together on one worktree; §3 and §4 as one project, stage 0 to
decide.  Each stage ends with `make check`, `make longcheck`, `make doccheck`, and the timing and memory figures for the
canary modules, as for the `Probability` recast.

## Stage 0 results (survey, no code changed)

* **The root is one line.** `ℛQ` (`Probes.agda:25`) has `Carrier = setoid R`, the propositional-equality setoid on the
  reals, and `probe`'s `cong` matches `refl`.  `meas-ext` has exactly four sites: its field (`Core:30`), `ℛQ`'s `random-resp`
  (`Probes:27`), and the two sources (`Borel/Source:62`, `Model/DiscreteSource:25`).
* **`funext` is called in exactly three places**: `split-merge`, `merge-evens`, `merge-odds` (`Continuous/Sample:132-138`).
  The other 22 modules that mention it only thread the parameter.  The consumers of those three equalities are 34 uses
  in 9 files, all in `Continuous/` (`Monad` 6, `SFiniteMonad` 6, `CoinCoords` 5, `ProbInstance` 3, `SFinite` 3, `Strong` 2, and
  one each in `SFiniteCommute`, `SFiniteIncl`, `SFiniteNorm`), each as the argument of a `cong` on `R`.  Plus about 14
  `(≡.refl , ≡.refl)` patterns on `R × R` (`Monad` 5, `Model/ProbInstance` 2, `Sample` 2, and singles in
  `OpenMeasure`, `SFiniteMonad`, `Continuous/ProbInstance`, `SFiniteSum`).
* **So stage 3 is much smaller than "19 modules" suggested**: three proofs lose `funext`, and 34 call sites change from
  `cong F (merge-evens r s)` to a pointwise-setoid `cong`.  Deleting the parameter itself is then a mechanical sweep of
  the 25 threading modules.
* **Stage 1 is the real cost.** It changes `Measurability`, `Random` and `ℛQ`, so everything re-checks, and `lift`/`lower`
  boilerplate (R = `Lift ℓ ℕ`) is spread over ~40 files (`ExtNat` 37, `Param` 33, `BoolSemiring` 26, …); most of that is
  weight arithmetic that does not touch `R`'s equality.
* **Where the core mentions `≡` on `R`** (abstract layer, grepped): `Core:30` (`meas-ext`), `Probes` (`ℛQ.Carrier = setoid R`;
  `probe`'s `cong = λ { refl → … }`) and `Exponential` (lines 44 and 58: `cong` and the `(refl , e)` match on `R × X`).  `Limits`,
  `Colimits`, `Category`, `Probability`, `Statistical*` and the `Is*QBSLike` files do not.  `Complete` uses `≡` on *index types*
  `I`, not on `R`; that is a separate question (indexed products over a bare `Set`) and is out of scope here.
* **Go/no-go: go.**  The core becomes parametric in `Rˢ`, with no default; the discrete model supplies `≡.setoid (Lift ℓ ℕ)`
  and Cantor supplies pointwise equality.  The core changes are the three files above; the instances change in their
  `RandomSource` records and in the proofs that matched on `refl` over `R`.

## Outcome (stages 1–3 done)

* `RandomSource` carries `Rˢ` with `meas-resp`, `idx-resp`, and `QBS` has `random-cong`; the core never mentions `≡` on `R`.
  `discreteSource` supplies `≡.setoid`; `cantorSource` supplies pointwise equality (`Borel/Source.R₁ˢ`, lifted to `Set₁`).
* New theorems: `Borel/Core.borel-≗` and `measurable-≗` (Borel sets and measurable maps respect pointwise equality, no
  `lem`), `Analysis/Fun.Fun-resp` and `Analysis/Meas.Meas-resp` (need `lem`), `Continuous/Monad.Wit-cong`, `SFinite.∫ᴹ-Meas`.
* `funext` is gone from all 25 modules that threaded it; `merge-evens`, `merge-odds`, `split-merge` are pointwise.
* Cost: the 17 `random-cong` proofs, and `lem` now reaches `UnitInterval` (`UnitInterval A lem`).  Timing, forced rechecks
  (new vs old): `SFiniteMonad` 4.66 s / 656 MB vs 4.83 s / 634 MB; `SFiniteNorm` 6.60 s / 882 MB vs 6.80 s / 878 MB;
  `Continuous/Monad` 3.59 s / 526 MB vs 3.48 s / 467 MB.
* Not done: §2 (standard setoids for ℕ and `Bool`).
* `Complete.agda` index-type `≡`: rebutted, not changed.  agda-categories states `IndexedProductOf`, `AllProductsOf` and
  the coproduct analogues for `I : Set`, so `Complete`/`Cocomplete` only ever see Set-indexed families.  A setoid-indexed
  `ΣQ` would need a transport `P i → P j` along `i ≈ j` with coherence, and would not be the object those interfaces ask
  for.  `≡` there is the identity type of the indexing set, which is what `Σ` equality is.

## Stage 1 as first planned: probes are setoid maps (`probes-site` branch)

Stage 1 shipped with raw functions plus `meas-resp`, `idx-resp` and `random-cong`.  The branch carries out the plan
as written above: `Meas`, `Idx` and `Random` are predicates on `Func Rˢ _`, and the three fields disappear into
`Func.cong`.  The shared shape is one record, `Probes M X` (closed under `≈`, constants, precomposition by `Meas`),
so `Core` reads as a one-object site and its concrete sheaves: `Meas` is the representable (`measProbes`), `Idx`
the probes of discrete `ℕˢ`, `idx-const`/`idx-pre`/`idx-glue` the coverage axioms, `meas-glue` subcanonicity, and
`glue-random` the sheaf condition.

* Witness records (`Continuous/Monad.Wit`, `SFinite.WitM`) stay indexed by the raw family; `TQ`'s `Random` is
  `λ β → Wit (β ⟨$⟩_)`, so no lemma signature downstream changed.
* Implicit `Func` arguments are not inferable from a `Meas`/`Idx`/`Random` proof (the predicate only sees `to`):
  pass them, or use `Probes.unprobe` instead of `map-random h meas-id`.  Glued probes whose `cong` differs from the
  expected one are re-typed with `random-cast X (λ _ → ≡.refl)`.
* Gains: `UnitInterval` no longer takes `lem`, and the Cantor source no longer needs `measurable-≗`/`borel-≗` in
  its record.  Probes built from raw functions get their `cong` once, where they are built: `Borel/Source.idxₛ`
  (Borel-ness), `Continuous/Monad.Wit-cong` (via `Fun-resp lem`, as before) for the normalisation in `SFiniteNorm`,
  and `Fun-resp` for `Uniform.expansionProbe`.

### Further simplifications noticed during the sweep (not done)

Ordered by payoff.  Each one swaps a local definition for a standard structure, or removes a repeated idiom.

1. **`QBSCat` as an agda-categories `SubCategory` of `Setoids`.**  A `Hom` is a setoid map plus a property
   (`map-random`) that is closed under `id` and `∘`.  That is exactly `Categories.Category.SubCategory.SubCat`:
   take `U = Carrier`, `R f = ∀ {α} → Random X α → Random Y (f ∘ₛ α)`, `Rid = id`, and `_∘R_` = composition.
   `Category.agda` would then get `assoc`/`identity`/`equiv`/`∘-resp-≈` for free.  It would also get the faithful
   forgetful functor to `Setoids`, which is the "concrete" in concrete sheaf.  `_≈H_` would become
   `Function.Relation.Binary.Setoid.Equality._≈_` on `map`.
2. **`Measurability` as the same construction, with one object.**  `Meas` with `meas-id`/`meas-∘` is
   `SubCat ⊤` of `Setoids` with `U _ = Rˢ`: the site's single-object category, i.e. a submonoid of
   `Function.Relation.Binary.Setoid.Equality.setoid Rˢ Rˢ`.  `meas-ext` is the statement that `R` respects that
   setoid.  `Probes M X` is then a subfunctor of `Hom(−, X)` restricted to that category: a sub-presheaf of the
   representable, as the comment in `Core` already says in words.  Doing (1) and (2) together makes `probe`/`unprobe`
   literally Yoneda in agda-categories terms.
3. **Name the composite cover.**  `glueₛ j (λ n → pairₛ n ∘ₛ i n)` is written out four times (`Core.idx-glue`,
   `Colimits` ×2, `Complete`).  A `refineₛ j i` in `Core` (the composite cover of `j` by the `i n`) would make
   `idx-glue : Idx j → (∀ n → Idx (i n)) → Idx (refineₛ j i)` read as the coverage axiom it is.
4. **Remove the `random-cast X (λ _ → refl)` casts (22 sites, 11 files).**  Every one has a `refl` proof: the two
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
5. **One raw-function-to-`Func` constructor.**  `⇑` (`Model/Monad`, for `≡`-discrete `R`), `measₛ`/`idxₛ`
   (`Borel/Source`) and `witₛ` (`Continuous/Monad`) all have the shape "`to` plus a proof that it respects `≈`".
   `⇑` is the stdlib's `→-to-⟶`, which is deprecated with no `Func` successor.  So keep `⇑`, but move it to `Core`
   next to `constₛ`.
6. **`reassoc` is defined twice** (`Continuous/Monad`, `SFiniteMonad`): `(r , s) ↦ (merge r (evens s) , odds s)`.
   Export it once from `Continuous/Sample`, next to `mergeR`/`evensR`/`oddsR`.
7. **Witness indexing.**  `Wit β` is indexed by the raw family, while `Wit-cong`/`witₛ` show that every witness
   already yields a `Func`.  Once (4) lands, try indexing `Wit`/`WitM` by `Func Rˢ (PreS X)`.  The earlier attempt
   failed only because `C.PreS` and `PreMS` put different equalities on one carrier.  Indexing by the carrier map
   `Func Rˢ (Carrier X)`, with `≈ᵖ` kept separate, may avoid that.
8. **`Idx` is the probes of a discrete QBS.**  `Partitions` is `Probes M ℕˢ` plus gluing, which is `glue-random` for
   the coproduct `∐ℕ 1`.  The circularity (a `QBS` needs `Idx`) prevents defining it as a QBS in `Core`.  But
   `Colimits` could expose `ℕQ` with `probes = partitions` and `glue-random = idx-glue`-derived, so countable
   coproducts and `idx-*` lemmas share one source.

Kept local on purpose: `constₛ` (stdlib `Function.Construct.Constant.function` requires both setoids to have the same
equality level, and `Rˢ`/carriers differ); `glueₛ` (no stdlib counterpart); setoid products are already the
stdlib's (`Data.Product.Function.NonDependent.Setoid`: `<_,_>ₛ`, `proj₁ₛ`, `swapₛ`, `_×-function_`).
