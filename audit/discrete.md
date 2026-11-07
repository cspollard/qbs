# Audit: `discrete` (discrete model and examples)

Reading audit only; nothing was compiled.  Line numbers refer to the tree at the time of reading.

## 1. Summary

The discrete model takes the random source `R = ℕ` (every function measurable) and a *complete commutative semiring* `A` of
weights.  A measure on a QBS `X` is a probe `α : R → X` with weights `μ : R → A`; two are equal when they integrate every test
function `X → A` identically.  This gives a commutative strong monad `TQ` on `QBS S` for each *weight class* `K` (all measures,
probability, sub-probability).  It carries the full `StatisticalInterface` (score, countable sums, `normalize`), and is
instantiated at Boolean (possibilistic), Viterbi (max, ×) and additive `[0,∞]` weights, so the abstract interfaces are not
vacuous.  `Example/` shows `do`-notation programs, Bayes' rule and conditioning.

The mathematical architecture is good: generic in `(A, K)`, instances are thin.  The main weaknesses are presentational and
about duplication, not about unsound modelling.

Top recommendations:
1. **Share the classical-decision toolkit** (`dec`, `dec-true`, `dec-false`, `from-true`, `dec-iff`) that is copied in
   `BoolSemiring.agda:63-97`, `ViterbiSemiring.agda:94-115`, `Analysis/CutSum.agda:165`, `Analysis/CoinIntegral.agda:73`.
   One `QBS.Classical.Decide` module (4 copies, about 40 lines saved, and a better reading experience).
2. **Prove Bool/Viterbi/additive from one pattern**: both lower-cut instances need `∑-Σ`, `∑-reindex`, `∑-distribˡ` by union
   arguments; and `boolComplete` is `Lift ℓ Bool` re-proved by hand (`BoolSemiring.agda:31-49` re-derives with `lc` what stdlib
   gives for `Bool`; use `Algebra.Construction.LiftedChoice`-style lifting or `Algebra.Bundles.Raw` lifting, or drop the `Lift`).
3. **Split `StatInstance.agda` (565 lines)** into `Model.Weights`, `Model.Score`, `Model.Sums`-instance, `Model.Normalize`; it
   is the only large module in the domain and hides its main result in the last 20 lines.
4. **Make the entry point `Model.Discrete` plus an `Example.Overview`**; the three `*Model` files are three-line wrappers and
   could be one `Model.Instances` module.  Move the Example modules to a README-style reading order.
5. **State `WeightClass` as a sub-monad structure** (closure under `η`, `map`, `bind`) in agda-categories terms, or at least
   document it as such; `Measures`' `integral`/`monadData` route to `TM` via `QBS.IntegralMonad` is good and should be
   advertised in `Interface.md`.

## 2. Main results

| # | Name | Where | Plain statement | Easy to find? |
|---|------|-------|-----------------|---------------|
| 1 | `CompleteSemiring`, `NormalizableSemiring` | `Model/Semiring.agda:19`, `:41` | commutative semiring with `Set ℓ`-indexed sums, partition-associative and distributive | Interface.md yes, but the stated field list is wrong (lists `_+_ _*_ 0# 1# ∑`, omits the six sum axioms) |
| 2 | `WeightClass` | `Model/Monad.agda:30` | predicate on weights closed under `dirac`, push-forward, bind | Not in Interface.md; undocumented in prose |
| 3 | `Measures.Pre`, `∫`, `_≈ᵖ_`, `PreS`, `TQ` | `Monad.agda:47-122` | measures as probe+weight, equal iff same integrals; QBS of measures | Interface.md has `Pre`/`∫`; `TQ`/`PreS` missing |
| 4 | `TH`, `ηH`, `joinH`, `∫-η`, `∫-join` (Tonelli) | `Monad.agda:134-244` | functor action, unit, join and their integral laws | In Interface.md |
| 5 | `Measures.TM` (via `Laws integral monadData`) | `Monad.agda:279` | the agda-categories `Monad` on `QBSCat S` | **Not mentioned**; arguably the headline of the module |
| 6 | `Strength.strongMonad`, `strength`, `fubini`, `commutative`, `commutativeMonad` | `Strong.agda:84-138` | `T` is a commutative strong monad (Fubini for countable sums) | Not in Interface.md |
| 7 | `allClass`, `probClass`, `subClass` | `WeightClasses.agda:19,28`; `SubProb.agda:63` | the three weight classes | Interface.md yes |
| 8 | `discreteProb` | `ProbInstance.agda:117` | model of `ProbabilityInterface` | Mentioned only implicitly |
| 9 | `inclusion` (`Monad⇒-id`), `normH`, `discreteStat` | `StatInstance.agda:101,399,551` | sub-monad inclusion prob ⊂ all; normalisation; the `StatisticalInterface` | `discreteStat` in Interface.md; `normH` buried at line 399 |
| 10 | `discreteStatisticalQBSLike` | `Discrete.agda:17` | one-line packaging, no remaining hypotheses | Yes, Guide.md:139 |
| 11 | `boolStatisticalQBSLike`, `viterbiStatisticalQBSLike`, `additiveStatisticalQBSLike` | `BoolModel/ViterbiModel/AdditiveModel` | non-vacuity witnesses (need `LEM`) | Interface.md omits `viterbi...` |
| 12 | `Programs`: `Prog`, `pure`, `_>>=_`, `kernel`, `∫-bind`, `Flip`, `BoolDemo` | `Example/Program.agda:37-187` | `do`-notation programs with expectation rules | Guide.md section 1, good |
| 13 | `bayes` | `Example/Bayes.agda:51` | posterior = normalised reweighting; Bayes' rule | Guide.md |

## 3. Documentation

- **Interface.md:63** says `CompleteSemiring` has "fields `_+_`, `_*_`, `0#`, `1#`, `∑`".  Replace with: "`CompleteSemiring ℓ` —
  a stdlib `CommutativeSemiring ℓ ℓ` (`commutativeSemiring`, opened publicly) with an `∑` over `Set ℓ`-indexed families that
  respects `≈`, vanishes on `⊥`, is the identity on `⊤`, splits over `⊎`, is associative over `Σ` (partitions), invariant under
  bijection, and distributes over `*`.  The model examples are `[0,∞]`, Viterbi and Boolean."
- Add to Interface.md "Discrete model": `WeightClass` ("a predicate `Ok` on weight functions closed under `dirac`,
  push-forward and bind; `allClass`, `probClass`, `subClass`"), `Measures.TQ` / `TM` ("the commutative strong monad of
  measures: `Measures.TM : Monad (QBSCat S)`, `Strength.commutativeMonad`"), `Strength` and `fubini`.
- **`Model/Monad.agda` header**: add the line "`Measures.TM` packages `TQ, TH, ηH, joinH` as an agda-categories `Monad`;
  strength and commutativity are in `Model/Strong.agda`; instances in `ProbInstance`/`StatInstance`."
- **`Model/Semiring.agda`**: header says "complete commutative semirings (Golan)"; add that `[0,∞]` is *not* instantiated here and that
  the Boolean, Viterbi and additive instances are `BoolSemiring`, `ViterbiSemiring`, `AdditiveSemiring`.
- **`StatInstance.agda` header** is a single line.  Replace with: "Assembles `StatisticalInterface` for the discrete model:
  weights object `WQ` (L61), inclusion of probability measures into all measures (L101), `score` (L147), countable sums (L195),
  normalisation `normH` (L399); packaged at `discreteStat` (L551)."
- Module names: `Model.Pairing` and `Model.Cantor` are really one concern (`ℕ × ℕ ≅ ℕ` and its effect on sums); `Model.Sums`
  holds derived lemmas, not "sums" as such: consider `Model.SumLemmas`.  `Model.Discrete` is a good name for the entry point,
  but the three `*Model` files give no hint of their purpose; document them as "non-vacuity witnesses".
- **Example reading order** (put at the top of `Example/Recipes.agda` or in Guide.md): `Recipes` (set-up) -> `Program`
  (programs, `∫-bind`) -> `Probability` (two coins) -> `Bayes` -> `Conditioning` -> `HardConditioning`.  `Program.agda` is the
  best entry point but its header is a 12-line paragraph; open with a 5-line `do` snippet showing a program and its theorem
  (`∫ both (isTrue) ≈ half * half`).  `Recipes` is named as a "copy and paste" file but contains a *continuous* recipe
  as well; say so in the header.
- Examples declare `module Conditioning (A : CompleteSemiring L.zero)` while `Bayes` uses a `NormalizableSemiring ℓ`: state in
  each header which universe level and which hypotheses it needs.

## 4. Simplification

1. **Classical-decision helpers copied 4 times.** `BoolSemiring.agda:63-97`, `ViterbiSemiring.agda:94-115`,
   `Analysis/CutSum.agda:165-185`, `Analysis/CoinIntegral.agda:73-106`.  All define `dec P = lem P ↦ true/false`, `dec-true`,
   `from-true`, `exfalso`.  Proposed: `QBS.Classical.Decide (lem : LEM ℓ)` exporting `dec`, `dec-true`, `dec-false`,
   `from-true`, `dec-iff`.  Gain: about 40 lines, one place for the classical axiom to be audited.  Cost: trivial; `Classical.agda` is imported
   already.  Alternative: stdlib `Relation.Nullary.Decidable` with `Dec P` from `lem` and `⌊_⌋`; `Relation.Nullary.Decidable.Core.⌊_⌋` and
   `Dec` combinators (`_⊎-dec_`, `_×-dec_`, `map′`) replace `dec-or`, `dec-iff` outright (`map′` for `dec-iff`).
2. **`boolCommSemiring` re-proves the stdlib** (`BoolSemiring.agda:30-50`): twenty lines whose only content is "lift `∨-∧`
   through `Lift`".  Use `Algebra.Construction.Lift`?  (if absent from this stdlib version, define a generic
   `liftCommSemiring` once; it will also serve any future `ℕ∞`, `Fin`-valued instance).  Alternatively make the Boolean
   semiring use `Lift`-free carrier by choosing the Boolean model at the `Set₀` level and lifting the whole `CompleteSemiring`
   (`liftComplete : CompleteSemiring ℓ → CompleteSemiring (ℓ ⊔ ℓ′)`); this is nontrivial because `∑` ranges over `Set ℓ`
   (need `Set ℓ`-indexed sums), so the first option is realistic.
3. **Viterbi and additive share the same shape.** `ViterbiSemiring.sumC` (about `:120-187`) and `CutSum.sumC` differ only in how the
   `mem` at a rational is computed ("exists i" vs "some finite sub-sum").  `∑-cong`, `∑-empty`, `∑-unit` proofs are structurally
   identical to `AdditiveSemiring.agda:44-50`.  A generic lemma "sup-like families of cuts: `Mem-mono`, `Mem-empty`, `Mem-unit`"
   would remove those pieces.  Risk: the two have different universe handling; only attempt after item 1.
4. **Three `*Model` files**: `BoolModel`, `ViterbiModel`, `AdditiveModel` are 18 lines each and nearly identical.  Merge into
   `Model/Instances.agda` (or put each next to its semiring).  Gain: 3 fewer modules, one place listing the instances.  Cost: 3
   import updates in docs.
5. **`Strength` and `Measures` are opened with the same 10-line preamble** (`Monad.agda:41-50`, `Strong.agda:29-43`, `SubProb.agda:18-24`,
   `Example/*`, `StatInstance.agda:42-54`).  Introduce a `module Setup A K` that `open`s and `private`-defines `R`, `S`, `∣A∣`,
   `Aˢ` so a file starts with one `open Setup A K`.  Gain: readability for outsiders.  Cost: none beyond a re-export.
6. **`probClass`/`subClass` proofs repeat `diracMass`, `pushMass`** (`WeightClasses.agda:26-33` vs `SubProb.agda:26-34`): factor
   `∑ (dirac j) ≈ 1#`, `∑ (push f μ) ≈ ∑ μ` into `Sums.agda` (they are `dirac-∑`/`push-∑` with `g = 1`).  Gain: about 10 lines.
7. **`StatInstance` ad-hoc inverse algebra** (`inv-unique`, `inv-of-scaled`, `inv-scaled`, lines 235-380): this is the unit
   group of a commutative monoid.  Use `Algebra.Properties.CommutativeMonoid`/`Algebra.Properties.Monoid.Divisibility`
   (`_∣_`, `∣-trans`) or define `Invertible m n = m * n ≈ 1#` and cite stdlib `Algebra.Definitions.RightInvertible`
   (already used in `InvDec`).  `inv-unique` is `Algebra.Properties.Monoid.Invertible` style (check which lemma exists; not
   verified).  Gain: modest (30 lines), mostly reuse.
8. **`fubini` has a local `mid`** (`Strong.agda:127`) imported from `CommutativeSemigroup`: fine.  But the proof chain of
   `fubini` and `∫-join` (`Monad.agda:218-232`) share the pattern "distribute, swap, reassociate, scale"; extract `∑-bilinear`
   to `Sums` (with `∑-swap` and `∑-scale`) and both become 2-liners.  Cost: re-compiles dependents of `Sums`.
9. **`CompleteSemiring` could be built from a stdlib-style `Algebra.Module`-like structure**: `∑` is a Set-indexed
   additive operation.  No stdlib structure covers this ("complete semiring", "infinitary commutative monoid" are not in
   stdlib), so the bespoke record is the right choice.  Do not change.
10. **`∑-reindex`/`∑-⊎`/`∑-empty`/`∑-unit` are derivable from fewer axioms.**  `∑-empty` and `∑-unit` are special cases of
    `∑-Σ` and reindexing only when 0 and 1 are involved; `∑-⊎` follows from `∑-Σ` plus `∑-reindex` with `Σ Bool ... ↔ I ⊎ J`.
    Minimising the axioms makes each new instance cheaper (the additive instance spends the most proof effort on them).  Medium
    gain, low risk because derived lemmas can sit in `Sums.agda` while the record retains convenient fields: prove the
    minimal set `∑-cong, ∑-Σ, ∑-reindex, ∑-unit, ∑-empty, ∑-distribˡ` (so `∑-⊎` derived) and keep `∑-⊎` as a derived lemma.
11. **`Model.StatInstance.normC′/normC` use `InvDec` through `Σ`-free `⊎`**; fine, no change.

## 5. Categorical language

- **Monad.**  Already stated as an agda-categories `Monad` (`Measures.TM`), built through `QBS.IntegralMonad.Laws`, which
  reduces monad laws to integral equations.  This is the right choice; it removes the three monad-law proofs.  Document it.
- **Strength and commutativity.**  `Strong.agda:84-138` uses `Categories.Monad.Strong.Strength`, `StrongMonad`,
  `Commutative` and `CommutativeMonad` directly: good.  The `Right.Shorthands` detour for `commutes` is unavoidable in
  agda-categories.  Note the comment at L134: building `commutativeMonad` took 30 s elsewhere; leave it.
- **`WeightClass` as a submonad.**  `Ok` with `ok-dirac`, `ok-push`, `ok-bind` is exactly "a submonad of `T_all` on the sets of
  weights".  Category-theoretically, `inclusion : Monad⇒-id MA.TM MP.TM` (StatInstance:101) is the morphism.  Stating the
  class as a record in agda-categories terms (`Categories.Monad.Morphism`) would require a generic submonad construction;
  not worth it, but say so in the header of `WeightClasses.agda` ("an instance of the general submonad construction").
- **`Sums` over `Set ℓ` families as a monoidal structure.**  Weights are `CommutativeMonoidWithZero` in `QBSCat` (see
  `discreteWeights`, `StatInstance:466`): good, uses the abstract interface.
- **Kleisli.**  `Example/Program.agda` builds `kernel : (T → Prog U) → Hom (Disc T) (TQ (Disc U))`, which is the Kleisli
  functor from `Set` into `Kleisli TM`.  Explicitly exposing `Disc : Set ℓ → QBS S` as a functor `Setoids ⇒ QBSCat S` and
  `Prog = TQ ∘ Disc` would explain `_>>=_` as Kleisli composition.  Worth doing only as prose; a functor record costs a
  lot of setoid plumbing (`Func` on every `T`).
- **Normalisation.**  `normH : MA.TQ X ⇒ MP.TQ X + 1` is a natural transformation in the Kleisli sense (`normalize-scale` etc. are the
  laws); the `StatisticalInterface` already records these as laws, so it is already categorical.
- **Bespoke is better** for `Pre`/`PreS` (the setoid of pre-measures): it avoids quotients.  Agree with the header.
- **`Cantor`/`Pairing`**: pure combinatorics; better to use stdlib `Data.Nat.Bijection` (`ℕ × ℕ ↔ ℕ`?) if present.  The stdlib
  has `Data.Nat.Bijection` (for `ℕ ⊎ ℕ`) and `Data.Nat.Pairing`?  Not verified; grep `Cantor`/`pair` in
  `/Users/cspollard/Programming/agda-stdlib/src/Data/Nat` before deciding.  Likely gain: all of `Pairing.agda` (69 lines).

## 6. Open questions

1. Is the `Lift ℓ Bool` instance used at any level except `ℓ = 1` (the only one that `Example.Program.BoolDemo` uses is 0)?
   If never, can `boolStatisticalQBSLike` fix the level and drop the `Lift`?
2. `Example.Conditioning` is stated at `CompleteSemiring L.zero`, whereas the additive semiring lives at `Set₁`; so can the
   conditioning examples actually be run on real weights?  If not, state it as a limitation.
3. Does anything depend on `Model.Pairing` being separate from `Model.Cantor`?  (merge candidate.)
4. Is `ViterbiModel` exercised anywhere beyond its own check?  It has no example; add a short best-path example or
   remove it from the Guide's list of semirings.
5. Are `∑-reindex` and `∑-empty` genuinely independent axioms for the intended models (Section 4, item 10)?
6. Should `WeightClass` also require `ok-resp`-free (strictly, setoid-respecting) classes to be proof-irrelevant?  `Ok` is
   `Set ℓ`-valued; for `probClass`, `Ok μ = ∑ μ ≈ 1#` is not a proposition in general, which matters when comparing `Pre`
   equality (it is avoided by `_≈ᵖ_` ignoring `μ-ok`; confirm this is deliberate).

## Implementation status (2026-11-07)

- A (docs): done.  `Interface.md` `CompleteSemiring` entry replaced; `WeightClass`, `TQ`/`TM`, `commutativeMonad`/`fubini`,
  `viterbiStatisticalQBSLike` added; headers of `Model/Monad`, `Model/Semiring`, `StatInstance`, `Example/Program` (5-line `do`
  snippet) and `Example/Recipes` (reading order, levels and hypotheses per example, continuous recipe noted) updated.
  Entry point is `Model.Discrete` (+ `Example/Program` as overview); no separate `Example.Overview` module was added.
- B: `boolCommSemiring` as stdlib `Lift`: skipped, this stdlib has no lifting of semirings (only `LiftedChoice`); the
  existing proof already reuses `Bool`'s `∨-∧-commutativeSemiring` through `lc`.  Classical toolkit sharing was done by agent 0.
- E: `StatInstance` (565 lines) split into `StatWeights` (inclusion, score, sums), `StatNormalize` (`normH`) and
  `StatInstance` (laws and `discreteStat`): 27.4 s -> 3.7 + 4.1 + 6.5 s.  `BoolModel`/`ViterbiModel`/`AdditiveModel` folded
  into `Model/Instances` (old modules deleted).  `WeightClass` documented as a sub-monad in the `WeightClasses` header.
- Not attempted (C/D and report items 4.3, 4.5-4.8, 4.10, Pairing/Cantor merge): out of the requested tiers.
