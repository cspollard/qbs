{-# OPTIONS --safe --without-K #-}

-- The parameters of the theory: a random source R (the reals) with its measurable maps and measurable partitions.
--   * `Partitions M`: the measurable countable partitions R → ℕ, the probes of discrete ℕ, along which measurable
--     maps glue (`Meas₀-glue`, giving `meas-glue`); `idx-const`, `idx-pre` are the trivial cover and pullback;
--   * `IsRandomSource sc`: measurable maps, partitions, and `common-refinement` (covers compose: a partition `k`
--     refining `j` by the `i n`, with `decode` recovering `(j r , i (j r) r)` from `k r`);
--   * `RandomSource ℓ`: a one-object sub-category `subcat` with an `IsRandomSource`; all fields are re-exported.
-- Route: the three pieces are records over `MeasurableMaps` and `Probes`; no pairing function of ℕ is fixed, each
-- source chooses `k` and `decode`.
module QBS.RandomSource where

open import Level using (Level; suc; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
import Categories.Category.SubCategory.SubHom as SH
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import QBS.SetoidMaps using (glueₛ; ℕˢ)
open import QBS.MeasurableMaps using (MeasurableMaps)
open import QBS.Probes using (Probes)

-- the measurable countable partitions R → ℕ, the probes of discrete ℕ, along which measurable maps glue
record Partitions {ℓ} {sc} (M : MeasurableMaps {ℓ} sc) : Set (suc ℓ) where
  open MeasurableMaps M
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)
  field
    partitions : Probes M (ℕˢ {ℓ})

  open Probes partitions public using () renaming
    (Random to Idx; random-resp to idx-ext; const-random to idx-const; pre-random to idx-pre)

  field
    Meas₀-glue : ∀ {j f} → Idx j → (∀ n → Meas₀ (f n)) → Meas₀ (glueₛ j f)

  meas-glue : ∀ {j f} → Idx j → (∀ n → Meas (f n)) → Meas (glueₛ j f)
  meas-glue {j} pj mf =
    mem (glueₛ j (λ n → proj₁ (probe (mf n))) , Meas₀-glue pj (λ n → proj₂ (probe (mf n))))
      (λ {r} → reads (mf (lower (j ⟨$⟩ r))) {r})

-- the laws of a random source on the one-object sub-category `sc`.  Covers compose through a common refinement:
-- refining each piece
-- of `j` by `i n` gives a partition `k` that determines the pair `(j r , i (j r) r)`, recovered by `decode`.
-- (No pairing function of ℕ is fixed: each source chooses `k` and `decode`.)
record IsRandomSource {ℓ} (sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})) : Set (suc ℓ) where
  field
    measurable : MeasurableMaps sc

  open MeasurableMaps measurable public

  field
    covering : Partitions measurable

  open Partitions covering public

  field
    common-refinement : ∀ {j} {i : ℕ → Func Rˢ ℕˢ} → Idx j → (∀ n → Idx (i n)) →
      Σ (Func Rˢ ℕˢ) λ k → Idx k × Σ (ℕ → ℕ × ℕ) λ decode →
        ∀ r → decode (lower (k ⟨$⟩ r)) ≡ (lower (j ⟨$⟩ r) , lower (i (lower (j ⟨$⟩ r)) ⟨$⟩ r))

record RandomSource (ℓ : Level) : Set (suc ℓ) where
  field
    subcat : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})
    isRandomSource : IsRandomSource subcat

  open IsRandomSource isRandomSource public
