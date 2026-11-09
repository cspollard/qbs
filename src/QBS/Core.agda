{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces over an abstract random source.  Elementarily: a QBS is a setoid X together with a set of
-- "random elements" ℛ → X, closed under precomposition with measurable maps, constants, and countable measurable
-- case splits.  Equivalently (the rest of this header): concrete sheaves on a one-object site.  The site lives in
-- its own modules, all re-exported here:
--   SetoidMaps     : setoid-map helpers (`_∘ₛ_`, `constₛ`, `ℕˢ`, `glueₛ`).
--   MeasurableMaps sc : the monoid 𝕄 of measurable maps Rˢ → Rˢ is a one-object sub-category `sc` of `Setoids`
--                    (agda-categories `SubCat`).  `Meas f` says f is pointwise equal to a hom of `sc` (the image of
--                    the inclusion `Sub`), so it respects ≈ by construction; only the constants are extra data.
--   Probes M X     : a sub-𝕄-set of the setoid maps Rˢ → X, closed under ≈ and containing the constants;
--                    i.e. a subpresheaf of Setoid(Rˢ, X) on 𝕄.
--   RandomSource   : `Partitions` (the measurable countable partitions R → ℕ, the probes of discrete ℕ) with
--                    `common-refinement` form a coverage J on 𝕄 (`idx-const` the trivial cover, `idx-pre` pullback,
--                    `common-refinement` composition of covers), and `meas-glue` says J is subcanonical.
-- Here: `QBS S`, a setoid with probes that glue along J (the sheaf condition); `Hom X Y`, setoid maps preserving
-- probes (natural transformations); identity and composition.
module QBS.Core where

open import Level using (Level; suc)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.SetoidMaps public
open import QBS.MeasurableMaps public
open import QBS.Probes public
open import QBS.RandomSource public

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S

  -- A quasi-Borel space: a setoid with probes that glue along measurable partitions.
  record QBS : Set (suc ℓ) where
    no-eta-equality
    field
      Carrier : Setoid ℓ ℓ
      probes : Probes measurable Carrier

    open Setoid Carrier public using () renaming (Carrier to ∣_∣; _≈_ to _≈ˣ_)
    open Probes probes public

    field
      glue-random : ∀ {i} → Idx i → (α : ℕ → Func Rˢ Carrier) → (∀ n → Random (α n)) → Random (glueₛ i α)

  open QBS

  -- Morphisms: setoid maps preserving probes.
  record Hom (X Y : QBS) : Set ℓ where
    field
      map : Func (Carrier X) (Carrier Y)
      map-random : ∀ {α} → Random X α → Random Y (map ∘ₛ α)

  open Hom

  idH : ∀ {X} → Hom X X
  idH {X} = record { map = Id.function (Carrier X) ; map-random = λ p → p }

  _∘H_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
  g ∘H f = record
    { map = map g ∘ₛ map f
    ; map-random = λ p → map-random g (map-random f p)
    }

  -- Morphisms are equal when they agree pointwise.
  _≈H_ : ∀ {X Y} → Hom X Y → Hom X Y → Set ℓ
  _≈H_ {X} {Y} f g = ∀ {x} → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)
