{-# OPTIONS --safe --without-K #-}

-- The measurable maps of a random source: the monoid 𝕄 ⊆ End(Rˢ) as a one-object sub-category of `Setoids`.
--   * `MeasurableMaps sc`: `sc` is an agda-categories `SubCat` of `Setoids` with one object, the setoid `Rˢ`;
--     `Meas f` says `f` is pointwise equal to a hom of `sc` (the image of the inclusion `Sub`), so `meas-resp`,
--     `meas-id` and `meas-∘` are derived; the only extra data are the constants (`Meas₀-const`, giving `meas-const`);
--   * `measSubHom`: the sub-category as a subpresheaf of the homs `Rˢ ⇒ Rˢ` (the representable `repSubHom`).
-- Route: `Meas` is membership in `measSubHom` (`Categories.Category.SubCategory.SubHom`); closure under identity and
-- composition comes from `SubCat.Rid` and `∈-pre`/`∈-resp`.
module QBS.MeasurableMaps where

open import Level using (suc)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
open import Categories.Functor.Construction.SubCategory using (Sub)
import Categories.Category.SubCategory.SubHom as SH

open import QBS.SetoidMaps using (_∘ₛ_; constₛ)

-- the monoid 𝕄 ⊆ End(Rˢ) of measurable maps: a one-object sub-category `sc` of `Setoids` (whose object is the setoid
-- `Rˢ`, whose homs `Meas` are the measurable maps, closed under identity and composition) whose maps respect `≈`
-- and which contains the constants.
record MeasurableMaps {ℓ} (sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})) : Set (suc ℓ) where
  Rˢ : Setoid ℓ ℓ
  Rˢ = SubCat.U sc tt

  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)

  open Setoid Rˢ public using () renaming (Carrier to R; _≈_ to _≈ᴿ_)

  -- the raw predicate of the sub-category
  Meas₀ : Func Rˢ Rˢ → Set ℓ
  Meas₀ = SubCat.R sc

  field
    Meas₀-const : ∀ r → Meas₀ (constₛ r)

  -- the sub-category `sc` is a subpresheaf of the homs `Rˢ ⇒ Rˢ` (the representable `repSubHom` along `Sub`)
  -- and the measurable maps are its members (`_∈ι`): maps pointwise equal to a hom of `sc`
  measSubHom : SH.SubHom (Setoids ℓ ℓ) (Sub (Setoids ℓ ℓ) sc) Rˢ
  measSubHom = SH.repSubHom (Setoids ℓ ℓ) {J = Sub (Setoids ℓ ℓ) sc} (λ e → e) tt

  Meas : Func Rˢ Rˢ → Set ℓ
  Meas f = f ∈ measSubHom

  meas₀ : ∀ {f} → Meas₀ f → Meas f
  meas₀ m = mem (_ , m) (Setoid.refl Rˢ)

  meas-id : Meas (Id.function Rˢ)
  meas-id = meas₀ (SubCat.Rid sc)

  meas-∘ : ∀ {f g} → Meas f → Meas g → Meas (f ∘ₛ g)
  meas-∘ {f} a b =
    ∈-resp (λ {r} → Func.cong f (reads b {r}))
      (∈-pre (probe b) a)

  meas-resp : ∀ {f g} → (∀ {r} → f ⟨$⟩ r ≈ᴿ g ⟨$⟩ r) → Meas f → Meas g
  meas-resp e a = ∈-resp e a

  meas-const : ∀ r → Meas (constₛ r)
  meas-const r = meas₀ (Meas₀-const r)
