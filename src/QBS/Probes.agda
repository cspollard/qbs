{-# OPTIONS --safe --without-K #-}

-- Probes of a setoid X: the 𝕄-set of random elements Rˢ → X, a subpresheaf of the homs `Rˢ ⇒ X` containing the constants.
--   * `Probes M X`: a `SubHom` of `Sub sc` into X, whose image `Random` contains the constants (`const-image`); closure
--     under ≈ (`random-resp`), constants and precomposition by measurable maps (`pre-random`) is derived;
--   * `measProbes`: the measurable maps are the probes of Rˢ itself (the representable).
-- Route: `Random α` is membership `α ∈ subhom`, so `random-resp` and `pre-random` are `∈-resp` and `∈-pre`.
module QBS.Probes where

open import Level using (suc)
open import Function.Bundles using (Func)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Construction.SubCategory using (Sub)
import Categories.Category.SubCategory.SubHom as SH

open import QBS.SetoidMaps using (_∘ₛ_; constₛ; _≈ₛ_)
open import QBS.MeasurableMaps using (MeasurableMaps)

-- Probes of a setoid X: the 𝕄-set of "random elements" Rˢ → X, given as a subpresheaf of the homs `Rˢ ⇒ X` on the
-- one-object sub-category `sc` of the measurable maps (`SubHom` along the inclusion `Sub`) whose image contains the
-- constants.  The random elements are the image of `ι`; closure under ≈, constants and precomposition is derived.
module _ {ℓ} {sc} (M : MeasurableMaps {ℓ} sc) where
  open MeasurableMaps M
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)

  record Probes (X : Setoid ℓ ℓ) : Set (suc ℓ) where
    open Setoid X using (_≈_)
    field
      subhom : SH.SubHom (Setoids ℓ ℓ) (Sub (Setoids ℓ ℓ) sc) X

    -- the random elements are the members of the subpresheaf (the maps `ι a`), so they respect `≈` and
    -- precomposition by measurable maps by construction
    Random : Func Rˢ X → Set ℓ
    Random α = α ∈ subhom

    field
      const-image : ∀ x → Random (constₛ x)

    random-resp : ∀ {α β} → α ≈ₛ β → Random α → Random β
    random-resp e = ∈-resp (λ {r} → e r)

    const-random : ∀ x → Random (constₛ x)
    const-random = const-image

    pre-random : ∀ {α f} → Random α → Meas f → Random (α ∘ₛ f)
    pre-random {α} a mf =
      ∈-resp (λ {r} → Func.cong α (reads mf {r}))
        (∈-pre (probe mf) a)

  -- the measurable maps are the probes of R itself: the members of the representable `measSubHom`
  measProbes : Probes Rˢ
  measProbes = record { subhom = measSubHom ; const-image = meas-const }
