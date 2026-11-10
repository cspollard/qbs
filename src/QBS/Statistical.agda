{-# OPTIONS --safe --without-K #-}

-- Normalization, an optional extension for inference, on top of a measure monad `M` with additive kernels (`Monad.Additive`).
-- The weights are not data: they are the scalars `M ⊤ = K [ ⊤ , ⊤ ]` of the Kleisli category, a semiring (`kleisli-semiring ⊤`)
-- whose product is Kleisli composition.  Scaling a measure by a weight `w` is `m ∘ w`.
open import Level using (_⊔_)
open import Data.Product.Base using (Σ)

open import Categories.Category.Core using (Category)

module QBS.Statistical {o h e} {C : Category o h e} where

open import Categories.Category.Construction.Kleisli using (Kleisli)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.NaturalTransformation as NT
import Categories.Monad.Notation as Notation
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import Categories.Monad.Additive using (IsAdditive)
open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Probability using (ProbMonad)

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

-- Normalisation, an optional extension for inference: `normalize : M X ⇒ Prob X + 1` divides a measure by its mass.  It
-- is a left inverse of scaling a probability measure by an invertible weight (`normalize-scale`), and fails on the zero
-- measure (`normalize-zero`); the degenerate infinite-mass case is left unspecified.
record Normalization
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC}
  (AK : IsAdditive (MeasureMonad.monad MM))
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open IsAdditive AK using (𝟘)
  private
    module M = Notation (MeasureMonad.monad MM)
    module Pr = Notation (ProbMonad.monad P)
    module inc = StrongMonad⇒ inc
    K = Kleisli (MeasureMonad.monad MM)
    module K = Category K

  -- scaling a measure by a weight
  scale : (⊤ ⇒ M.₀ ⊤) → ∀ {X} → ⊤ ⇒ M.₀ X → ⊤ ⇒ M.₀ X
  scale w m = m K.∘ w

  -- the component `ι X : Prob X ⇒ M X` of the inclusion
  open NT.NaturalTransformation inc.α using () renaming (η to ι)

  -- a weight with a multiplicative inverse (the product is Kleisli composition)
  Invertible : (⊤ ⇒ M.₀ ⊤) → Set (h ⊔ e)
  Invertible w = Σ (⊤ ⇒ M.₀ ⊤) λ w⁻¹ → w K.∘ w⁻¹ K.≈ K.id

  field
    normalize : ∀ X → M.₀ X ⇒ Pr.₀ X + ⊤
    -- normalizing a probability measure scaled by an invertible weight gives it back
    normalize-scale : ∀ {X} (w : ⊤ ⇒ M.₀ ⊤) → Invertible w → (p : ⊤ ⇒ Pr.₀ X) →
      normalize X ∘ scale w (ι X ∘ p) ≈ i₁ ∘ p
    -- the zero measure cannot be normalized
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.₁ x ∘ 𝟘 ≈ i₂
