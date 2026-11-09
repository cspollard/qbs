{-# OPTIONS --safe --without-K #-}

-- Strong monad morphisms: a monad morphism `α : S ⇒ T` between strong monads on a monoidal category that also
-- respects the strengths,  α_{A⊗B} ∘ τS_{A,B} ≈ τT_{A,B} ∘ (id ⊗ α_B).
--   `IsStrong S T α`   the strength law, as a property of a monad morphism `α`
--   `StrongMonad⇒ S T` a monad morphism together with `IsStrong`
-- (`Monad⇒-id` names its target first, so a morphism `S ⇒ T` is a `Monad⇒-id T.M S.M`.)
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Monad.Morphism.Strong {o ℓ e} {C : Category o ℓ e} {V : Monoidal C} where

open import Level using (_⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad.Strong using (StrongMonad; Strength)
import Categories.NaturalTransformation as NT

-- a monad morphism `α : S ⇒ T` respects the strengths
record IsStrong (S T : StrongMonad V) (α : Monad⇒-id (StrongMonad.M T) (StrongMonad.M S)) : Set (o ⊔ ℓ ⊔ e) where
  open Category C
  open Monoidal V using (_⊗₀_; _⊗₁_)
  private
    module τS = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength S))
    module τT = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength T))
    module α = Monad⇒-id α
  field
    -- `α` commutes with the strengths: strengthening, then `α`, is `α` then strengthening
    strong : ∀ A B → α.α.η (A ⊗₀ B) ∘ τS.η (A , B) ≈ τT.η (A , B) ∘ (id ⊗₁ α.α.η B)

-- a strong monad morphism `S ⇒ T`
record StrongMonad⇒ (S T : StrongMonad V) : Set (o ⊔ ℓ ⊔ e) where
  field
    monad⇒ : Monad⇒-id (StrongMonad.M T) (StrongMonad.M S)
    isStrong : IsStrong S T monad⇒
  open Monad⇒-id monad⇒ public
  open IsStrong isStrong public
