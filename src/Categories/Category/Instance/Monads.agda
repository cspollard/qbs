{-# OPTIONS --safe --without-K #-}

-- The category of monads on a category `C`, with the monad morphisms of `Monad⇒-id` (the identity functor on `C`) as
-- arrows, up to equality of components.  `Monad⇒-id M N` is a monad morphism `N ⇒ M`, so an arrow `S ⇒ T` of `Monads` is
-- a `Monad⇒-id T S`, as in `Categories.Monad.Morphism.Strong`.
-- Route: identity and composition are `Monad⇒-id-id` and `Monad⇒-id-∘` (agda-categories); the category laws hold
-- componentwise, from the laws of `C`.
open import Level using (_⊔_)

open import Categories.Category.Core using (Category)

module Categories.Category.Instance.Monads {o ℓ e} (C : Category o ℓ e) where

open import Relation.Binary.Construct.On using (isEquivalence)

open import Categories.Monad using (Monad)
open import Categories.Monad.Morphism using (Monad⇒-id; Monad⇒-id-id; Monad⇒-id-∘)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open Category C
open Monad⇒-id

Monads : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
Monads = record
  { Obj       = Monad C
  ; _⇒_       = λ S T → Monad⇒-id T S
  ; _≈_       = λ f g → α f ≃ α g
  ; id        = Monad⇒-id-id
  ; _∘_       = λ g f → Monad⇒-id-∘ f g
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = isEquivalence α ≃-isEquivalence
  ; ∘-resp-≈  = λ g≈h f≈i → ∘-resp-≈ g≈h f≈i
  }
