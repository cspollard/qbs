{-# OPTIONS --safe --without-K #-}

-- The category of algebraic monads on a category `C` for a theory `T`: monads supporting the operations of `T`
-- (`Monad.Algebraic`) and the monad morphisms that preserve them (`Monad.Algebraic.Morphism`), up to equality of
-- components.  With `T` the theory of commutative monoids this is the category of additive monads.
--   `Forget`   the forgetful functor to `Monads C`
open import Level using (_⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Theory.Equational using (Theory)

module Categories.Category.Instance.Monads.Algebraic {o h e} (C : Category o h e) (T : Theory) where

open import Relation.Binary.Construct.On using (isEquivalence)

open import Categories.Category.Instance.Monads C using (Monads)
open import Categories.Functor using (Functor)
open import Categories.Monad.Algebraic using (Algebraic)
open import Categories.Monad.Algebraic.Morphism
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open Category C
open Algebraic⇒ using (monad⇒; α)

AlgebraicMonads : Category (o ⊔ h ⊔ e) (o ⊔ h ⊔ e) (o ⊔ e)
AlgebraicMonads = record
  { Obj       = Algebraic {C = C} T
  ; _⇒_       = Algebraic⇒ T
  ; _≈_       = λ f g → α f ≃ α g
  ; id        = Algebraic⇒-id
  ; _∘_       = λ g f → Algebraic⇒-∘ f g
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = isEquivalence α ≃-isEquivalence
  ; ∘-resp-≈  = λ g≈h f≈i → ∘-resp-≈ g≈h f≈i
  }

-- forget the operations
Forget : Functor AlgebraicMonads Monads
Forget = record
  { F₀           = Algebraic.M
  ; F₁           = monad⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → eq
  }
