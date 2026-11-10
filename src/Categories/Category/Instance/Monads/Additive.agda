{-# OPTIONS --safe --without-K #-}

-- The category of additive monads on a category `C` (`AMnd(C)` of Coumans–Jacobs, Scalars, Monads, and Categories):
-- monads with additive kernels (`Monad.Additive`) and the monad morphisms that preserve `⊕` and `𝟘`
-- (`Monad.Additive.Morphism`), up to equality of components.  As in `Instance.Monads`, an arrow `S ⇒ T` has a monad
-- morphism `α : S.F ⇒ T.F` underneath.
--   `Forget`   the forgetful functor to `Monads C`
-- Route: the laws are those of `Instance.Monads`, componentwise; identity and composition are `AdditiveMonad⇒-id` and
-- `AdditiveMonad⇒-∘`.
open import Level using (_⊔_)

open import Categories.Category.Core using (Category)

module Categories.Category.Instance.Monads.Additive {o h e} (C : Category o h e) where

open import Relation.Binary.Construct.On using (isEquivalence)

open import Categories.Category.Instance.Monads C using (Monads)
open import Categories.Functor using (Functor)
open import Categories.Monad.Additive using (AdditiveMonad)
open import Categories.Monad.Additive.Morphism
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open Category C
open AdditiveMonad⇒ using (monad⇒; α)

AdditiveMonads : Category (o ⊔ h ⊔ e) (o ⊔ h ⊔ e) (o ⊔ e)
AdditiveMonads = record
  { Obj       = AdditiveMonad {C = C}
  ; _⇒_       = AdditiveMonad⇒
  ; _≈_       = λ f g → α f ≃ α g
  ; id        = AdditiveMonad⇒-id
  ; _∘_       = λ g f → AdditiveMonad⇒-∘ f g
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = isEquivalence α ≃-isEquivalence
  ; ∘-resp-≈  = λ g≈h f≈i → ∘-resp-≈ g≈h f≈i
  }

-- forget the additive structure
Forget : Functor AdditiveMonads Monads
Forget = record
  { F₀           = AdditiveMonad.M
  ; F₁           = monad⇒
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → eq
  }
