{-# OPTIONS --safe --without-K #-}

-- The scalars functor `Scalars X : AdditiveMonads C → Semirings`: an additive monad `M` goes to the semiring
-- `kleisli-semiring X` of endomorphisms of `X` in its Kleisli category (sum `⊕`, product Kleisli composition), and an additive
-- monad morphism `α` to `f ↦ α_X ∘ f`.  For `X = ⊤` these are the scalars `M(1)` of Coumans–Jacobs (`E` in
-- `Scalars, Monads, and Categories`).
-- Route: `α_X ∘ -` preserves `⊕` and `𝟘` by `IsAdditive⇒`, the unit by `unit-comp`, and Kleisli composition by
-- `mult-comp` and naturality of `α`.
open import Categories.Category.Core using (Category)

module Categories.Functor.Instance.Scalars {o h e} (C : Category o h e) (X : Category.Obj C) where

open import Algebra.Bundles using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)

open import Categories.Category.Instance.Monads.Additive C using (AdditiveMonads)
open import Categories.Category.Instance.Semirings h e using (Semirings)
open import Categories.Functor using (Functor)
open import Categories.Monad.Additive using (AdditiveMonad)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad.Additive.Morphism using (AdditiveMonad⇒)
import Categories.Monad.Notation as Notation
import Categories.Morphism.Reasoning C as MR

open Category C
open HomReasoning
open MR

-- the endomorphism semiring is functorial: `α_X ∘ -` preserves the product (Kleisli composition)
module _ {S T : AdditiveMonad {C = C}} (σ : AdditiveMonad⇒ S T) where
  private
    module S = Notation (AdditiveMonad.M S)
    module T = Notation (AdditiveMonad.M T)
    module σ = AdditiveMonad⇒ σ
    α = σ.α.η X
    αT = σ.α.η (T.₀ X)

  ∘-hom : ∀ (f g : X ⇒ S.₀ X) → α ∘ (S.μ X ∘ S.₁ f) ∘ g ≈ (T.μ X ∘ T.₁ (α ∘ f)) ∘ (α ∘ g)
  ∘-hom f g = begin
    α ∘ (S.μ X ∘ S.₁ f) ∘ g                                ≈⟨ sym-assoc ○ (sym-assoc ⟩∘⟨refl) ⟩
    ((α ∘ S.μ X) ∘ S.₁ f) ∘ g                              ≈⟨ (σ.mult-comp ⟩∘⟨refl) ⟩∘⟨refl ⟩
    ((T.μ X ∘ αT ∘ S.₁ α) ∘ S.₁ f) ∘ g          ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
    T.μ X ∘ (((αT ∘ S.₁ α) ∘ S.₁ f) ∘ g)
      ≈⟨ refl⟩∘⟨ ((assoc ○ (refl⟩∘⟨ ⟺ S.homomorphism)) ⟩∘⟨refl) ⟩
    T.μ X ∘ ((αT ∘ S.₁ (α ∘ f)) ∘ g)            ≈⟨ refl⟩∘⟨ (σ.α.commute (α ∘ f) ⟩∘⟨refl) ⟩
    T.μ X ∘ ((T.₁ (α ∘ f) ∘ α) ∘ g)                        ≈⟨ refl⟩∘⟨ assoc ⟩
    T.μ X ∘ (T.₁ (α ∘ f) ∘ (α ∘ g))                        ≈⟨ sym-assoc ⟩
    (T.μ X ∘ T.₁ (α ∘ f)) ∘ (α ∘ g)                        ∎

  -- `α_X ∘ -` is a semiring homomorphism `kleisli-semiring S X ⇒ kleisli-semiring T X`
  Scalars-hom : SemiringHomomorphism
    (Semiring.rawSemiring (AdditiveMonad.kleisli-semiring S X)) (Semiring.rawSemiring (AdditiveMonad.kleisli-semiring T X))
  Scalars-hom = record
    { ⟦_⟧ = α ∘_
    ; isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = ∘-resp-≈ʳ }
            ; homo = σ.α-⊕
            }
          ; ε-homo = σ.α-𝟘
          }
        ; *-homo = ∘-hom
        }
      ; 1#-homo = σ.unit-comp
      }
    }

Scalars : Functor AdditiveMonads Semirings
Scalars = record
  { F₀           = λ S → AdditiveMonad.kleisli-semiring S X
  ; F₁           = Scalars-hom
  ; identity     = λ _ → identityˡ
  ; homomorphism = λ _ → assoc
  ; F-resp-≈     = λ eq _ → ∘-resp-≈ˡ eq
  }
