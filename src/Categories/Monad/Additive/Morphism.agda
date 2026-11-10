{-# OPTIONS --safe --without-K #-}

-- Additive monad morphisms: a monad morphism `α : S ⇒ T` between additive monads that preserves the sum and zero
-- of kernels, `α_Y ∘ (f ⊕ g) ≈ α_Y ∘ f ⊕ α_Y ∘ g`; equivalently, the induced functor `Kℓ(S) → Kℓ(T)` is
-- additive.
--   `IsAdditive⇒ S T α`   the additivity laws, as a property of a monad morphism `α`
--   `AdditiveMonad⇒ S T`  a monad morphism together with `IsAdditive⇒`, with identity `AdditiveMonad⇒-id` and
--                         composition `AdditiveMonad⇒-∘ f g` (`f` first; from `Monad⇒-id-id`, `Monad⇒-id-∘`)
-- (as in `Morphism.Strong`, a morphism `S ⇒ T` is a `Monad⇒-id T.M S.M`.)
open import Categories.Category.Core using (Category)

module Categories.Monad.Additive.Morphism {o h e} {C : Category o h e} where

open import Level using (_⊔_)

open import Categories.Monad.Additive using (AdditiveMonad)
open import Categories.Monad.Morphism using (Monad⇒-id; Monad⇒-id-id; Monad⇒-id-∘)
import Categories.Monad.Notation as Notation

open Category C
open HomReasoning

-- a monad morphism `α : S ⇒ T` preserves the sum and zero of kernels
record IsAdditive⇒ (S T : AdditiveMonad {C = C}) (α : Monad⇒-id (AdditiveMonad.M T) (AdditiveMonad.M S))
  : Set (o ⊔ h ⊔ e) where
  private
    module S = Notation (AdditiveMonad.M S)
    module α = Monad⇒-id α
  open AdditiveMonad S using () renaming (_⊕_ to _⊕ˢ_; 𝟘 to 𝟘ˢ)
  open AdditiveMonad T using () renaming (_⊕_ to _⊕ᵗ_; 𝟘 to 𝟘ᵗ)
  field
    α-⊕ : ∀ {X Y} (f g : X ⇒ S.₀ Y) → α.α.η Y ∘ (f ⊕ˢ g) ≈ (α.α.η Y ∘ f) ⊕ᵗ (α.α.η Y ∘ g)
    α-𝟘 : ∀ {X Y} → α.α.η Y ∘ 𝟘ˢ {X} {Y} ≈ 𝟘ᵗ

-- an additive monad morphism `S ⇒ T`
record AdditiveMonad⇒ (S T : AdditiveMonad {C = C}) : Set (o ⊔ h ⊔ e) where
  field
    monad⇒ : Monad⇒-id (AdditiveMonad.M T) (AdditiveMonad.M S)
    isAdditive⇒ : IsAdditive⇒ S T monad⇒
  open Monad⇒-id monad⇒ public
  open IsAdditive⇒ isAdditive⇒ public

module _ {S : AdditiveMonad {C = C}} where
  private module S = AdditiveMonad S

  AdditiveMonad⇒-id : AdditiveMonad⇒ S S
  AdditiveMonad⇒-id = record
    { monad⇒ = Monad⇒-id-id
    ; isAdditive⇒ = record
      { α-⊕ = λ f g → identityˡ ○ S.⊕-cong (⟺ identityˡ) (⟺ identityˡ)
      ; α-𝟘 = identityˡ
      }
    }

module _ {S T R : AdditiveMonad {C = C}} (f : AdditiveMonad⇒ S T) (g : AdditiveMonad⇒ T R) where
  private
    module S = AdditiveMonad S
    module SM = Notation (AdditiveMonad.M S)
    module T = AdditiveMonad T
    module R = AdditiveMonad R
    module f = AdditiveMonad⇒ f
    module g = AdditiveMonad⇒ g

  ∘-α-⊕ : ∀ {X Y} (u v : X ⇒ SM.₀ Y) →
    (g.α.η Y ∘ f.α.η Y) ∘ (u S.⊕ v) ≈ ((g.α.η Y ∘ f.α.η Y) ∘ u) R.⊕ ((g.α.η Y ∘ f.α.η Y) ∘ v)
  ∘-α-⊕ u v = begin
    (g.α.η _ ∘ f.α.η _) ∘ (u S.⊕ v)                       ≈⟨ assoc ⟩
    g.α.η _ ∘ f.α.η _ ∘ (u S.⊕ v)                         ≈⟨ refl⟩∘⟨ f.α-⊕ u v ⟩
    g.α.η _ ∘ ((f.α.η _ ∘ u) T.⊕ (f.α.η _ ∘ v))           ≈⟨ g.α-⊕ _ _ ⟩
    (g.α.η _ ∘ f.α.η _ ∘ u) R.⊕ (g.α.η _ ∘ f.α.η _ ∘ v)   ≈⟨ R.⊕-cong sym-assoc sym-assoc ⟩
    ((g.α.η _ ∘ f.α.η _) ∘ u) R.⊕ ((g.α.η _ ∘ f.α.η _) ∘ v) ∎

  ∘-α-𝟘 : ∀ {X Y} → (g.α.η Y ∘ f.α.η Y) ∘ S.𝟘 {X} {Y} ≈ R.𝟘
  ∘-α-𝟘 = assoc ○ (refl⟩∘⟨ f.α-𝟘) ○ g.α-𝟘

  -- composition: `f` first, then `g`
  AdditiveMonad⇒-∘ : AdditiveMonad⇒ S R
  AdditiveMonad⇒-∘ = record
    { monad⇒ = Monad⇒-id-∘ f.monad⇒ g.monad⇒
    ; isAdditive⇒ = record { α-⊕ = ∘-α-⊕ ; α-𝟘 = ∘-α-𝟘 }
    }
