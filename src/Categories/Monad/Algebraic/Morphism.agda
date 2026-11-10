{-# OPTIONS --safe --without-K #-}

-- Algebraic monad morphisms: a monad morphism `α : S ⇒ T` between algebraic monads (for a theory `Th`) that preserves
-- every operation of kernels, `α_Y ∘ op f gs ≈ op f (α_Y ∘ gs)`; equivalently, the induced functor `Kℓ(S) → Kℓ(T)`
-- preserves the operations. 
--   `IsAlgebraic⇒ Th S T α`   the preservation law, as a property of a monad morphism `α`
--   `Algebraic⇒ Th S T`       a monad morphism together with `IsAlgebraic⇒`, with `Algebraic⇒-id` and `Algebraic⇒-∘ f g`
--                             (`f` first)
open import Categories.Category.Core using (Category)

module Categories.Monad.Algebraic.Morphism {o h e} {C : Category o h e} where

open import Level using (_⊔_)
open import Data.Fin.Base using (Fin)

open import Categories.Monad.Algebraic using (Algebraic)
open import Categories.Monad.Morphism using (Monad⇒-id; Monad⇒-id-id; Monad⇒-id-∘)
import Categories.Monad.Notation as Notation
open import Categories.Theory.Equational using (Theory)

open Category C
open HomReasoning

-- a monad morphism `α : S ⇒ T` preserves the operations of `Th`
record IsAlgebraic⇒ (Th : Theory) (S T : Algebraic {C = C} Th)
  (α : Monad⇒-id (Algebraic.M T) (Algebraic.M S)) : Set (o ⊔ h ⊔ e) where
  private
    module S = Notation (Algebraic.M S)
    module α = Monad⇒-id α
  open Theory Th
  open Algebraic S using () renaming (op to opˢ)
  open Algebraic T using () renaming (op to opᵗ)
  field
    α-op : ∀ (f : Op) {X Y} (gs : Fin (arity f) → X ⇒ S.₀ Y)
      → α.α.η Y ∘ opˢ f gs ≈ opᵗ f (λ i → α.α.η Y ∘ gs i)

-- an algebraic monad morphism `S ⇒ T`
record Algebraic⇒ (Th : Theory) (S T : Algebraic {C = C} Th) : Set (o ⊔ h ⊔ e) where
  field
    monad⇒ : Monad⇒-id (Algebraic.M T) (Algebraic.M S)
    isAlgebraic⇒ : IsAlgebraic⇒ Th S T monad⇒
  open Monad⇒-id monad⇒ public
  open IsAlgebraic⇒ isAlgebraic⇒ public

module _ {Th : Theory} where
  open Theory Th

  module _ {S : Algebraic {C = C} Th} where
    private module S = Algebraic S

    Algebraic⇒-id : Algebraic⇒ Th S S
    Algebraic⇒-id = record
      { monad⇒ = Monad⇒-id-id
      ; isAlgebraic⇒ = record
        { α-op = λ f gs → identityˡ ○ S.op-cong f (λ i → ⟺ identityˡ) }
      }

  module _ {S T R : Algebraic {C = C} Th} (f : Algebraic⇒ Th S T) (g : Algebraic⇒ Th T R) where
    private
      module S = Algebraic S
      module SM = Notation (Algebraic.M S)
      module T = Algebraic T
      module R = Algebraic R
      module f = Algebraic⇒ f
      module g = Algebraic⇒ g

    ∘-α-op : ∀ (φ : Op) {X Y} (us : Fin (arity φ) → X ⇒ SM.₀ Y)
      → (g.α.η Y ∘ f.α.η Y) ∘ S.op φ us ≈ R.op φ (λ i → (g.α.η Y ∘ f.α.η Y) ∘ us i)
    ∘-α-op φ us = begin
      (g.α.η _ ∘ f.α.η _) ∘ S.op φ us                    ≈⟨ assoc ⟩
      g.α.η _ ∘ f.α.η _ ∘ S.op φ us                      ≈⟨ refl⟩∘⟨ f.α-op φ us ⟩
      g.α.η _ ∘ T.op φ (λ i → f.α.η _ ∘ us i)            ≈⟨ g.α-op φ _ ⟩
      R.op φ (λ i → g.α.η _ ∘ f.α.η _ ∘ us i)            ≈⟨ R.op-cong φ (λ i → sym-assoc) ⟩
      R.op φ (λ i → (g.α.η _ ∘ f.α.η _) ∘ us i)          ∎

    -- composition: `f` first, then `g`
    Algebraic⇒-∘ : Algebraic⇒ Th S R
    Algebraic⇒-∘ = record
      { monad⇒ = Monad⇒-id-∘ f.monad⇒ g.monad⇒
      ; isAlgebraic⇒ = record { α-op = ∘-α-op }
      }
