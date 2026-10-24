{-# OPTIONS --safe --without-K #-}

-- The two weight classes: probability measures (total mass 1) and all measures.
module QBS.Model.WeightClasses where

open import Level using (Level; suc; Lift; lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad

module _ {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A
  open Sums A
  open SetoidReasoning setoid
  private R = Lift ℓ ℕ

  -- every weight function is a (not necessarily finite) measure
  allClass : WeightClass A
  allClass = record
    { Ok = λ _ → ⊤
    ; ok-resp = λ _ _ → tt
    ; ok-dirac = λ _ → tt
    ; ok-push = λ _ _ → tt
    ; ok-bind = λ _ _ → tt
    }

  -- probability measures: total mass 1
  probClass : WeightClass A
  probClass = record
    { Ok = λ μ → ∑ μ ≈ 1#
    ; ok-resp = λ e m → trans (sym (∑-cong e)) m
    ; ok-dirac = λ r₀ → trans (∑-cong (λ j → sym (*-identityʳ _))) (dirac-∑ r₀ (λ _ → 1#))
    ; ok-push = λ {μ} f m →
        trans (∑-cong (λ j → sym (*-identityʳ _)))
          (trans (push-∑ f μ (λ _ → 1#))
            (trans (∑-cong (λ i → *-identityʳ _)) m))
    ; ok-bind = λ {ν} {g} mν mg → begin
        ∑ (λ k → ∑ (λ r → ν r * g r k))      ≈⟨ ∑-swap (λ k r → ν r * g r k) ⟩
        ∑ (λ r → ∑ (λ k → ν r * g r k))      ≈⟨ ∑-cong (λ r → ∑-scale (ν r) (g r)) ⟩
        ∑ (λ r → ν r * ∑ (g r))              ≈⟨ ∑-cong (λ r → *-cong refl (mg r)) ⟩
        ∑ (λ r → ν r * 1#)                   ≈⟨ ∑-cong (λ r → *-identityʳ _) ⟩
        ∑ ν                                  ≈⟨ mν ⟩
        1#                                   ∎
    }
