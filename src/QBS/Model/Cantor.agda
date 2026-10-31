{-# OPTIONS --safe --without-K #-}

-- Reindexing sums over R = ℕ by pairs, through the Cantor pairing.
module QBS.Model.Cantor where

open import Level using (Level; Lift; lift; lower)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Model.Pairing
open import QBS.Model.Semiring
open import QBS.Model.Sums

module Cantor {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣)
  open Sums A
  private R = Lift ℓ ℕ

  -- the two components of unpair, and the index map of ⟨n, –⟩
  ιR ρR : R → R
  ιR k = lift (proj₁ (unpair (lower k)))
  ρR k = lift (proj₂ (unpair (lower k)))

  φ : ℕ → R → R
  φ n m = lift (pair n (lower m))

  cantorIso : Σ R (λ _ → R) ↔ R
  cantorIso = mk↔ₛ′ (λ p → lift (pair (lower (proj₁ p)) (lower (proj₂ p))))
    (λ k → ιR k , ρR k)
    (λ k → ≡.cong lift (pair-unpair (lower k)))
    (λ { (r₁ , r₂) → ≡.cong₂ _,_ (≡.cong (λ u → lift (proj₁ u)) (unpair-pair (lower r₁) (lower r₂)))
                                 (≡.cong (λ u → lift (proj₂ u)) (unpair-pair (lower r₁) (lower r₂))) })

  cantor-cong : ∀ (F : R → R → ∣A∣) r₁ r₂ →
    F r₁ r₂ ≈ F (ιR (lift (pair (lower r₁) (lower r₂)))) (ρR (lift (pair (lower r₁) (lower r₂))))
  cantor-cong F r₁ r₂ = reflexive (≡.cong₂ F
    (≡.sym (≡.cong (λ u → lift (proj₁ u)) (unpair-pair (lower r₁) (lower r₂))))
    (≡.sym (≡.cong (λ u → lift (proj₂ u)) (unpair-pair (lower r₁) (lower r₂)))))

  -- summing over R = ℕ is summing over pairs
  cantor : ∀ (F : R → R → ∣A∣) → ∑ (λ k → F (ιR k) (ρR k)) ≈ ∑ (λ a → ∑ (λ b → F a b))
  cantor F = trans (sym (∑-reindex cantorIso (λ k → F (ιR k) (ρR k))))
    (trans (∑-cong (λ p → sym (cantor-cong F (proj₁ p) (proj₂ p))))
           (∑-Σ {J = λ _ → R} (λ p → F (proj₁ p) (proj₂ p))))

  -- the weights of ⟨n, –⟩ pushed along φ n, tested against a function of the unpaired indices
  push-pair-∑ : ∀ n (μ : R → ∣A∣) (H : ℕ × ℕ → ∣A∣) →
    ∑ (λ k → push (φ n) μ k * H (unpair (lower k))) ≈ ∑ (λ m → μ m * H (n , lower m))
  push-pair-∑ n μ H = trans (push-∑ (φ n) μ (λ k → H (unpair (lower k))))
    (∑-cong (λ m → *-cong refl (reflexive (≡.cong H (unpair-pair n (lower m))))))
