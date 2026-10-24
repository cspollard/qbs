{-# OPTIONS --safe --without-K #-}

-- Sub-probability measures: the weight class "total mass ≤ 1" (mass + defect = 1).  The discrete
-- measure monad of `Model/Monad.agda` is generic in the weight class, so this gives a commutative
-- strong monad of sub-probability measures (with `fail`, the zero measure, and rejection-style
-- conditioning) with no further proofs.
module QBS.Model.SubProb where

open import Level using (Level; Lift; lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad

module _ {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open SetoidReasoning Aˢ
  private R = Lift ℓ ℕ

  private
    -- the mass of a Dirac measure and of a push-forward
    diracMass : ∀ (j : R) → ∑ (dirac j) ≈ 1#
    diracMass j = trans (∑-cong (λ r → sym (*-identityʳ (dirac j r)))) (dirac-∑ j (λ _ → 1#))

    pushMass : ∀ (f : R → R) (μ : R → ∣A∣) → ∑ (push f μ) ≈ ∑ μ
    pushMass f μ = trans (∑-cong (λ j → sym (*-identityʳ (push f μ j))))
      (trans (push-∑ f μ (λ _ → 1#)) (∑-cong (λ i → *-identityʳ (μ i))))

  subClass : WeightClass A
  subClass = record
    { Ok = λ μ → Σ ∣A∣ (λ d → ∑ μ + d ≈ 1#)
    ; ok-resp = λ e (d , p) → d , trans (+-cong (sym (∑-cong e)) refl) p
    ; ok-dirac = λ r₀ → 0# , trans (+-identityʳ _) (diracMass r₀)
    ; ok-push = λ f (d , p) → d , trans (+-cong (pushMass f _) refl) p
    ; ok-bind = λ {ν} {g} (e , pν) hg →
        let m : R → ∣A∣
            m r = ∑ (g r)
            d : R → ∣A∣
            d r = proj₁ (hg r)
            pd : ∀ r → m r + d r ≈ 1#
            pd r = proj₂ (hg r)
            T = ∑ (λ k → ∑ (λ r → ν r * g r k))
            D = ∑ (λ r → ν r * d r)
            -- T = Σ_r ν r * m r
            T≈ : T ≈ ∑ (λ r → ν r * m r)
            T≈ = trans (∑-swap (λ k r → ν r * g r k)) (∑-cong (λ r → ∑-scale (ν r) (g r)))
            -- Σ_r ν r * m r + Σ_r ν r * d r = Σ ν
            mass : ∑ (λ r → ν r * m r) + D ≈ ∑ ν
            mass = begin
              ∑ (λ r → ν r * m r) + ∑ (λ r → ν r * d r)  ≈⟨ sym (∑-+ (λ r → ν r * m r) (λ r → ν r * d r)) ⟩
              ∑ (λ r → ν r * m r + ν r * d r)            ≈⟨ ∑-cong (λ r → sym (distribˡ (ν r) (m r) (d r))) ⟩
              ∑ (λ r → ν r * (m r + d r))                ≈⟨ ∑-cong (λ r → trans (*-cong refl (pd r)) (*-identityʳ (ν r))) ⟩
              ∑ ν                                         ∎
        in D + e ,
           (begin
              T + (D + e)                           ≈⟨ +-cong T≈ refl ⟩
              ∑ (λ r → ν r * m r) + (D + e)         ≈⟨ sym (+-assoc _ D e) ⟩
              (∑ (λ r → ν r * m r) + D) + e         ≈⟨ +-cong mass refl ⟩
              ∑ ν + e                               ≈⟨ pν ⟩
              1# ∎)
    }

  -- the monad of sub-probability measures on the discrete model, with its strength; everything
  -- (functor, unit, join, laws, commutativity by Tonelli) comes from the generic construction
  module Sub = Measures A subClass
  open import QBS.Model.Strong using (module Strength)
  module SubStrength = Strength A subClass
