{-# OPTIONS --safe --without-K #-}

-- Ring identities on parts of signed values for the variance of independent sums (plan 05, helper for `IndepAlg`).
--   * `sa-cross`, `sa-sums`: (f + g)² = (f² + f g) + (f g + g²) on the parts (as `SignedVarRing` identities);
--   * `var-cross`: ((e₁ + a b) + (a b + e₂)) − (a + b)² = (e₁ − a²) + (e₂ − b²).
-- Route: one `solve` of the natural-coefficient ring solver each, over an abstract commutative semiring.
module QBS.Continuous.IndepRing where

open import Algebra using (CommutativeSemiring)
open import Data.Product.Base using (_,_)
open import QBS.Continuous.SignedVarRing using (module Ring)

module IRing {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (refl)
  open Ring R using (Pr; _⊕_; _⊗_; ng; cross; sums; Pa; _⊕ᵃ_; _⊗ᵃ_; ngᵃ; crossᵃ; sumsᵃ)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R

  -- (a + c)² and (a² + a c) + (a c + c²)
  SA SA′ : ∀ {n} → Pr n → Pr n → Pr n
  SA a c = (a ⊕ c) ⊗ (a ⊕ c)
  SA′ a c = ((a ⊗ a) ⊕ (a ⊗ c)) ⊕ ((a ⊗ c) ⊕ (c ⊗ c))

  SAᵃ SA′ᵃ : Pa → Pa → Pa
  SAᵃ a c = (a ⊕ᵃ c) ⊗ᵃ (a ⊕ᵃ c)
  SA′ᵃ a c = ((a ⊗ᵃ a) ⊕ᵃ (a ⊗ᵃ c)) ⊕ᵃ ((a ⊗ᵃ c) ⊕ᵃ (c ⊗ᵃ c))

  sa-cross : ∀ a b c d → crossᵃ (SAᵃ (a , b) (c , d)) (SA′ᵃ (a , b) (c , d))
  sa-cross a b c d = solve 4 (λ a b c d → cross (SA (a , b) (c , d)) (SA′ (a , b) (c , d))) refl a b c d

  sa-sums : ∀ a b c d → sumsᵃ (SAᵃ (a , b) (c , d)) (SA′ᵃ (a , b) (c , d))
  sa-sums a b c d = solve 4 (λ a b c d → sums (SA (a , b) (c , d)) (SA′ (a , b) (c , d))) refl a b c d

  -- the variance identity
  VL VR : ∀ {n} → Pr n → Pr n → Pr n → Pr n → Pr n
  VL e₁ e₂ a b = (((e₁ ⊕ (a ⊗ b)) ⊕ ((a ⊗ b) ⊕ e₂)) ⊕ ng ((a ⊕ b) ⊗ (a ⊕ b)))
  VR e₁ e₂ a b = ((e₁ ⊕ ng (a ⊗ a)) ⊕ (e₂ ⊕ ng (b ⊗ b)))

  VLᵃ VRᵃ : Pa → Pa → Pa → Pa → Pa
  VLᵃ e₁ e₂ a b = (((e₁ ⊕ᵃ (a ⊗ᵃ b)) ⊕ᵃ ((a ⊗ᵃ b) ⊕ᵃ e₂)) ⊕ᵃ ngᵃ ((a ⊕ᵃ b) ⊗ᵃ (a ⊕ᵃ b)))
  VRᵃ e₁ e₂ a b = ((e₁ ⊕ᵃ ngᵃ (a ⊗ᵃ a)) ⊕ᵃ (e₂ ⊕ᵃ ngᵃ (b ⊗ᵃ b)))

  var-cross : ∀ p₁ n₁ p₂ n₂ x y z w →
    crossᵃ (VLᵃ (p₁ , n₁) (p₂ , n₂) (x , y) (z , w)) (VRᵃ (p₁ , n₁) (p₂ , n₂) (x , y) (z , w))
  var-cross p₁ n₁ p₂ n₂ x y z w = solve 8
    (λ p₁ n₁ p₂ n₂ x y z w → cross (VL (p₁ , n₁) (p₂ , n₂) (x , y) (z , w)) (VR (p₁ , n₁) (p₂ , n₂) (x , y) (z , w)))
    refl p₁ n₁ p₂ n₂ x y z w
