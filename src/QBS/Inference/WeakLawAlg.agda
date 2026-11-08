{-# OPTIONS --safe --without-K #-}

-- Order algebra on [0, ∞] and the signed values for `Inference/WeakLaw` (plan 05 item 50).
--   * `cong-≤`: a + y⁻ ≤ y⁺ from a + x⁻ ≤ x⁺ and x ≃ y (add the finite x⁻ + k, cancel with `SignedLimitsAlg.cancel-le`);
--   * `natS-parts`: the parts of the signed natural n are nat n and 0;
--   * `rate-alg`: from (N e)² ∫χ ≤ᵛ N σ² (N = nat (m + 1)) to N e² ∫χ ≤ᵛ σ², cancelling N (`NatCancel.cancel-nat`).
-- Route: ring identities by the natural-coefficient solver, with the parts of N σ² computed by `natS-parts`.
module QBS.Inference.WeakLawAlg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.SignedLimitsAlg using (module SignedLimitsAlg)
open import QBS.Continuous.NatCancel using (module NatCancel)
open import QBS.Continuous.SgMoments using (module SgMoments)

module WeakLawAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; zeroˡ; +-identityʳ; +-identityˡ;
    +-mono; ≤-trans; ≤-reflexive; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; _≃_; _*S_; nat; finite; 0S; mk≃)
  open Sg
  open SubSemiring finite using (Is-+)
  open SignedLimitsAlg lem₁ using (cancel-le)
  open NatCancel lem₁ using (cancel-nat)
  open SgMoments lem₁ using (natS)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- a ≤ x, and x ≃ y, give a ≤ y
  cong-≤ : ∀ {a} {x y : Sg} → a + neg x ≤ pos x → x ≃ y → a + neg y ≤ pos y
  cong-≤ {a} {x} {y} h (mk≃ k fk e) = cancel-le {neg x + k} (Is-+ {_} {_} (neg-fin x) fk)
    (≤-trans (≤-reflexive (solve 4 (λ a nx ny k → (nx :+ k) :+ (a :+ ny) := (a :+ nx) :+ (ny :+ k)) refl a (neg x) (neg y) k))
    (≤-trans (+-mono h (≤-reflexive refl))
    (≤-trans (≤-reflexive (solve 3 (λ px ny k → px :+ (ny :+ k) := px :+ ny :+ k) refl (pos x) (neg y) k))
    (≤-trans (≤-reflexive e)
      (≤-reflexive (solve 3 (λ py nx k → py :+ nx :+ k := (nx :+ k) :+ py) refl (pos y) (neg x) k))))))

  -- the parts of n
  natS-parts : ∀ k → pos (natS k) ≈ nat k × neg (natS k) ≈ 0#
  natS-parts zero = refl , refl
  natS-parts (suc k) = +-cong refl (proj₁ (natS-parts k)) , trans (+-cong refl (proj₂ (natS-parts k))) (+-identityˡ 0#)

  -- the parts of n σ
  neg-nσ : ∀ k (σ : Sg) → neg (natS k *S σ) ≈ nat k * neg σ
  neg-nσ k σ = trans (+-cong (*-cong (proj₁ (natS-parts k)) refl) (trans (*-cong (proj₂ (natS-parts k)) refl) (zeroˡ _)))
    (+-identityʳ _)

  pos-nσ : ∀ k (σ : Sg) → pos (natS k *S σ) ≈ nat k * pos σ
  pos-nσ k σ = trans (+-cong (*-cong (proj₁ (natS-parts k)) refl) (trans (*-cong (proj₂ (natS-parts k)) refl) (zeroˡ _)))
    (+-identityʳ _)

  -- N² e² I + N σ⁻ ≤ N σ⁺ gives N e² I + σ⁻ ≤ σ⁺
  rate-alg : ∀ m (e I : ∣A∣) (σ : Sg) →
    ((nat (suc m) * e) * (nat (suc m) * e)) * I + neg (natS (suc m) *S σ) ≤ pos (natS (suc m) *S σ) →
    (nat (suc m) * (e * e)) * I + neg σ ≤ pos σ
  rate-alg m e I σ h = cancel-nat m (≤-trans (≤-reflexive lhs) (≤-trans h (≤-reflexive (pos-nσ (suc m) σ))))
    where
      N = nat (suc m)
      lhs : N * ((N * (e * e)) * I + neg σ) ≈ ((N * e) * (N * e)) * I + neg (natS (suc m) *S σ)
      lhs = trans (solve 4 (λ N e I s → N :* ((N :* (e :* e)) :* I :+ s) := ((N :* e) :* (N :* e)) :* I :+ N :* s) refl N e I (neg σ))
        (+-cong refl (sym (neg-nσ (suc m) σ)))
