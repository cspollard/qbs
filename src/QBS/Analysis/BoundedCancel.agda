{-# OPTIONS --safe --without-K #-}

-- Cancellation of elements bounded by a natural number: `a ≤ n`, `a + x = a + y` give `x = y`.
-- `OmegaSemiring.cancel` handles `a ≤ 1`; for `a ≤ 2ᵏ` halve `k` times (`half + half = 1`), cancel, and double
-- back.  Needed so that equality of bounded signed functions (pointwise equality of signed values, whose witness
-- is a bounded element) implies equality of the cross sums.
module QBS.Analysis.BoundedCancel where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ₙ_)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Data.Nat.Properties using (+-mono-≤; n≤1+n) renaming (≤-trans to ≤ₙ-trans)
open import Data.Product.Base using (Σ; _,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Half using (module Half)

module BoundedCancel (A : OmegaSemiring (L.suc L.zero)) (half : OmegaSemiring.Carrier A)
  (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Bounded A using (nat; nat-+; Bnd)
  open Half A half hh using (half-twice)

  -- 2ᵏ⁺¹ = 2ᵏ + 2ᵏ, and k < 2ᵏ
  2^-suc : ∀ k → 2 ℕ.^ suc k ≡ 2 ℕ.^ k ℕ.+ 2 ℕ.^ k
  2^-suc k = ≡.cong (2 ℕ.^ k ℕ.+_) (ℕ.+-identityʳ (2 ℕ.^ k))

  suc≤2^ : ∀ k → suc k ≤ₙ 2 ℕ.^ k
  suc≤2^ zero = s≤s z≤n
  suc≤2^ (suc k) = ≡.subst (suc (suc k) ≤ₙ_) (≡.sym (2^-suc k))
    (+-mono-≤ (≤ₙ-trans (s≤s z≤n) (suc≤2^ k)) (suc≤2^ k))

  -- n ≤ m gives nat n ≤ nat m
  nat-mono : ∀ {n m} → n ≤ₙ m → nat n ≤ nat m
  nat-mono z≤n = 0-least
  nat-mono (s≤s h) = +-mono ≤-refl (nat-mono h)

  -- ½ · (n + n) = n
  double-half : ∀ x → half * x + half * x ≈ x
  double-half x = trans (sym (distribˡ half x x)) (half-twice x)

  half-nat : ∀ n → half * nat (n ℕ.+ n) ≈ nat n
  half-nat n = trans (*-cong refl (nat-+ n n)) (half-twice (nat n))

  -- cancellation below 2ᵏ, by induction on k
  cancel-pow : ∀ k {a x y} → a ≤ nat (2 ℕ.^ k) → a + x ≈ a + y → x ≈ y
  cancel-pow zero {a} h e = cancel (≤-trans h (≤-reflexive (+-identityʳ 1#))) e
  cancel-pow (suc k) {a} {x} {y} h e = trans (sym (double-half x)) (trans (+-cong hx hx) (double-half y))
    where
      small : half * a ≤ nat (2 ℕ.^ k)
      small = ≤-trans (*-mono half (≡.subst (λ m → a ≤ nat m) (2^-suc k) h)) (≤-reflexive (half-nat (2 ℕ.^ k)))
      e′ : half * a + half * x ≈ half * a + half * y
      e′ = trans (sym (distribˡ half a x)) (trans (*-cong refl e) (distribˡ half a y))
      hx : half * x ≈ half * y
      hx = cancel-pow k small e′

  cancel-bnd : ∀ {a x y} → Bnd a → a + x ≈ a + y → x ≈ y
  cancel-bnd {a} (N , h) = cancel-pow N (≤-trans h (nat-mono (≤ₙ-trans (n≤1+n N) (suc≤2^ N))))
