{-# OPTIONS --safe --without-K #-}

-- Cancelling a positive natural factor in the order of the lower reals (lower-real arithmetic, misfiled here; helper for `Inference/WeakLaw`).
--   * `cancel-nat m`: (m + 1) x ≤ (m + 1) y gives x ≤ y, for any x, y in [0, ∞] (also infinite ones).
-- Route: multiply by the reciprocal cut 1/(m + 1) (`ExpLower.qinvC`), which satisfies 1/(m + 1) · (m + 1) = 1
-- (`ExpLower.inv-ok`, transported along `natE (m + 1) ≈ nat (m + 1)`); then x = 1/(m+1) · ((m+1) x) ≤ 1/(m+1) · ((m+1) y) = y
-- by monotonicity and associativity of `*`.
module QBS.Continuous.NatCancel where

open import Data.Nat.Base using (ℕ; suc)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.ExpLower using (qinvC; inv-ok)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)

module NatCancel (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _*_; 1#; refl; sym; trans; *-cong; *-assoc; *-identityˡ; *-mono; ≤-trans; ≤-reflexive)
  open Bounded A using (nat)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)

  -- 1/(m + 1) · (m + 1) = 1
  inv-nat : ∀ m → qinvC (lemOf lem₁) m * nat (suc m) ≈ 1#
  inv-nat m = trans (*-cong refl (sym (natE≈nat (suc m)))) (inv-ok (lemOf lem₁) m)

  cancel-nat : ∀ m {x y} → nat (suc m) * x ≤ nat (suc m) * y → x ≤ y
  cancel-nat m {x} {y} h = ≤-trans (≤-reflexive (sym (cx x))) (≤-trans (*-mono q h) (≤-reflexive (cx y)))
    where
      q = qinvC (lemOf lem₁) m
      cx : ∀ z → q * (nat (suc m) * z) ≈ z
      cx z = trans (sym (*-assoc q (nat (suc m)) z)) (trans (*-cong (inv-nat m) refl) (*-identityˡ z))
