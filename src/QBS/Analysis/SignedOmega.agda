{-# OPTIONS --safe --without-K #-}

-- Signed values over an `OmegaSemiring` (for the extended non-negative reals): the "finite" elements are those
-- bounded by a natural number, and `Analysis/Signed` gives the ring of their differences.
module QBS.Analysis.SignedOmega where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_)

open import QBS.Analysis.Omega
open import QBS.Analysis.Signed

module Bounded (A : OmegaSemiring (L.suc L.zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  open import Algebra.Properties.Semiring.Mult semiring using (_×_; ×-homo-+; idem-×-homo-*)

  -- the natural number n as an element of A
  nat : ℕ → ∣A∣
  nat n = n × 1#

  nat-+ : ∀ n m → nat (n ℕ.+ m) ≈ nat n + nat m
  nat-+ n m = ×-homo-+ 1# n m

  nat-* : ∀ n m → nat (n ℕ.* m) ≈ nat n * nat m
  nat-* n m = sym (idem-×-homo-* n m (*-identityˡ 1#))

  -- bounded by a natural number
  Bnd : ∣A∣ → Set (L.suc L.zero)
  Bnd a = Σ ℕ λ n → a ≤ nat n

  finite : SubSemiring commutativeSemiring (L.suc L.zero)
  finite = record
    { Is = Bnd
    ; Is-resp = λ e (n , h) → n , ≤-trans (≤-reflexive (sym e)) h
    ; Is-0 = 0 , 0-least
    ; Is-1 = 1 , ≤-reflexive (sym (+-identityʳ 1#))
    ; Is-+ = λ { (n , h) (m , g) → n ℕ.+ m , ≤-trans (+-mono h g) (≤-reflexive (sym (nat-+ n m))) }
    ; Is-* = λ { {a} {b} (n , h) (m , g) → n ℕ.* m ,
        ≤-trans (*-mono a g) (≤-trans (≤-reflexive (*-comm a (nat m)))
          (≤-trans (*-mono (nat m) h) (≤-trans (≤-reflexive (*-comm (nat m) (nat n))) (≤-reflexive (sym (nat-* n m)))))) }
    }

  open Signed commutativeSemiring finite public
