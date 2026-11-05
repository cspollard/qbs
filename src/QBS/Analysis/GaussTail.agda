{-# OPTIONS --safe --without-K #-}

-- Small facts for the Gaussian tail and finiteness, over an abstract Archimedean ω-semiring A.
--   * `big N : natE N ≤ ½ (natE N)²` for N ≥ 2 (so `e^{−x²/2} ≤ e^{−x}` at the integers N ≥ 2):
--     with x = natE N = 2 + r, `x + x ≤ x (2 + r) = x²`, and `½ (x + x) = x`;
--   * `four`: `(1 + 1) + (1 + 1)` as the natural number 4 (the bound on `∫ e^{−x²/2}`, as `∑ᶠ (2 · ½ⁿ) ≤ 4`).
module QBS.Analysis.GaussTail where

import Level as L
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Product.Base using (_,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.PolyExpCert using (module AlgP)

module AlgGT (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half-twice)
  open AlgP A R using (natE-+)
  open Exp A using (natE)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  big : ∀ N → 2 ℕ.≤ N → natE N ≤ half * (natE N * natE N)
  big N le with ℕ.m≤n⇒∃[o]m+o≡n le
  ... | r , ≡.refl = ≤-trans (≤-reflexive (sym (half-twice x))) (*-mono half xx)
    where
    x : ∣A∣
    x = natE (2 ℕ.+ r)
    e : x ≈ natE 2 + natE r
    e = natE-+ 2 r
    a2 : natE 2 ≈ 1# + 1#
    a2 = +-cong (+-identityˡ 1#) refl
    xx : x + x ≤ x * x
    xx = ≤-trans (≤-reflexive (trans (solve 1 (λ y → y :+ y := y :* (con 1 :+ con 1)) refl x) (*-cong refl (sym a2))))
      (≤-trans ≤-+ʳ (≤-reflexive (trans (sym (distribˡ x (natE 2) (natE r))) (*-cong refl (sym e)))))

  four : (1# + 1#) + (1# + 1#) ≈ 1# + (1# + (1# + (1# + 0#)))
  four = solve 1 (λ o → (o :+ o) :+ (o :+ o) := o :+ (o :+ (o :+ (o :+ con 0)))) refl 1#
