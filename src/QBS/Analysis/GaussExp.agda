{-# OPTIONS --safe --without-K #-}

-- Small algebra for the Gaussian exponential facts `E u + u E u ≤ 1 ≤ E u + u` (`E = e^{−x}`), over an abstract
-- Archimedean ω-semiring A.
--   * `bd m = 2m + 1`: the bound `2ᵇ` on the arguments of E used by `Continuous/GaussHalfLine`;
--   * `eb : y e = 1 → 1 + u ≤ e → y + u y ≤ 1` (the first fact, from `1 + u ≤ eᵘ` with `e^{−u} eᵘ = 1`);
--   * `ec-big : 1 ≤ u → 1 ≤ y + u` (the second fact for u ≥ 1, where it is trivial).
-- (The Gaussian certificate itself, `Φ (a + w) = Φ a · Y a w` with its first-order bounds, is now the chain rule of
-- `Analysis/DerivChain` and `Analysis/DerivGauss`; the hand-written `Gauss` module that derived it here was retired.)
module QBS.Analysis.GaussExp where

import Level as L
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Product.Base using (_,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)

-- the bound on the arguments of E: 2ᵇ with b = 2m + 1
bd : ℕ → ℕ
bd m = suc (m ℕ.+ m)

module AlgGE (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half+half; half-twice)
  open AlgT A R using (P; P≥1)
  open HalfOrder A R using (half≤1)
  open AlgP A R using (*-monoʳ; *-mono₂; P-mono; P-+; P-*; yt)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  half≤ : ∀ z → half * z ≤ z
  half≤ z = ≤-trans (*-monoʳ z half≤1) (≤-reflexive (*-identityˡ z))

  -- `y e = 1` and `1 + u ≤ e` give `y + u y ≤ 1`; and `1 ≤ u` gives `1 ≤ y + u`
  eb : ∀ {y u e} → y * e ≈ 1# → 1# + u ≤ e → y + u * y ≤ 1#
  eb {y} {u} {e} ye lo = ≤-trans (≤-reflexive (solve 2 (λ y′ w′ → y′ :+ w′ :* y′ := y′ :* (con 1 :+ w′)) refl y u))
    (≤-trans (*-mono y lo) (≤-reflexive ye))

  ec-big : ∀ {y u} → 1# ≤ u → 1# ≤ y + u
  ec-big {y} {u} h = ≤-trans h (≤-trans ≤-+ʳ (≤-reflexive (+-comm u y)))

-- Small facts for the Gaussian tail and finiteness (formerly `Analysis/GaussTail`).
--   * `big N : natE N ≤ ½ (natE N)²` for N ≥ 2 (so `e^{−x²/2} ≤ e^{−x}` at the integers N ≥ 2):
--     with x = natE N = 2 + r, `x + x ≤ x (2 + r) = x²`, and `½ (x + x) = x`;
--   * `four`: `(1 + 1) + (1 + 1)` as the natural number 4 (the bound on `∫ e^{−x²/2}`, as `∑ᶠ (2 · ½ⁿ) ≤ 4`).
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

