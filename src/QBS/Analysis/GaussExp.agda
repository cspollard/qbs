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

open import QBS.Analysis.Omega using (OmegaSemiring)
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

