{-# OPTIONS --safe --without-K #-}

-- A certificate calculus for the tail FTC (part 3: the base cases `xⁿ` and `e^{−x}`, and `xʲ⁺¹ e^{−x}`).
--
-- Over an abstract Archimedean ω-semiring with the exponential data of `Analysis/PolyExpCert` (`Ex`: E x ≤ 1, E antitone,
-- E (a + t) = E a E t when a + t ≤ M and t ≤ 1, and the first-order facts E t + t E t ≤ 1 ≤ E t + t):
--   * `DE : D M 1 E E 0`, i.e. `(e^{−x})′ = −e^{−x}`: the Lipschitz bounds are `E-lipD` (reused from `Ex`) and monotonicity,
--     the certificate is `E a (E w + w) ≤ E a (1 + w²)` (`yt`, reused) and `1 ≤ E w + w`;
--   * `pwD i : Deriv M (xⁱ) 0 (dpw i)`, by induction with the product rule from the identity (and `dpw` of `Analysis/PolyExpCert`);
--   * `xjE j : Deriv M (xʲ⁺¹ e^{−x}) (xʲ⁺¹ e^{−x}) ((j+1) xʲ e^{−x})`, the integration-by-parts data of
--     `Analysis/PolyExpCert.Ex.pack`, now from the rules instead of a 300-line pack (for any M with `Fin M`).
module QBS.Analysis.DerivExp where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivProd using (module AlgDP)

module AlgDE (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgT A R using (P)
  open AlgP A R using (pw; dpw; yt; module Ex)
  open Exp A using (natE)
  open AlgD A R
  open AlgDP A R using (DFprod)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the powers

  pwD : ∀ {M} → Fin M → ∀ i → Deriv M (pw i) (λ _ → 0#) (dpw i)
  pwD fM zero = DFconst 1# Fin-1
  pwD {M} fM (suc i) = DFresp {G = λ x → x * pw i x} {h = λ x → 0# * pw i x + x * 0#} {k = λ x → 1# * pw i x + x * dpw i x}
    {G′ = pw (suc i)} {h′ = λ _ → 0#} {k′ = dpw (suc i)} (λ _ → refl)
    (λ x → trans (+-cong (zeroˡ _) (zeroʳ _)) (+-identityˡ 0#)) (λ x → +-cong (*-identityˡ _) refl)
    (DFprod (DFid fM) (pwD fM i))

  ----------------------------------------------------------------------------
  -- the exponential

  module Expo (E : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x) (E-cong : ∀ {x y} → x ≈ y → E x ≈ E y)
    (E-add : ∀ {a t} → a + t ≤ M → t ≤ 1# → E (a + t) ≈ E a * E t)
    (E-b : ∀ {t} → t ≤ 1# → E t + t * E t ≤ 1#) (E-c : ∀ {t} → t ≤ 1# → 1# ≤ E t + t) where
    module X = Ex E M m Mm E≤1 E-anti E-add E-b E-c

    private
      eq1 : ∀ p y w → p * y + w * p ≈ p * (y + w)
      eq1 p y w = solve 3 (λ p′ y′ w′ → p′ :* y′ :+ w′ :* p′ := p′ :* (y′ :+ w′)) refl p y w

      eq2 : ∀ p w → p * (1# + w * w) ≈ p + (w * w) * p
      eq2 p w = solve 2 (λ p′ w′ → p′ :* (con 1 :+ w′ :* w′) := p′ :+ (w′ :* w′) :* p′) refl p w

      eq3 : ∀ p w → p + (w * w) * 1# ≈ (p + w * 0#) + (w * w) * 1#
      eq3 p w = solve 2 (λ p′ w′ → p′ :+ (w′ :* w′) :* con 1 := (p′ :+ w′ :* con 0) :+ (w′ :* w′) :* con 1) refl p w

      eq0 : ∀ p w → p + w * 0# ≈ p * 1#
      eq0 p w = solve 2 (λ p′ w′ → p′ :+ w′ :* con 0 := p′ :* con 1) refl p w

    DE : D M 1# E E (λ _ → 0#)
    DE = mkD E-cong E-cong (λ _ → refl) (λ _ → E≤1 _) (λ _ → E≤1 _) (λ _ → 0-least)
      (λ {a} {w} _ _ → ≤-trans (E-anti ≤-+ʳ) ≤-+ʳ)
      (λ {a} {w} aw w1 → ≤-trans (X.E-lipD aw w1) (+-mono ≤-refl (≤-reflexive (sym (*-identityʳ w)))))
      (λ _ _ → 0-least) (λ _ _ → 0-least)
      (λ {a} {w} aw w1 → ≤-trans (≤-reflexive (+-cong (E-add aw w1) refl))
        (≤-trans (≤-reflexive (eq1 (E a) (E w) w))
          (≤-trans (*-mono (E a) (yt (E-b w1) (E-c w1)))
            (≤-trans (≤-reflexive (eq2 (E a) w))
              (≤-trans (+-mono ≤-refl (*-mono (w * w) (E≤1 a))) (≤-reflexive (eq3 (E a) w)))))))
      (λ {a} {w} aw w1 → ≤-trans (≤-reflexive (eq0 (E a) w))
        (≤-trans (*-mono (E a) (E-c w1))
          (≤-trans (≤-reflexive (sym (eq1 (E a) (E w) w)))
            (≤-trans (≤-reflexive (+-cong (sym (E-add aw w1)) refl)) ≤-+ʳ))))

    DFE : Deriv M E E (λ _ → 0#)
    DFE = 1# , Fin-1 , DE

    -- G = h = xʲ⁺¹ e^{−x}, k = (j+1) xʲ e^{−x}
    xjE : Fin M → ∀ j → Deriv M (X.hh (suc j)) (X.hh (suc j)) (X.kh j)
    xjE fM j = DFresp {G = λ x → pw (suc j) x * E x} {h = λ x → 0# * E x + pw (suc j) x * E x}
      {k = λ x → dpw (suc j) x * E x + pw (suc j) x * 0#} {G′ = X.hh (suc j)} {h′ = X.hh (suc j)} {k′ = X.kh j}
      (λ _ → refl) (λ x → trans (+-cong (zeroˡ _) refl) (+-identityˡ _))
      (λ x → trans (+-cong refl (zeroʳ _)) (trans (+-identityʳ _) (sym (X.kk j x))))
      (DFprod (pwD fM (suc j)) DFE)
