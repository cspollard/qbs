{-# OPTIONS --safe --without-K #-}

-- A certificate calculus for the tail FTC (part 5: the Gaussian), over an abstract Archimedean ω-semiring.
--   * `DFquad : Deriv M (½ x²) 0 x`, from the product rule on x · x and the scalar ½ (`half-twice`);
--   * with the exponential facts of `Analysis/DerivChain` (`module Gx`), `Φ x = E (½ x²)`:
--       `DFgauss  : Deriv M Φ (x¹ Φ) 0`            (Φ′ = −x Φ),
--       `DFgaussJ : ∀ j → Deriv M (xʲ⁺¹ Φ) (xʲ⁺² Φ) ((j+1) xʲ Φ)`   ((xʲ⁺¹Φ)′ = (j+1) xʲ Φ − xʲ⁺² Φ),
--     the second from the product rule on xʲ⁺¹ · Φ.  They are stated with `pw` of `Analysis/PolyExpCert`, the form of the
--     tests `gMomH` of `Continuous/GaussHalfLine`.
module QBS.Analysis.DerivGauss where

import Level as L
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivProd using (module AlgDP)
open import QBS.Analysis.DerivChain using (module AlgDX)
open import QBS.Analysis.DerivExp using (module AlgDE)
open import QBS.Analysis.Exp using (module Exp)

module AlgDG (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half+half; half-twice)
  open AlgT A R using (P)
  open AlgP A R using (pw; dpw; dpw-eq)
  open Exp A using (natE)
  open AlgDE A R using (pwD)
  open AlgD A R
  open AlgDP A R using (DFprod)
  open AlgDX A R using (module Chain)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  Fin-half : Fin half
  Fin-half = 0 , ≤-trans ≤-+ʳ (≤-reflexive half+half)

  -- (½ x²)′ = x
  DFquad : ∀ {M} → Fin M → Deriv M (λ x → half * (x * x)) (λ _ → 0#) (λ x → x)
  DFquad {M} fM = DFresp {G = λ x → half * (x * x)} {h = λ x → half * (0# * x + x * 0#)}
    {k = λ x → half * (1# * x + x * 1#)} {G′ = λ x → half * (x * x)} {h′ = λ _ → 0#} {k′ = λ x → x}
    (λ _ → refl) (λ x → trans (*-cong refl (trans (+-cong (zeroˡ x) (zeroʳ x)) (+-identityˡ 0#))) (zeroʳ half))
    (λ x → trans (*-cong refl (+-cong (*-identityˡ x) (*-identityʳ x))) (half-twice x))
    (DFscale half Fin-half (DFprod (DFid fM) (DFid fM)))

  module Gx (E : ∣A∣ → ∣A∣) (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ s {x y} → x ≤ P s → y ≤ P s → x + y ≤ P s → E (x + y) ≈ E x * E y)
    (E-b : ∀ s {t} → t ≤ P s → E t + t * E t ≤ 1#) (E-c : ∀ s {t} → t ≤ P s → 1# ≤ E t + t) where
    module C = Chain E E≤1 E-anti E-add E-b E-c

    Φ : ∣A∣ → ∣A∣
    Φ x = E (half * (x * x))

    DFgauss : ∀ {M} → Fin M → Deriv M Φ (λ x → pw 1 x * Φ x) (λ _ → 0#)
    DFgauss {M} fM = DFresp {G = λ x → E (half * (x * x))} {h = λ x → E (half * (x * x)) * x}
      {k = λ x → E (half * (x * x)) * 0#} {G′ = Φ} {h′ = λ x → pw 1 x * Φ x} {k′ = λ _ → 0#}
      (λ _ → refl) (λ x → trans (*-comm _ _) (*-cong (sym (*-identityʳ x)) refl)) (λ x → zeroʳ _)
      (C.DFexp {M} {λ x → half * (x * x)} {λ _ → 0#} {λ x → x} (DFquad fM))

    -- all the powers: `(xʲ⁺¹ Φ)′ = (j+1) xʲ Φ − xʲ⁺² Φ`, by the product rule on xʲ⁺¹ · Φ (j = 0 is `(xΦ)′ = Φ − x² Φ`)
    DFgaussJ : ∀ {M} → Fin M → ∀ j → Deriv M (λ x → pw (suc j) x * Φ x) (λ x → pw (suc (suc j)) x * Φ x)
      (λ x → natE (suc j) * (pw j x * Φ x))
    DFgaussJ {M} fM j = DFresp {G = λ x → pw (suc j) x * Φ x}
      {h = λ x → 0# * Φ x + pw (suc j) x * (pw 1 x * Φ x)} {k = λ x → dpw (suc j) x * Φ x + pw (suc j) x * 0#}
      {G′ = λ x → pw (suc j) x * Φ x} {h′ = λ x → pw (suc (suc j)) x * Φ x} {k′ = λ x → natE (suc j) * (pw j x * Φ x)}
      (λ _ → refl)
      (λ x → solve 3 (λ p′ x′ f′ → con 0 :* f′ :+ p′ :* ((x′ :* con 1) :* f′) := (x′ :* p′) :* f′) refl (pw (suc j) x) x (Φ x))
      (λ x → trans (+-cong refl (zeroʳ _)) (trans (+-identityʳ _)
        (trans (*-cong (dpw-eq j x) refl) (*-assoc (natE (suc j)) (pw j x) (Φ x)))))
      (DFprod (pwD fM (suc j)) (DFgauss fM))
