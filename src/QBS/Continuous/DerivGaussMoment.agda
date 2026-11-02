{-# OPTIONS --safe --without-K #-}

-- Validation of the chain rule (`Analysis/DerivChain`, `Analysis/DerivGauss`): the Gaussian first and second moments on the
-- half-line from `Deriv` data built by the rules, through `DerivBridge.OnHalfLine.glue-D0`.
--   * `∫-xφ : ∫₀^∞ x e^{−x²/2} ≈ 1`:  G = φ, h = x φ, k = 0 (`DFgauss`), `G 0 = 1`, `φ(N) → 0`; the statement of
--     `Continuous/GaussMean.∫-xφ`, which needed `Analysis/GaussCertM1` and a hand-written telescoping sum;
--   * `∫-x²φ : ∫₀^∞ x² e^{−x²/2} ≈ Z`, `Z = ∫₀^∞ e^{−x²/2}` (as in `Continuous/GaussMoment`): G = xφ, h = x²φ, k = φ
--     (`DFgauss1`, the product rule on x · φ), `G 0 = 0`, `xφ(N) → 0`.
-- The exponential facts at every bound `P s` are those of `Continuous/GaussHalfLine` (stated at `P (bd s)`), and the measurability
-- is that of the tests `gMomH`, `kzH`, `phiH`.
module QBS.Continuous.DerivGaussMoment where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussTail using (module AlgGT)
open import QBS.Analysis.GaussExp using (bd)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivGauss using (module AlgDG)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMeanUnit using (module GaussMeanUnit)
open import QBS.Continuous.GaussMean using (module GaussMean)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.DerivBridge using (module DerivBridge)

module DerivGaussMoment (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgT A R using (P)
  open AlgP A R using (pw; natE≤P; P-mono)
  open AlgGT A R using (big)
  open Exp A using (natE)
  open Series A using (∑ᶠ-zero)
  open AlgD A R using (Deriv; Fin; DFresp)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; negExp-anti)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; ∫ᴹ-leb)
  open HalfLineMomentFact lem₁ using (module T)
  open GaussHalfLine lem₁ using (Φ; gh; gMomH; E-add; E-b; E-c)
  open GaussMeanUnit lem₁ using (kz; kzH)
  open GaussMean lem₁ using (b0; Φ0)
  open GaussMoment lem₁ using (Z; G0; gtail; ∫-gMom0)
  open DerivBridge lem₁ using (module OnHalfLine)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the exponential facts at every bound P s

  s≤bd : ∀ s → s ℕ.≤ bd s
  s≤bd s = ℕ.≤-trans (ℕ.m≤m+n s s) (ℕ.n≤1+n (s ℕ.+ s))

  Ea : ∀ s {x y} → x ≤ P s → y ≤ P s → x + y ≤ P s → negExp (x + y) ≈ negExp x * negExp y
  Ea s xb yb xyb = E-add s (≤-trans xb (P-mono (s≤bd s))) (≤-trans yb (P-mono (s≤bd s))) (≤-trans xyb (P-mono (s≤bd s)))

  Eb : ∀ s {t} → t ≤ P s → negExp t + t * negExp t ≤ 1#
  Eb s tb = E-b s (≤-trans tb (P-mono (s≤bd s)))

  Ec : ∀ s {t} → t ≤ P s → 1# ≤ negExp t + t
  Ec s _ = E-c

  open AlgDG A R using (module Gx)
  open Gx negExp negExp≤1 negExp-anti Ea Eb Ec using (DFgauss; DFgauss1)

  fin : ∀ n → Fin (natE (suc n))
  fin n = suc n , natE≤P (suc n)

  ----------------------------------------------------------------------------
  -- φ(N) → 0 along the integers N ≥ N₀

  Φtail : ∀ m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × Φ (natE N) ≤ hp m)
  Φtail m N₀ = N , ℕ.≤-trans (ℕ.m≤m+n N₀ 2) le , ≤-trans (negExp-anti (big N (ℕ.≤-trans (ℕ.m≤n+m 2 N₀) le)))
    (≤-trans (≤-reflexive (sym (*-identityˡ _))) bnd)
    where
    t = T.tail 0 m (N₀ ℕ.+ 2)
    N : ℕ
    N = proj₁ t
    le : N₀ ℕ.+ 2 ℕ.≤ N
    le = proj₁ (proj₂ t)
    bnd : pw 0 (natE N) * negExp (natE N) ≤ hp m
    bnd = proj₂ (proj₂ t)

  ----------------------------------------------------------------------------
  -- ∫₀^∞ x e^{−x²/2} = 1

  dv1 : ∀ n → Deriv (natE (suc n)) Φ (λ x → map (gMomH 1) ⟨$⟩ x) (λ x → map kzH ⟨$⟩ x)
  dv1 n = DFresp {G = Φ} {h = λ x → gh 1 x} {k = λ _ → 0#} {G′ = Φ} {h′ = λ x → map (gMomH 1) ⟨$⟩ x}
    {k′ = λ x → map kzH ⟨$⟩ x} (λ _ → refl) (λ _ → refl) (λ x → sym (zeroˡ (gh 0 x))) (DFgauss (fin n))

  ∫kz : ∫ᴹ {WQ} lebPre kzH ≈ 0#
  ∫kz = trans (∫ᴹ-leb kzH) (∑ᶠ-zero b0)

  ∫-xφ : ∫ᴹ {WQ} lebPre (gMomH 1) ≈ 1#
  ∫-xφ = trans (OnHalfLine.glue-D0 (gMomH 1) kzH Φ dv1 Φtail) (trans (+-cong Φ0 ∫kz) (+-identityʳ 1#))

  ----------------------------------------------------------------------------
  -- ∫₀^∞ x² e^{−x²/2} = Z

  dv2 : ∀ n → Deriv (natE (suc n)) (gh 1) (λ x → map (gMomH 2) ⟨$⟩ x) (λ x → map (gMomH 0) ⟨$⟩ x)
  dv2 n = DFgauss1 (fin n)

  ∫-x²φ : ∫ᴹ {WQ} lebPre (gMomH 2) ≈ Z
  ∫-x²φ = trans (OnHalfLine.glue-D0 (gMomH 2) (gMomH 0) (gh 1) dv2 (gtail 0))
    (trans (+-cong (G0 0) ∫-gMom0) (+-identityˡ Z))
