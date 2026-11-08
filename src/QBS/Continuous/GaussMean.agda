{-# OPTIONS --safe --without-K #-}

-- Gaussian first moment on the half-line: `∫₀^∞ x e^{−x²/2} dx = 1` (no π, no abstract normaliser).
-- With `G = φ = e^{−x²/2}`, `h = x φ` and `k = 0` (the zero test `kzH`, written `0 · φ` so that its integral is `0 · ∫ φ`),
-- `dv1 n` is the `Deriv` certificate `G′ = k − h` on `[0, n+1]` from `DerivGauss.DFgauss` (the chain rule applied to `½ x²`).
-- Since `G 0 = 1` and `φ(N) → 0` along the integers N ≥ 2 (`Φtail`: φ(N) ≤ e^{−N}, `Analysis/GaussExp.AlgGT.big`, and
-- `Continuous/HalfLineMomentFact.T.tail` at j = 0), `DerivBridge.OnHalfLine.glue-D0` gives
--   `∫-xφ : ∫ᴹ lebPre (gMomH 1) ≈ 1`.
-- (This replaces a hand-written telescoping sum over the unit-interval identities of the retired `GaussCertM1` pack.)
module QBS.Continuous.GaussMean where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussExp using (module AlgGT)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivGauss using (module AlgDG)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.DerivBridge using (module DerivBridge)

module GaussMean (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; arch; hp)
  open AlgP A R using (pw; natE≤P)
  open AlgGT A R using (big)
  open Exp A using (natE)
  open Series A using (∑ᶠ-zero)
  open AlgD A R using (Deriv; Fin; DFresp)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; negExp-anti; negExp-zero; negExp-cong)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineMomentFact lem₁ using (module T)
  open GaussHalfLine lem₁ using (Φ; Φ-cong; gh; gh-cong; gMomH; Ea; Eb; Ec)
  open AlgDG A R using (module Gx)
  open Gx negExp negExp≤1 negExp-anti Ea Eb Ec using (DFgauss)
  open DerivBridge lem₁ using (module OnHalfLine)
  open QBS
  open Hom

  -- the zero test, written `x ↦ 0 · e^{−x²/2}` so that its integral is `0 · ∫ e^{−x²/2}`
  kz : ∣A∣ → ∣A∣
  kz x = 0# * gh 0 x

  kz-cong : ∀ {x y} → x ≈ y → kz x ≈ kz y
  kz-cong e = *-cong refl (gh-cong 0 e)

  kzH : Hom S WQ WQ
  kzH = record
    { map = record { to = kz ; cong = kz-cong }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → 0#} {λ r → gh 0 (γ ⟨$⟩ r)} (Meas-const 0#)
        (map-random (gMomH 0) {γ} m) }

  -- the unit integrals of the zero test
  b : ℕ → ∣A∣
  b n = J fairCoin (λ r → map kzH ⟨$⟩ shiftPt n r) (Meas-hshift n kzH)

  b0 : ∀ n → b n ≈ 0#
  b0 n = trans (J-irrel fairCoin (Meas-hshift n kzH)
      (Meas-⊗ {λ _ → 0#} {λ r → map (gMomH 0) ⟨$⟩ shiftPt n r} (Meas-const 0#) (Meas-hshift n (gMomH 0))))
    (trans (J-scale fairCoin 0# {λ r → map (gMomH 0) ⟨$⟩ shiftPt n r} (Meas-hshift n (gMomH 0)))
      (zeroˡ _))

  Φ0 : Φ 0# ≈ 1#
  Φ0 = trans (negExp-cong (trans (*-cong refl (zeroˡ 0#)) (zeroʳ half))) negExp-zero

  ∫kz : ∫ᴹ {WQ} lebPre kzH ≈ 0#
  ∫kz = trans (∫ᴹ-leb kzH) (∑ᶠ-zero b0)

  -- φ(N) → 0 along the integers N ≥ N₀ (φ(N) ≤ e^{−N})
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

  -- the data on [0, n+1] for G = φ, h = x φ, k = 0, from the rules of `Analysis/Deriv*` (`DFgauss`)
  fin : ∀ n → Fin (natE (suc n))
  fin n = suc n , natE≤P (suc n)

  dv1 : ∀ n → Deriv (natE (suc n)) Φ (λ x → map (gMomH 1) ⟨$⟩ x) (λ x → map kzH ⟨$⟩ x)
  dv1 n = DFresp {G = Φ} {h = λ x → gh 1 x} {k = λ _ → 0#} {G′ = Φ} {h′ = λ x → map (gMomH 1) ⟨$⟩ x}
    {k′ = λ x → map kzH ⟨$⟩ x} (λ _ → refl) (λ _ → refl) (λ x → sym (zeroˡ (gh 0 x))) (DFgauss (fin n))

  -- ∫₀^∞ x e^{−x²/2} dx = 1  (`G 0 = 1`, so `glue-D0`)
  ∫-xφ : ∫ᴹ {WQ} lebPre (gMomH 1) ≈ 1#
  ∫-xφ = trans (OnHalfLine.glue-D0 (gMomH 1) kzH Φ dv1 Φtail) (trans (+-cong Φ0 ∫kz) (+-identityʳ 1#))
