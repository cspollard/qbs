{-# OPTIONS --safe --without-K #-}

-- The Gaussian normaliser is finite: `Z = ∫₀^∞ e^{−x²/2} dλ ≤ 4` (its value `√(π/2) ≈ 1.25` is not used).
-- On the unit interval [n, n+1] the Gaussian is at most its left value Φ(n) (it is antitone), so the unit integral is
-- at most Φ(n) (`J-const`), and Φ(n) ≤ 2 ½ⁿ: for n = 0, 1 because Φ ≤ 1, and for n ≥ 2 because ½ n² ≥ n
-- (`Analysis/GaussTail.big`) gives `e^{−n²/2} ≤ e^{−n} ≤ ½ⁿ` (`TailFTCExpHalf.tail`).  Then
-- `Z = ∑ₙ ∫₀¹ Φ(n+u) du ≤ ∑ₙ 2 ½ⁿ ≤ 4`, since `∑ ½ⁿ = 1 + ∑ ½ⁿ⁺¹ ≤ 2`.
--   * `Z-le : Z ≤ (1 + 1) + (1 + 1)`;  `Z-bnd : Bnd Z` (bounded by the natural number 4).
module QBS.Continuous.GaussFinite where

open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussTail using (module AlgGT)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.CoinIndep using (module CoinIndep)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCExpHalf using (module TailFTCExpHalf)

module GaussFinite (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero; hp-double; ∑hp≤1)
  open AlgP A R using (*-mono₂)
  open AlgGT A R using (big; four)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-mono; ∑ᶠ-cong; ∑ᶠ-+; ∑ᶠ-shift)
  open Bounded A using (Bnd)
  open NegExp (lemOf lem₁) using (negExp-anti; negExp≤1)
  open Lebesgue (lemOf lem₁) using (J; J-mono)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open Meas (lemOf lem₁) using (Meas-const)
  open CoinIndep lem₁ using (fairCoin-prob)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open GaussHalfLine lem₁ using (Φ; phiH)
  open TailFTCExpHalf lem₁ using (tail)
  open QBS
  open Hom

  Φ-anti : ∀ {x y} → x ≤ y → Φ y ≤ Φ x
  Φ-anti xy = negExp-anti (*-mono half (*-mono₂ xy xy))

  -- Φ(n) ≤ 2 ½ⁿ
  cn : ∀ n → Φ (natE n) ≤ hp n + hp n
  cn zero = ≤-trans (negExp≤1 _) (≤-trans (≤-reflexive (sym hp-zero)) ≤-+ʳ)
  cn (suc zero) = ≤-trans (negExp≤1 _) (≤-reflexive (sym (trans (hp-double 0) hp-zero)))
  cn (suc (suc n)) = ≤-trans (negExp-anti (big (suc (suc n)) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))) (≤-trans (tail (suc (suc n))) ≤-+ʳ)

  -- the integral over [n, n+1]
  term : ∀ n → J fairCoin (λ r → map phiH ⟨$⟩ shiftPt n r) (Meas-hshift n phiH) ≤ hp n + hp n
  term n = ≤-trans (J-mono fairCoin (Meas-hshift n phiH) (Meas-const (Φ (natE n)))
      (λ r → Φ-anti (≤-+ʳ {natE n} {_})))
    (≤-trans (≤-reflexive (J-const fairCoin-prob (Φ (natE n)))) (cn n))

  sum-hp : ∑ᶠ hp ≤ 1# + 1#
  sum-hp = ≤-trans (≤-reflexive (∑ᶠ-shift hp)) (+-mono (≤-reflexive hp-zero) ∑hp≤1)

  Z-le : ∫ᴹ {WQ} lebPre phiH ≤ (1# + 1#) + (1# + 1#)
  Z-le = ≤-trans (≤-reflexive (∫ᴹ-leb phiH)) (≤-trans (∑ᶠ-mono term)
    (≤-trans (≤-reflexive (∑ᶠ-+ hp hp)) (+-mono sum-hp sum-hp)))

  Z-bnd : Bnd (∫ᴹ {WQ} lebPre phiH)
  Z-bnd = 4 , ≤-trans Z-le (≤-reflexive four)
