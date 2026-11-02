{-# OPTIONS --safe --without-K #-}

-- Normalisation of the exponential density: `∫₀^∞ e^{−x} dλ(x) = 1`, multiplied out (there is no
-- subtraction): with `g = e^{−1}` and `I = ∫₀¹ e^{−u} du`,
--   * `negExp-pw : e^{−n} = gⁿ`;
--   * `norm-from : I + g ≈ 1 → ∫ e^{−x} dλ ≈ 1`, the geometric sum `(∑ gⁿ) I = 1` of `Analysis/GeometricNorm`
--     (its hypothesis `gᴺ (N+1) ≤ 1` is `e^{−N} e^{N} = 1` with `1 + N ≤ e^N`);
--   * `∫ᴹ-leb-negExp-norm : ∫ e^{−x} dλ ≈ 1`, with `I + g ≈ 1` from `Continuous/HalfLineUnit`.
module QBS.Continuous.HalfLineNorm where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.GeometricNorm using (module GeometricNorm)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineUnit using (module HalfLineUnit)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)

module HalfLineNorm (lem₁ : LEM₁) where
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH; negExp-add; I-negExp; ∫ᴹ-leb-negExp-split)
  open Lebesgue (lemOf lem₁) using (A)
  open import QBS.Analysis.Omega using (module OmegaSemiring)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; 0#; refl; sym; trans; *-cong; *-comm; +-comm; ≤-trans; ≤-reflexive;
    ≤-refl; +-identityˡ; *-mono; ≤-antisym)
  open Exp A using (natE; pw)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp-zero; negExp-expC-nat)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  R = lowerRealsArch (lemOf lem₁)
  open GeometricNorm A R
  open HalfLineUnit lem₁ using (I-negExp-unit)

  g : _
  g = negExp 1#

  -- `e^{−n} = gⁿ`
  negExp-pw : ∀ n → negExp (natE n) ≈ pw g n
  negExp-pw ℕ.zero = negExp-zero
  negExp-pw (ℕ.suc n) = trans (negExp-add {natE n} {1#} {n} {1} {ℕ.suc n} ≤-refl (≤-reflexive (sym (+-identityˡ 1#))) ≤-refl)
    (trans (*-comm _ _) (*-cong refl (negExp-pw n)))

  -- `gᴺ (N+1) ≤ 1`
  gb : ∀ N → pw g N * natE (ℕ.suc N) ≤ 1#
  gb N = ≤-trans (≤-reflexive (*-cong (sym (negExp-pw N)) refl))
    (≤-trans (*-mono (negExp (natE N)) (≤-trans (≤-reflexive (+-comm (natE N) 1#)) (1+≤expC (lemOf lem₁) (natE N))))
      (≤-reflexive (negExp-expC-nat (natE N) N ≤-refl)))

  norm-from : I-negExp + g ≈ 1# → ∫ᴹ {WQ} lebPre negExpH ≈ 1#
  norm-from h = trans ∫ᴹ-leb-negExp-split
    (trans (∑ᶠ-cong (λ n → trans (*-cong (negExp-pw n) refl) (*-comm _ _)))
      (trans (sym (∑ᶠ-scale I-negExp (pw g)))
        (trans (*-comm _ _) (Geo.total g I-negExp h gb))))

  -- `∫₀^∞ e^{−x} dx = 1`
  ∫ᴹ-leb-negExp-norm : ∫ᴹ {WQ} lebPre negExpH ≈ 1#
  ∫ᴹ-leb-negExp-norm = norm-from I-negExp-unit
