{-# OPTIONS --safe --without-K #-}

-- Pointwise facts for `InfoProduct` (plan 03, "Information quantities", helper).  For positive finite x, y:
--   * `log-mul-pt` : log⁺(xy) + (log⁻ x + log⁻ y) ≈ (log⁺ x + log⁺ y) + log⁻(xy);
--   * `logN-sub` : log⁻(xy) ≤ log⁻ x + log⁻ y, and `logP-sub` : log⁺(xy) ≤ log⁺ x + log⁺ y.
-- Route: `log-mul-pt` is the cross-added `SignedLog.log-mul` with witness 0; `logN-sub`, `logP-sub` by `cut-total (xy) 1`:
-- on one side the other part of xy vanishes (`logP-le`, `logN-ge`) and the identity bounds the remaining one.
module QBS.Continuous.InfoProductAux where

open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (case_of_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.LowerReals using (oneC)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.MonusAlg using (module MonusAlg)

module InfoProductAux (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; distribˡ; +-comm;
    +-identityˡ; +-identityʳ; ≤-trans; ≤-reflexive; ≤-+ʳ; 0-least)
  open MonusAlg lem₁ using (cut-total)
  open SignedLog lem₁ using (PosQ; logP; logN; logP-le; logN-ge; log-mul; PosQ-mul; BndQ-mul)
  open import QBS.Analysis.SignedOmega using (module Bounded)
  open Bounded A using (_≃_)
  open _≃_

  module _ (x y : _) (px : PosQ x) (py : PosQ y) (bx : BndQ x) (by : BndQ y) where

    log-mul-pt : logP (x * y) + (logN x + logN y) ≈ (logP x + logP y) + logN (x * y)
    log-mul-pt = trans (sym (+-identityʳ _)) (trans (eq (log-mul x y px py bx by)) (+-identityʳ _))

    logN-sub : logN (x * y) ≤ logN x + logN y
    logN-sub = case cut-total (x * y) oneC of λ
      { (inj₁ xy1) → ≤-trans (≤-trans (≤-+ʳ {logN (x * y)} {logP x + logP y}) (≤-reflexive (+-comm _ _)))
          (≤-reflexive (trans (sym log-mul-pt) (trans (+-cong (logP-le (x * y) xy1) refl) (+-identityˡ _))))
      ; (inj₂ 1xy) → ≤-trans (≤-reflexive (logN-ge (x * y) 1xy)) 0-least }

    logP-sub : logP (x * y) ≤ logP x + logP y
    logP-sub = case cut-total (x * y) oneC of λ
      { (inj₁ xy1) → ≤-trans (≤-reflexive (logP-le (x * y) xy1)) 0-least
      ; (inj₂ 1xy) → ≤-trans (≤-+ʳ {logP (x * y)} {logN x + logN y})
          (≤-reflexive (trans log-mul-pt (trans (+-cong refl (logN-ge (x * y) 1xy)) (+-identityʳ _)))) }

  -- multiplying the identity by w
  mul-id : ∀ w a b c d e f → a + (b + c) ≈ (d + e) + f → w * a + (w * b + w * c) ≈ (w * d + w * e) + w * f
  mul-id w a b c d e f q = trans (sym (+-cong refl (distribˡ w b c))) (trans (sym (distribˡ w a (b + c)))
    (trans (*-cong refl q) (trans (distribˡ w (d + e) f) (+-cong (distribˡ w d e) refl))))
