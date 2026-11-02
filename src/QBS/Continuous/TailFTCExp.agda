{-# OPTIONS --safe --without-K #-}

-- Validation of `Continuous/TailFTC`: `∫₀¹ e^{−u} du + e^{−1} = 1` (as `HalfLineUnit.I-negExp-unit`), with h = G = e^{−·}.
-- The certificate on a dyadic piece [a, a + w], w = ½ⁿ, is pointwise exp algebra: with y = e^{−w}, e^{−(a+w)} = e^{−a} y
-- (`negExp-add`), and `y (1 + w) ≤ 1 ≤ y + w` (from y e^{w} = 1 and 1 + w ≤ e^{w} ≤ 1 + w + w², `AlgT.exp-facts`) give
--   e^{−a} y + w (e^{−a} y) ≤ e^{−a} ≤ e^{−a} y + w e^{−a}.
module QBS.Continuous.TailFTCExp where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineUnit using (module HalfLineUnit)

module TailFTCExp (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R; module Unit)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R
  open Integration A using (I; I-cong)
  open Exp A using (natE)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-expC-nat; negExp-zero)
  open Expansion A half hh using (expansion)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open FairCoin lem₁ using (fairCoin)
  open HalfLineNegExp lem₁ using (negExp-add; I-negExp; Meas-negExp-expansion)
  open HalfLineUnit lem₁ using (I-negExp≈F0; Fun-G)

  negExp-cong : ∀ {x y} → x ≈ y → negExp x ≈ negExp y
  negExp-cong e = negExp-anti (proj₂ e) , negExp-anti (proj₁ e)

  bd1 : ∀ {x} → x ≤ 1# → x ≤ natE 1
  bd1 h = ≤-trans h (≤-reflexive (sym (+-identityˡ 1#)))

  Fh = Meas→Fun {λ r → negExp (expansion r)} (λ r → negExp≤1 _) Meas-negExp-expansion

  -- the exponential facts at the width ½ⁿ
  facts : ∀ n → (negExp (hp n) + hp n * negExp (hp n) ≤ 1#) × (1# ≤ negExp (hp n) + hp n)
  facts n = exp-facts {negExp (hp n)} {hp n} {expC (lemOf lem₁) (hp n)} (negExp-expC-nat (hp n) 1 (bd1 (hp≤1 n)))
    (1+≤expC (lemOf lem₁) (hp n)) (expC≤quad (lemOf lem₁) (hp≤1 n))

  -- e^{−(a+w)} = e^{−a} e^{−w} on a dyadic piece
  add-at : ∀ {n a} → Dy n a → negExp (a + hp n) ≈ negExp a * negExp (hp n)
  add-at {n} {a} d = negExp-add {a} {hp n} {1} {1} {1} (bd1 (≤-trans ≤-+ʳ (dy-bound d))) (bd1 (hp≤1 n)) (bd1 (dy-bound d))

  cert-lo : ∀ {n a} → Dy n a → negExp (a + hp n) + hp n * negExp (a + hp n) ≤ negExp a
  cert-lo {n} {a} d = ≤-resp (+-cong (sym e) (*-cong refl (sym e))) refl
    (proj₁ (exp-cert {negExp a} {negExp (hp n)} {hp n} (proj₁ (facts n)) (proj₂ (facts n))))
    where e = add-at d

  cert-hi : ∀ {n a} → Dy n a → negExp a ≤ negExp (a + hp n) + hp n * negExp a
  cert-hi {n} {a} d = ≤-resp refl (+-cong (sym e) refl)
    (proj₂ (exp-cert {negExp a} {negExp (hp n)} {hp n} (proj₁ (facts n)) (proj₂ (facts n))))
    where e = add-at d

  h≤1′ : ∀ x → x ≤ 1# → negExp x ≤ 1#
  h≤1′ x _ = negExp≤1 x

  h-mono′ : ∀ {x y} → x ≤ y → y ≤ 1# → negExp y ≤ negExp x
  h-mono′ x≤y _ = negExp-anti x≤y

  G-bnd′ : ∀ {n a} → Dy n a → negExp a ≤ P 0
  G-bnd′ {n} {a} _ = negExp≤1 a

  open Unit negExp negExp 0 negExp-cong negExp-cong h≤1′ h-mono′ Fh G-bnd′ cert-lo cert-hi using (ftc-unit)

  -- ∫₀¹ e^{−u} du + e^{−1} = 1
  I-negExp-unit′ : I fairCoin (λ r → negExp (expansion r)) Fh + negExp 1# ≈ 1#
  I-negExp-unit′ = trans ftc-unit negExp-zero

  -- the same statement for `HalfLineNegExp.I-negExp` (the `J`-form of the integral), as `HalfLineUnit.I-negExp-unit`
  I-negExp-unit″ : I-negExp + negExp 1# ≈ 1#
  I-negExp-unit″ = trans (+-cong (trans I-negExp≈F0 (I-cong fairCoin (λ r → negExp-cong (*-identityˡ _)) (Fun-G 0) Fh)) refl)
    I-negExp-unit′
