{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure on the plane ℝ × ℝ (plan 03, "Translation and products").
--   * `leb2 = lebR ⊗ lebR` (`Product.prodPre`), with iterated integrals in both orders (`∫-leb2`, `∫-leb2′`);
--   * `∫-leb2-rect`: ∫ g(x) h(y) d(x, y) ≈ ∫ g · ∫ h;
--   * `area`: the rectangle [a, b) × [c, d) in the positive quadrant has area x y, where a + x ≈ b and c + y ≈ d;
--   * `∫-swap`: leb2 is invariant under (x, y) ↦ (y, x).
-- Route: specialise `Product`; `area` from `∫-leb2-rect`, `RealLine.∫ᴹ-lebR` and `LebesgueInterval.leb-Iv` (cancel a
-- and c with `BoundedCancel.cancel-bnd`); `∫-swap` from `∫-leb2` and `∫-leb2′` (the inner integrals agree pointwise).
--   Skeleton: holes first.
module QBS.Continuous.LebPlane where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.Product using (module Product)

module LebPlane (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open SFiniteCommute (lemOf lem₁) using (fixH₂)
  open SFiniteStrong (lemOf lem₁) using (fixH)
  open Intervals (lemOf lem₁) using (χIv)
  open RealLine lem₁ using (RQ; lebR; copairH)
  open Product (lemOf lem₁) using (prodPre; intL; intR)
  open QBS
  open Hom

  R2 : QBS S
  R2 = _×Q_ S RQ RQ

  leb2 : C.Pre (XW R2)
  leb2 = prodPre {RQ} {RQ} lebR lebR

  -- iterated integrals
  ∫-leb2 : ∀ (g : Hom S R2 WQ) → ∫ᴹ {R2} leb2 g ≈ ∫ᴹ {RQ} lebR (intL {RQ} {RQ} lebR g)
  ∫-leb2 = ?

  ∫-leb2′ : ∀ (g : Hom S R2 WQ) → ∫ᴹ {R2} leb2 g ≈ ∫ᴹ {RQ} lebR (intR {RQ} {RQ} lebR g)
  ∫-leb2′ = ?

  ∫-leb2-rect : ∀ (g h : Hom S RQ WQ) →
    ∫ᴹ {R2} leb2 (mulH {R2} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S))) ≈ ∫ᴹ {RQ} lebR g * ∫ᴹ {RQ} lebR h
  ∫-leb2-rect = ?

  -- [a, b) × [c, d) in the positive quadrant
  rectH : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Hom S R2 WQ
  rectH a b c d = mulH {R2} (_∘H_ S (copairH (χIv a b) (constW 0#)) (fstQ S))
                            (_∘H_ S (copairH (χIv c d) (constW 0#)) (sndQ S))

  area : ∀ a b c d x y → Bnd a → Bnd b → Bnd c → Bnd d → a + x ≈ b → c + y ≈ d →
    ∫ᴹ {R2} leb2 (rectH a b c d) ≈ x * y
  area = ?

  -- (x, y) ↦ (y, x)
  swapH : Hom S R2 R2
  swapH = pairQ S {R2} {RQ} {RQ} (sndQ S) (fstQ S)

  ∫-swap : ∀ (g : Hom S R2 WQ) → ∫ᴹ {R2} leb2 (_∘H_ S g swapH) ≈ ∫ᴹ {R2} leb2 g
  ∫-swap = ?
