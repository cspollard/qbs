{-# OPTIONS --safe --without-K #-}

-- Scaling of Lebesgue measure on [0,∞) by every finite positive constant (plan 03, "Uniqueness on the half-line").
-- Skeleton: holes first.  For c with an inverse c′ (both finite) and every test h,
--   `∫-scale : c · ∫ h(cx) dx ≈ ∫ h dx`.
-- Route: `scaledLeb c`, the measure h ↦ c · ∫ h(cx) dx, gives [a,b) the mass c · (b c′ − a c′) = b − a
-- (`scaled-Iv`, from `LebesgueInterval.leb-Iv` at the endpoints a c′, b c′), and nothing to ∞, so it is Lebesgue measure
-- (`LebesgueInterval.leb-unique`).  This generalises the dyadic `Continuous/HalfLineScale`.
module QBS.Continuous.LebesgueScale where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)

module LebesgueScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open C using (Pre)
  open HalfLine lem₁ using (lebPre)
  open HalfLineRate lem₁ using (scaleH)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χIv)
  open QBS
  open Hom

  -- the measure h ↦ c · ∫ h(cx) dx
  scaledLeb : ∣A∣ → Pre (XW WQ)
  scaledLeb = ?

  ∫ᴹ-scaledLeb : ∀ c (h : Hom S WQ WQ) → ∫ᴹ {WQ} (scaledLeb c) h ≈ c * ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH c idW))
  ∫ᴹ-scaledLeb = ?

  scaled-Iv : ∀ c c′ → c * c′ ≈ 1# → Bnd c → Bnd c′ → ∀ a b → a ≤ b → Bnd b →
    a + ∫ᴹ {WQ} (scaledLeb c) (χIv a b) ≈ b
  scaled-Iv = ?

  ∫-scale : ∀ c c′ → c * c′ ≈ 1# → Bnd c → Bnd c′ → ∀ (h : Hom S WQ WQ) →
    c * ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH c idW)) ≈ ∫ᴹ {WQ} lebPre h
  ∫-scale = ?
