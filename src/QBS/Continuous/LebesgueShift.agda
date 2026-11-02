{-# OPTIONS --safe --without-K #-}

-- Translation of Lebesgue measure on [0,∞) by every finite cut (plan 03, "Uniqueness on the half-line").  Skeleton: holes
-- first.  With `shiftH t` the map x ↦ x + t, for every test h,
--   `∫-shift : ∫ h(x + t) dx + ∫_{[0,t)} h dx ≈ ∫ h dx`.
-- Route: `shiftedLeb t`, the measure h ↦ ∫ h(x + t) dx + ∫_{[0,t)} h dx, gives [a,b) the mass b − a (`shifted-Iv`: the
-- first part is λ([a,b) ∩ [t,∞)) translated, the second λ([a,b) ∩ [0,t))), and nothing to ∞, so it is Lebesgue measure
-- (`LebesgueInterval.leb-unique`).  Integer t is `HalfLine.shiftPre`.
module QBS.Continuous.LebesgueShift where

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
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Inference.Domination using (module Domination)

module LebesgueShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open ExpDist lem₁ using (idW)
  open Domination lem₁ using (addH)
  open Intervals (lemOf lem₁) using (χIv)
  open QBS
  open Hom

  -- x ↦ x + t
  shiftH : ∣A∣ → Hom S WQ WQ
  shiftH t = addH idW (constW {WQ} t)

  -- the measure h ↦ ∫ h(x + t) dx + ∫_{[0,t)} h dx
  shiftedLeb : ∣A∣ → Pre (XW WQ)
  shiftedLeb = ?

  ∫ᴹ-shiftedLeb : ∀ t (h : Hom S WQ WQ) →
    ∫ᴹ {WQ} (shiftedLeb t) h ≈ ∫ᴹ {WQ} lebPre (_∘H_ S h (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
  ∫ᴹ-shiftedLeb = ?

  shifted-Iv : ∀ t → Bnd t → ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} (shiftedLeb t) (χIv a b) ≈ b
  shifted-Iv = ?

  ∫-shift : ∀ t → Bnd t → ∀ (h : Hom S WQ WQ) →
    ∫ᴹ {WQ} lebPre (_∘H_ S h (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h) ≈ ∫ᴹ {WQ} lebPre h
  ∫-shift = ?
