{-# OPTIONS --safe --without-K #-}

-- Translation of the whole real line `RQ = WQ +Q WQ` by a finite t ≥ 0, and translation invariance of `lebR`
-- (plan 03, "Translation and products").
--   * `shiftRH t : RQ ⇒ RQ`, x ↦ x + t: `inl x ↦ inl (x + t)`; `inr x ↦ inl (t ∸ x)` if x ≤ t, else `inr (x ∸ t)`
--     (`shift-inl`, `shift-inr-le`, `shift-inr-gt`; the case split is excluded middle);
--   * `∫-reflIv : ∫_{[0,t)} h(t ∸ x) dx ≈ ∫_{[0,t)} h` (reflection of an interval);
--   * `∫-shiftR : ∫ h(x + t) dx ≈ ∫ h` over the real line, and `shiftNegRH t = refl ∘ shift t ∘ refl` (x ↦ x − t) with
--     `∫-shiftNegR`.
-- Route for `shiftRH`: on a random element of RQ (glued from `inl ∘ α` and `inr ∘ β` pieces, `Colimits`), split the
-- `inr` pieces along the Borel set {r | β r ≤ t} (`LipTestAlg.le-borel`) and glue `inl ∘ rsubH t ∘ β` and
-- `inr ∘ subH t ∘ β` (`Monus`).  `∫-shiftR`: by `RealLine.∫ᴹ-lebR` the left side is
-- ∫ h(inl (x + t)) + ∫_{[0,t)} h(inl (t ∸ x)) + ∫_{[t,∞)} h(inr (x ∸ t)); the first two give ∫ h∘inl by `∫-reflIv` and
-- `LebesgueShift.∫-shift`, the last gives ∫ h∘inr by `∫-shift` (the point x = t is null).  `∫-reflIv`: the reflected
-- measure has the interval masses of Lebesgue measure on [0,t) (`LebesgueInterval.leb-unique`), or any other route.
--   Skeleton: holes first.
module QBS.Continuous.RealShift where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.Monus using (module Monus)

module RealShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (χIv)
  open RealLine lem₁ using (RQ; lebR)
  open RealScale lem₁ using (reflRH)
  open Monus lem₁ using (monus; rsubH)
  open QBS
  open Hom

  -- equality of points of RQ
  infix 4 _≈ᴿ_
  _≈ᴿ_ : ∣ RQ ∣ → ∣ RQ ∣ → Set _
  _≈ᴿ_ = _≈ˣ_ RQ

  module _ (t : ∣A∣) (bt : Bnd t) where

    -- x ↦ x + t
    shiftRH : Hom S RQ RQ
    shiftRH = ?

    shift-inl : ∀ x → map shiftRH ⟨$⟩ inj₁ x ≈ᴿ inj₁ (x + t)
    shift-inl = ?

    shift-inr-le : ∀ x → x ≤ t → map shiftRH ⟨$⟩ inj₂ x ≈ᴿ inj₁ (monus t x)
    shift-inr-le = ?

    shift-inr-gt : ∀ x → (x ≤ t → ⊥) → map shiftRH ⟨$⟩ inj₂ x ≈ᴿ inj₂ (monus x t)
    shift-inr-gt = ?

    -- reflection of [0, t)
    ∫-reflIv : ∀ (h : Hom S WQ WQ) →
      ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (_∘H_ S h (rsubH t))) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
    ∫-reflIv = ?

    ∫-shiftR : ∀ (h : Hom S RQ WQ) → ∫ᴹ {RQ} lebR (_∘H_ S h shiftRH) ≈ ∫ᴹ {RQ} lebR h
    ∫-shiftR = ?

    -- x ↦ x − t
    shiftNegRH : Hom S RQ RQ
    shiftNegRH = _∘H_ S reflRH (_∘H_ S shiftRH reflRH)

    ∫-shiftNegR : ∀ (h : Hom S RQ WQ) → ∫ᴹ {RQ} lebR (_∘H_ S h shiftNegRH) ≈ ∫ᴹ {RQ} lebR h
    ∫-shiftNegR = ?
