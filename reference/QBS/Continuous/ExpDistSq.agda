{-# OPTIONS --safe --without-K #-}

-- The second moment of the exponential distribution: `∫ x² d(expDist) ≈ 1# + 1#` (that is, `E[X²] = 2`), for the squaring
-- statistic `sqW : x ↦ x·x`, from `HalfLineMomentFact.∫-x²` through the density formula `ExpDist.∫-expDist`.
-- Together with the mean `∫-expDist-id ≈ 1#` this gives `Var X = E[X²] − (E X)² = 1` (see `Inference/ExpDistVar`).
module QBS.Continuous.ExpDistSq where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.ExpDist using (module ExpDist)

module ExpDistSq (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; _+_; 1#; trans; *-cong; *-comm)
  open Meas (lemOf lem₁) using (Meas-⊗)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineMomentFact lem₁ using (x²NegExpH; ∫-x²)
  open ExpDist lem₁ using (expDist; ∫-expDist)
  open QBS
  open Hom

  -- the squaring statistic
  sqW : Hom S WQ WQ
  sqW = record
    { map = record { to = λ x → x * x ; cong = λ e → *-cong e e }
    ; map-random = λ {γ} m → Meas-⊗ {γ ⟨$⟩_} {γ ⟨$⟩_} m m }

  -- the second moment: `∫ x² e^{−x} dx = 2`
  ∫-expDist-sq : ∫ᴹ {WQ} (ιPre {WQ} expDist) sqW ≈ 1# + 1#
  ∫-expDist-sq = trans (∫-expDist sqW)
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH sqW} {x²NegExpH} (λ x → *-comm _ _)) ∫-x²)
