{-# OPTIONS --safe --without-K #-}

-- Rate 1 consistency: `ExpRateDist.expDistλ` at `l = c = 1#` agrees with the exponential distribution `ExpDist.expDist`.
--   * `expRate-one f : ∫ᴹ (ιPre expDistλ) f ≈ ∫ᴹ (ιPre expDist) f` for every non-negative test `f`, both being
--     `∫ lebPre (e^{−x} f)` (`DensityDist.∫-dens`, `ExpDist.∫-expDist`); the densities `1 · e^{−1·x}` and `e^{−x}` agree pointwise.
module QBS.Inference.ExpRateOne where

open import Data.Nat.Base using (zero; suc)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Inference.ExpRateDist using (module ExpRateDist)

module ExpRateOne (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A)
  open OmegaSemiring A using (_≈_; 1#; _*_; _+_; sym; trans; *-cong; *-identityˡ; +-identityˡ; ≤-reflexive)
  open Exp A using (natE)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineMomentN lem₁ using (negExp-cong)
  open ExpDist lem₁ using (expDist; ∫-expDist)
  open DensityDist lem₁ using (∫-dens)
  open ExpRateDist lem₁ using (module Dist)
  open import Function.Bundles using (_⟨$⟩_)
  open Hom

  open OmegaSemiring A using (_≤_)

  l≤ : 1# ≤ natE 1
  l≤ = ≤-reflexive (sym (+-identityˡ 1#))

  module D1 = Dist 1# 1# 0 0 (*-identityˡ 1#) l≤ l≤

  -- the densities agree pointwise against every test
  dens-eq : ∀ (f : Hom S WQ WQ) x → map (mulH {WQ} D1.d f) ⟨$⟩ x ≈ map (mulH {WQ} negExpH f) ⟨$⟩ x
  dens-eq f x = *-cong (trans (*-identityˡ _) (negExp-cong (*-identityˡ x))) (OmegaSemiring.refl A)

  expRate-one : ∀ (f : Hom S WQ WQ) → ∫ᴹ {WQ} (ιPre {WQ} D1.expDistλ) f ≈ ∫ᴹ {WQ} (ιPre {WQ} expDist) f
  expRate-one f = trans (∫-dens D1.d D1.expNrmλ f)
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} D1.d f} {mulH {WQ} negExpH f} (dens-eq f)) (sym (∫-expDist f)))
