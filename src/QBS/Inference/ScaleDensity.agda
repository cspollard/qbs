{-# OPTIONS --safe --without-K #-}

-- Pushforwards of density distributions under scaling, for every finite invertible scale (plan 03, "Change of variables").
-- For c, l finite with c l ≈ 1 and a normalised density g:
--   * `push-dens : ∫ (mapPre (x ↦ c x) (densDist g)) f ≈ ∫ (densDist (y ↦ l g(l y))) f`  for every test f; proof:
--     ∫ g(x) f(c x) dx = c ∫ l g(l c x) f(c x) dx = ∫ l g(l y) f(y) dy, which is `LebesgueScale.∫-scale` at c;
--   * Exp at every rate: `agree : ∫ (expPush c) f ≈ ∫ (densDist (λ e^{−λy})) f` (`Inference/ExpPushforward.Push`,
--     with l = λ), generalising `Inference/ExpPushforwardAgree` (c = ½), and `agree-dist`, the same against
--     `Inference/ExpRateDist.Dist.expDistλ`, so the moments of both forms are those of one measure.
--   Skeleton: holes first.
module QBS.Inference.ScaleDensity where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.LebesgueScale using (module LebesgueScale)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
open import QBS.Inference.ExpPushforward using (module ExpPushforward)
open import QBS.Inference.ExpRateDist using (module ExpRateDist)

module ScaleDensity (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineRate lem₁ using (negExpRH; scaleH)
  open DensityDist lem₁ using (densDist)
  open DensityExpectation lem₁ using (expNrm)
  open ExpDist lem₁ using (idW)
  open LebesgueScale lem₁ using (∫-scale)
  open ExpPushforward lem₁ using (module Push)
  open ExpRateDist lem₁ using (module Dist)
  open QBS
  open Hom

  module _ (c l : ∣A∣) (cl : c * l ≈ 1#) (cB : Bnd c) (lB : Bnd l) where

    sc : Hom S WQ WQ
    sc = scaleH c idW

    ----------------------------------------------------------------------------
    -- any density

    -- the density y ↦ l g(l y) of the scaled variable
    scD : Hom S WQ WQ → Hom S WQ WQ
    scD g = scaleH l (_∘H_ S g (scaleH l idW))

    -- l c ≈ 1, so l g(l (c x)) ≈ l g(x)
    scD-pt : ∀ (g : Hom S WQ WQ) x → map (scD g) ⟨$⟩ (map sc ⟨$⟩ x) ≈ l * (map g ⟨$⟩ x)
    scD-pt = ?

    nrm-sc : ∀ (g : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre g ≈ 1# → ∫ᴹ {WQ} lebPre (scD g) ≈ 1#
    nrm-sc = ?

    push-dens : ∀ (g : Hom S WQ WQ) (nrm : ∫ᴹ {WQ} lebPre g ≈ 1#) (f : Hom S WQ WQ) →
      ∫ᴹ {WQ} (ιPre {WQ} (C.mapPre {WQ} {WQ} sc (densDist g nrm))) f ≈ ∫ᴹ {WQ} (ιPre {WQ} (densDist (scD g) (nrm-sc g nrm))) f
    push-dens = ?

    ----------------------------------------------------------------------------
    -- the exponential at rate l

    -- the density y ↦ l e^{−l y}
    densR : Hom S WQ WQ
    densR = scaleH l (negExpRH l)

    -- ∫ e^{−l y} dy ≈ c
    ∫-negExpR : ∫ᴹ {WQ} lebPre (negExpRH l) ≈ c
    ∫-negExpR = ?

    nrmR : ∫ᴹ {WQ} lebPre densR ≈ 1#
    nrmR = ?

    scD-negExp : ∀ y → map (scD negExpH) ⟨$⟩ y ≈ map densR ⟨$⟩ y
    scD-negExp = ?

    agree : ∀ (f : Hom S WQ WQ) →
      ∫ᴹ {WQ} (ιPre {WQ} (Push.expPush c cB)) f ≈ ∫ᴹ {WQ} (ιPre {WQ} (densDist densR nrmR)) f
    agree = ?

    -- the same against the rate family of `Inference/ExpRateDist`
    agree-dist : ∀ μ ν (lc : l * c ≈ 1#) (lμ : l ≤ natE (suc μ)) (cν : c ≤ natE (suc ν)) (f : Hom S WQ WQ) →
      ∫ᴹ {WQ} (ιPre {WQ} (Push.expPush c cB)) f ≈ ∫ᴹ {WQ} (ιPre {WQ} (Dist.expDistλ l c μ ν lc lμ cν)) f
    agree-dist = ?
