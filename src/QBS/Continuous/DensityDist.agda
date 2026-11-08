{-# OPTIONS --safe --without-K #-}

-- Any normalised density on [0,∞) as a probability `Pre` (the general recipe of which `Continuous/ExpDist` is the hand-spelled instance `d = negExpH`; `ExpDist` does not import this module).
-- See the "Distribution recipe" entry of `docs/Interface.md`.
--   * for `d : Hom S WQ WQ` with `nrm : ∫ᴹ lebPre d ≈ 1#`, `densDist d nrm = normPre (reweightPre d lebPre) 1# _`;
--   * `∫-dens : ∫ᴹ (ιPre (densDist d nrm)) f ≈ ∫ᴹ lebPre (d · f)` for every non-negative `f`;
--   * `∫-dens-one`: the total mass `∫ᴹ (ιPre (densDist d nrm)) 1 ≈ 1#`.
module QBS.Continuous.DensityDist where

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)

module DensityDist (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#; sym; trans; *-identityˡ; *-identityʳ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (module C; XW; ∫ᴹ; ∫ᴹ-cong)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteNorm (lemOf lem₁) using (massP; normPre; ∫-normPre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open HalfLine lem₁ using (lebPre)
  open QBS
  open Hom

  -- Lebesgue measure with density `d`
  abstract
    densW : Hom S WQ WQ → C.Pre (XW WQ)
    densW d = reweightPre {WQ} d lebPre

    ∫ᴹ-densW : ∀ d (f : Hom S WQ WQ) → ∫ᴹ {WQ} (densW d) f ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} d f)
    ∫ᴹ-densW d f = ∫ᴹ-reweight {WQ} d lebPre f

  -- total mass 1
  massP-densW : ∀ d → ∫ᴹ {WQ} lebPre d ≈ 1# → massP {WQ} (densW d) ≈ 1#
  massP-densW d nrm = trans (∫ᴹ-densW d (constW 1#))
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (constW 1#)} {d} (λ x → *-identityʳ _)) nrm)

  mass-inv : ∀ d → ∫ᴹ {WQ} lebPre d ≈ 1# → massP {WQ} (densW d) * 1# ≈ 1#
  mass-inv d nrm = trans (*-identityʳ _) (massP-densW d nrm)

  -- the distribution
  abstract
    densDist : ∀ d → ∫ᴹ {WQ} lebPre d ≈ 1# → C.Pre WQ
    densDist d nrm = normPre {WQ} (densW d) 1# (mass-inv d nrm)

    ∫-dens : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (f : Hom S WQ WQ) →
      ∫ᴹ {WQ} (ιPre {WQ} (densDist d nrm)) f ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} d f)
    ∫-dens d nrm f = trans (∫-normPre {WQ} (densW d) 1# (mass-inv d nrm) f)
      (trans (*-identityˡ _) (∫ᴹ-densW d f))

  -- normalisation
  ∫-dens-one : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) → ∫ᴹ {WQ} (ιPre {WQ} (densDist d nrm)) (constW 1#) ≈ 1#
  ∫-dens-one d nrm = trans (∫-dens d nrm (constW 1#))
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (constW 1#)} {d} (λ x → *-identityʳ _)) nrm)
