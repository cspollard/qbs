{-# OPTIONS --safe --without-K #-}

-- Uniqueness of measures on the whole real line `RQ = WQ +Q WQ` (plan 03, "Tests and the real line").
-- A measure μ on RQ has two halves on the half-line, `restrL μ` and `restrR μ`: reweight by the indicator of the left
-- (right) summand and fold RQ onto WQ (`foldH = [id , id]`), so `∫-restrL : ∫ (restrL μ) g ≈ ∫ μ [g , 0]`.
--   * `∫-split : ∫ μ f ≈ ∫ μ [f∘inl , 0] + ∫ μ [0 , f∘inr]` (every test on RQ is the sum of its two halves);
--   * `uniqRQ`: measures with equal halves are equal;
--   * `lebR-unique`: a measure whose halves have the interval masses of Lebesgue measure and no mass at ±∞ is `lebR`
--     (through `LebesgueInterval.leb-unique` on each half, `restrL-lebR`, `restrR-lebR`).
-- Route for `∫-split`: f ≈ [f∘inl , 0] + [0 , f∘inr] pointwise on each summand (`copair` computes on `inl`, `inr`), and
-- `∫ᴹ` is additive in the test (`SFinite.∫ᴹ-series` with the sequence f₁, f₂, 0, 0, …, or the sum of tests by `copair`).
--   Skeleton: holes first.
module QBS.Continuous.UniquenessRQ where

open import Function.Bundles using (Func; _⟨$⟩_)

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
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.RealLine using (module RealLine)

module UniquenessRQ (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre)
  open HalfLine lem₁ using (lebPre)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χIv; χInf)
  open RealLine lem₁ using (RQ; inlH; inrH; copairH; lebR)
  open QBS
  open Hom

  zeroW : Hom S WQ WQ
  zeroW = constW 0#

  -- fold the two summands onto the half-line, and the indicators of the summands
  foldH : Hom S RQ WQ
  foldH = copairH idW idW

  oneL oneR : Hom S RQ WQ
  oneL = copairH (constW 1#) zeroW
  oneR = copairH zeroW (constW 1#)

  -- the two halves of a measure on RQ
  restrL restrR : Pre (XW RQ) → Pre (XW WQ)
  restrL μ = mapM {RQ} {WQ} foldH (reweightPre {RQ} oneL μ)
  restrR μ = mapM {RQ} {WQ} foldH (reweightPre {RQ} oneR μ)

  ∫-restrL : ∀ (μ : Pre (XW RQ)) (g : Hom S WQ WQ) → ∫ᴹ {WQ} (restrL μ) g ≈ ∫ᴹ {RQ} μ (copairH g zeroW)
  ∫-restrL = ?

  ∫-restrR : ∀ (μ : Pre (XW RQ)) (g : Hom S WQ WQ) → ∫ᴹ {WQ} (restrR μ) g ≈ ∫ᴹ {RQ} μ (copairH zeroW g)
  ∫-restrR = ?

  -- every test is the sum of its two halves
  ∫-split : ∀ (μ : Pre (XW RQ)) (f : Hom S RQ WQ) →
    ∫ᴹ {RQ} μ f ≈ ∫ᴹ {RQ} μ (copairH (_∘H_ S f inlH) zeroW) + ∫ᴹ {RQ} μ (copairH zeroW (_∘H_ S f inrH))
  ∫-split = ?

  uniqRQ : ∀ (μ ν : Pre (XW RQ)) → _≈ᴹ_ {WQ} (restrL μ) (restrL ν) → _≈ᴹ_ {WQ} (restrR μ) (restrR ν) →
    _≈ᴹ_ {RQ} μ ν
  uniqRQ = ?

  -- the halves of Lebesgue measure on RQ
  restrL-lebR : _≈ᴹ_ {WQ} (restrL lebR) lebPre
  restrL-lebR = ?

  restrR-lebR : _≈ᴹ_ {WQ} (restrR lebR) lebPre
  restrR-lebR = ?

  -- Lebesgue measure on RQ from its interval masses
  lebR-unique : ∀ (μ : Pre (XW RQ)) →
    (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {RQ} μ (copairH (χIv a b) zeroW) ≈ b) →
    (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {RQ} μ (copairH zeroW (χIv a b)) ≈ b) →
    ∫ᴹ {RQ} μ (copairH χInf χInf) ≈ 0# → _≈ᴹ_ {RQ} μ lebR
  lebR-unique = ?
