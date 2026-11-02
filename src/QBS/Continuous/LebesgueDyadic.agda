{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure of the dyadic intervals (plan 03, "Uniqueness on the half-line").  Skeleton: holes first.
--   * `fair-top`: the all-true point has fair-coin measure 0 (it lies in the cylinder `trueⁿ` of measure ½ⁿ, every n);
--   * `cell-in`, `cell-out`: the unit interval shifted by j, `j + expansion r`, lies in the dyadic interval
--     [m/2ⁿ, (m+1)/2ⁿ) with fair-coin probability ½ⁿ when that interval is inside [j, j+1), and 0 otherwise.  Induction
--     on n with the first-bit split (`Continuous/FirstBit`) and `expansion (b ∷ r) = b/2 + expansion r / 2`
--     (`Analysis/ExpansionCons`): an affine bijection maps half-open intervals exactly onto half-open intervals, so the
--     only null set is `fair-top`, at n = 0;
--   * `leb-χI`, `leb-inf`, `leb-fin`: the hypotheses of `UniquenessWQ.uniqWQ` for `lebPre` (via `HalfLine.∫ᴹ-leb`).
module QBS.Continuous.LebesgueDyadic where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc; _*_; _^_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Sum.Base using (_⊎_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Cells using (Top; borelTop)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)

module LebesgueDyadic (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J)
  open OmegaSemiring A using (_≈_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ)
  open LevelSets (lemOf lem₁) using (LS)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift)
  open Intervals (lemOf lem₁) using (χI; χInf)
  open QBS
  open Hom

  -- the all-true point is null
  fair-top : J fairCoin (χ Top) (LS (Fun-χ borelTop)) ≈ 0#
  fair-top = ?

  -- the law of the shifted expansion on dyadic intervals
  cell-in : ∀ j n m → j * 2 ^ n ≤ℕ m → m <ℕ suc j * 2 ^ n →
    J fairCoin (λ r → map (χI n m) ⟨$⟩ shiftPt j r) (Meas-hshift j (χI n m)) ≈ hp n
  cell-in = ?

  cell-out : ∀ j n m → (m <ℕ j * 2 ^ n) ⊎ (suc j * 2 ^ n ≤ℕ m) →
    J fairCoin (λ r → map (χI n m) ⟨$⟩ shiftPt j r) (Meas-hshift j (χI n m)) ≈ 0#
  cell-out = ?

  ----------------------------------------------------------------------------
  -- Lebesgue measure: the hypotheses of `UniquenessWQ.uniqWQ`

  leb-χI : ∀ n m → ∫ᴹ {WQ} lebPre (χI n m) ≈ hp n
  leb-χI = ?

  leb-inf : ∫ᴹ {WQ} lebPre χInf ≈ 0#
  leb-inf = ?

  leb-fin : ∀ k → Bnd (∫ᴹ {WQ} lebPre (χI 0 k))
  leb-fin = ?
