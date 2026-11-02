{-# OPTIONS --safe --without-K #-}

-- Uniqueness for finite weighted pushforwards on Cantor space (plan 03, "Uniqueness on the half-line").  Skeleton: holes
-- first.  A probability measure m, a `Meas` weight w and a measurable map x give the functional
--   Jw g = ∫ w(r) · g(x r) dm(r)
-- on the threshold-measurable g.  Two such functionals with equal finite mass that agree on every cylinder agree on
-- every `Meas` function (`uniqW`).  This extends `Analysis/Uniqueness` (probability measures, bounded `Fun`) by
--   * `wM`: a weighted pushforward of mass ≤ 1 is a `Measure`, with `I-wM` its integral;
--   * `uniqW-le1`: the case of mass ≤ 1, from `Uniqueness.agree-fun` applied to the two `wM`;
--   * `uniqW-fun`: finite mass, by scaling both weights by ½ʲ with `mass ≤ 2ʲ`;
--   * `uniqW`: unbounded g, by truncation and monotone convergence (`J-⨆`).
module QBS.Analysis.UniquenessWeighted where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ)

open import QBS.Borel.Core using (Measurable)
open import QBS.Borel.Source using (R₁) renaming (down to downR)
open import QBS.Borel.PiLambda using (Cyl)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)

module UniquenessWeighted (lem : LEM₀) where
  open Lebesgue lem using (A; J)
  open OmegaSemiring A using (_≈_; _≤_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Integration A using (Measure; I)
  open Measurable A using (Fun)
  open Meas lem using (Meas; Meas-⊗; Meas-pre; Meas-const)
  open LevelSets lem using (LS)
  open Indicators A lem using (χ; Fun-χ)
  open Bounded A using (Bnd)

  -- the indicator of a cylinder, as a `Meas` function
  χM : ∀ {C} → Cyl C → Meas (χ C)
  χM c = LS (Fun-χ (Cyl-borel c))

  -- the weighted pushforward g ↦ ∫ w(r) · g(x r) dm(r)
  Jw : (m : Measure) {w : R₁ → ∣A∣} → Meas w → {x : R₁ → R₁} → Measurable (downR x) → ∀ g → Meas g → ∣A∣
  Jw m {w} mw {x} mx g mg = J m (λ r → w r * g (x r)) (Meas-⊗ {w} {λ r → g (x r)} mw (Meas-pre {g} {x} mg mx))

  -- its mass
  Mw : (m : Measure) {w : R₁ → ∣A∣} → Meas w → {x : R₁ → R₁} → Measurable (downR x) → ∣A∣
  Mw m mw mx = Jw m mw mx (λ _ → 1#) (Meas-const 1#)

  -- a weighted pushforward of mass at most 1 is a `Measure`
  wM : (m : Measure) {w : R₁ → ∣A∣} (mw : Meas w) {x : R₁ → R₁} (mx : Measurable (downR x)) → Mw m mw mx ≤ 1# → Measure
  wM = ?

  I-wM : ∀ (m : Measure) {w} (mw : Meas w) {x} (mx : Measurable (downR x)) (b : Mw m mw mx ≤ 1#) {h} (f : Fun h) →
    I (wM m mw mx b) h f ≈ Jw m mw mx h (LS f)
  I-wM = ?

  module _ (m m′ : Measure) {w w′ : R₁ → ∣A∣} (mw : Meas w) (mw′ : Meas w′)
           {x x′ : R₁ → R₁} (mx : Measurable (downR x)) (mx′ : Measurable (downR x′))
           (fin : Bnd (Mw m mw mx)) (masses : Mw m mw mx ≈ Mw m′ mw′ mx′)
           (agree : ∀ {C} (c : Cyl C) → Jw m mw mx (χ C) (χM c) ≈ Jw m′ mw′ mx′ (χ C) (χM c)) where

    -- mass at most 1: `Uniqueness.agree-fun` for the two `wM`
    uniqW-le1 : Mw m mw mx ≤ 1# → ∀ {h} (f : Fun h) → Jw m mw mx h (LS f) ≈ Jw m′ mw′ mx′ h (LS f)
    uniqW-le1 = ?

    -- finite mass: scale both weights by ½ʲ, where `Mw m mw mx ≤ 2ʲ`
    uniqW-fun : ∀ {h} (f : Fun h) → Jw m mw mx h (LS f) ≈ Jw m′ mw′ mx′ h (LS f)
    uniqW-fun = ?

    -- every threshold-measurable function: truncate and pass to the limit
    uniqW : ∀ {g} (mg : Meas g) → Jw m mw mx g mg ≈ Jw m′ mw′ mx′ g mg
    uniqW = ?
