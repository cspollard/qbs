{-# OPTIONS --safe --without-K #-}

-- SKELETON (unsolved holes). The cumulative distribution function of the uniform distribution on
-- [0,1]: `P(u ≤ t) = t`, the integral of the indicator of `[0,t]`.
--
-- Plan (decided, not started; each step is a separate lemma):
--   1. Measurability of the test function: `cdfTest t : 𝕀 ⇒ 𝕀` must send random elements `β` to
--      measurable functions; the set `{r | β r ≤ t}` is Borel by `LevelSets.LS` applied to `β`.
--   2. First-bit decomposition of the fair coin: for every measurable `h`,
--        I fairCoin h ≈ ½ · I fairCoin (h ∘ cons true) + ½ · I fairCoin (h ∘ cons false),
--      by `Uniqueness` (both sides are probability measures agreeing on cylinders); needs
--      `Fun` closed under precomposition with `cons b`, a measurable map (cf. `Analysis/Param.agda`).
--   3. Self-similarity `expansion (cons b r) ≈ ½ · (bit b + expansion r)` (from `Analysis/BinaryExpansion`).
--   4. For dyadic `t = k/2ⁿ`, `F(t) = μ{expansion ≤ t}` satisfies `F(t) = ½F(2t)` and
--      `F(t) = ½ + ½F(2t−1)`, hence `F(k/2ⁿ) = k/2ⁿ` by induction on `n` (with `F(0) = 0` from the
--      null set `{000…}`); arbitrary `t` by monotonicity and density.
module QBS.Continuous.UniformCDF where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_; proj₁)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core using (Hom)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Continuous.Sample using (module UnitInterval; S)
open import QBS.Continuous.SubProb
open import QBS.Continuous.SubModel using (module SubModel)

module UniformCDF (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  A = LowerRealsOmega (lemOf lem₁)
  open UnitInterval A using (AQ)
  open ContinuousSub A (lemOf lem₁) funext
  open SubModel lem₁ funext using (uniformSub)
  open import QBS.Analysis.Omega using (module OmegaSemiring)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_)

  -- the indicator of [0,t] as a test function on the unit interval
  cdfTest : ∣A∣ → Hom S AQ AQ
  cdfTest t = ?

  cdf : ∀ (t : ∣A∣) → t ≤ OmegaSemiring.1# A → ∫ uniformSub (cdfTest t) ≈ t
  cdf t t≤1 = ?
