{-# OPTIONS --safe --without-K #-}

-- The sub-probability monad of the continuous model over the real values `[0,∞]`, with soft
-- conditioning of the uniform distribution: draw `u ~ U[0,1]` and weight the run by `u`.
module QBS.Continuous.SubModel where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)

open import QBS.Core using (QBS; Hom)
open Hom using ()
open import QBS.Borel.Source using (cantorSource)
open import QBS.Limits using (1Q)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Core using (_∘H_)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.BinaryExpansion
open import QBS.Continuous.Sample using (module UnitInterval; S)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.UniformMean using (module UniformMean)
open import QBS.Continuous.SubProb
open import QBS.Continuous.Uniform using (module Uniform)

module SubModel (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  A = LowerRealsOmega (lemOf lem₁)
  open FairCoin lem₁ using (fairCoin)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh
  open UnitInterval A using (AQ)
  open ContinuousSub A (lemOf lem₁)
  open OmegaSemiring A using (_≈_; 1#; ≤-refl; refl; trans)
  open UniformMean lem₁ using (mean)
  open Uniform lem₁ using (expansionProbe)
  open import QBS.Analysis.Fun using (module Measurable)
  open Measurable A using (Fun-const)
  open Integration A using (I-cong; I)

  -- U[0,1], as a sub-probability pre-measure (the fair coin is a probability measure)
  uniformSub : Pre AQ
  uniformSub = mk expansionProbe Fun-expansion fairCoin tt

  -- draw u ~ U[0,1], then score the run by the likelihood u
  softUniform : Pre (1Q S)
  softUniform = joinPre (mapPre scoreH uniformSub)

  -- its integral: the uniform integral of the integral of the scored measure
  ∫-softUniform : ∀ f → ∫ softUniform f ≈ ∫ uniformSub (_∘H_ S (∫ᶠ f) scoreH)
  ∫-softUniform f = ∫-join (mapPre scoreH uniformSub) f

  -- the total mass of the soft-conditioned uniform draw is E[u] = ½
  oneTest : Hom S (1Q S) AQ
  oneTest = record
    { map = record { to = λ _ → 1# , ≤-refl ; cong = λ _ → refl }
    ; map-random = λ _ → Fun-const 1# ≤-refl }

  mass-softUniform : ∫ softUniform oneTest ≈ Arch.half (lowerRealsArch (lemOf lem₁))
  mass-softUniform = trans (∫-softUniform oneTest)
    (trans (I-cong fairCoin {h′ = expansion} (λ r → OmegaSemiring.*-identityʳ A (expansion r))
      (Hom.map-random (_∘H_ S (∫ᶠ oneTest) scoreH) {expansionProbe} Fun-expansion) Fun-expansion) mean)
