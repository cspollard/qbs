{-# OPTIONS --safe --without-K #-}

-- Copy-and-paste set-ups, referenced from docs/Guide.md: the imports and `open`s needed to state a result about
-- (1) a Bernoulli coin in the discrete model (with a proof of its mean), and (2) the uniform distribution in
-- the continuous model (`∫ uniform f` and the unit interval `AQ` in scope).
module QBS.Example.Recipes where

import Level as L
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Model.Semiring
import QBS.Model.WeightClasses as WC      -- qualified: `Analysis.Measure` also exports `probClass`
open import QBS.Example.Program

-- (1) Discrete: a fair coin with weights in any complete semiring `A` with `half + half ≈ 1`.
module Bernoulli {ℓ} (A : CompleteSemiring ℓ) (half : CompleteSemiring.Carrier A)
    (hh : CompleteSemiring._≈_ A (CompleteSemiring._+_ A half half) (CompleteSemiring.1# A)) where
  open CompleteSemiring A renaming (Carrier to ∣A∣)
  open Programs A (WC.probClass A) (λ p → p)          -- weight class: probability measures; `ok1` is the identity

  B : Set ℓ
  B = L.Lift ℓ Bool

  _∧B_ : B → B → B
  L.lift a ∧B L.lift b = L.lift (a ∧ b)

  open Flip half hh B (L.lift true) (L.lift false) _∧B_   -- brings `flip : Prog B`, `∫-flip`, `both`, ... into scope

  -- the indicator of `true`, as a test function
  isTrue : B → ∣A∣
  isTrue (L.lift true) = 1#
  isTrue (L.lift false) = 0#

  -- the mean of the coin is ½
  flip-mean : ∫ flip (test isTrue) ≈ half
  flip-mean = trans (∫-flip isTrue) (trans (+-cong (*-identityʳ half) (zeroʳ half)) (+-identityʳ half))

-- (2) Continuous: `uniform : Pre AQ` and the integral `∫ : Pre X → Hom S X AQ → ∣A∣` (values in the unit interval).
open import QBS.Core using (idH)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Classical using (LEM₁)

module UniformSetup (lem₁ : LEM₁) where
  A = LowerRealsOmega (lemOf lem₁)                    -- values: [0,∞] as lower cuts of ℚ
  open UnitInterval A public using (AQ)               -- the unit interval as a quasi-Borel space
  open Integration A using (probClass)
  open Continuous A (lemOf lem₁) probClass public using (∫)
  open OmegaSemiring A public using (_≈_)
  open Arch (lowerRealsArch (lemOf lem₁)) public using (half)
  open Uniform lem₁ public using (uniform)

  -- `idH S {AQ}` is the identity morphism of `AQ`; the mean `∫ uniform (idH S {AQ}) ≈ half` is
  -- `UniformMean.mean` (stated at the level of the underlying integral `I`)
