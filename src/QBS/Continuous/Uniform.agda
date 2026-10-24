{-# OPTIONS --safe --without-K #-}

-- The uniform distribution on [0,1] as an element of the continuous probability monad: the
-- fair coin pushed forward along the binary expansion map.
module QBS.Continuous.Uniform where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core using (QBS)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.BinaryExpansion
open import QBS.Continuous.Sample using (module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.FairCoin

module Uniform (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  open FairCoin lem₁ using (fairCoin)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh
  open UnitInterval A using (AQ)
  open Integration A using (probClass)
  open Continuous A (lemOf lem₁) funext probClass using (Pre; mk)

  -- the binary-expansion probe, a random element of the unit interval
  expansionProbe : R₁ → QBS.∣ AQ ∣
  expansionProbe r = expansion r , expansion≤1 r

  -- U[0,1]
  uniform : Pre AQ
  uniform = mk expansionProbe Fun-expansion fairCoin L-one
