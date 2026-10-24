{-# OPTIONS --safe --without-K #-}

-- The discrete statistical model with additive real weights over [0,∞]: ordinary (countably
-- additive) discrete measures with real-valued weights, with `normalize`.
module QBS.Model.AdditiveModel where

import Level as L
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Category using (QBSCat)
open import QBS.IsStatisticalQBSLike using (IsStatisticalQBSLike)
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.AdditiveSemiring
open import QBS.Model.Discrete

additiveStatisticalQBSLike : (∀ (P : Set (L.suc L.zero)) → P ⊎ (P → ⊥ {L.suc L.zero})) →
  IsStatisticalQBSLike (L.suc L.zero) (QBSCat (discreteSource (L.suc L.zero)))
additiveStatisticalQBSLike lem = discreteStatisticalQBSLike (additiveNormalizable lem)
