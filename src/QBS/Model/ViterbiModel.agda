{-# OPTIONS --safe --without-K #-}

-- The discrete statistical model with Viterbi (max, ×) weights over [0,∞]: weights are real
-- numbers and invertibility is non-trivial.
module QBS.Model.ViterbiModel where

import Level as L
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Category using (QBSCat)
open import QBS.IsStatisticalQBSLike using (IsStatisticalQBSLike)
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.ViterbiSemiring
open import QBS.Model.Discrete
open import QBS.Classical using (LEM)

viterbiStatisticalQBSLike : LEM (L.suc L.zero) →
  IsStatisticalQBSLike (L.suc L.zero) (QBSCat (discreteSource (L.suc L.zero)))
viterbiStatisticalQBSLike lem = discreteStatisticalQBSLike (viterbiNormalizable lem)
