{-# OPTIONS --safe --without-K #-}

-- Non-vacuity witnesses for the discrete statistical model: `IsStatisticalQBSLike` instances with Boolean
-- (possibilistic), Viterbi (max, ×) and additive [0,∞] weights, so the abstract interfaces and the model are
-- not empty.  Each needs excluded middle at the weights' level (to decide invertibility of a mass).
module QBS.Model.Instances where

import Level as L
open import Level using (Level)

open import QBS.Category using (QBSCat)
open import QBS.IsStatisticalQBSLike using (IsStatisticalQBSLike)
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.BoolSemiring
open import QBS.Model.ViterbiSemiring
open import QBS.Model.AdditiveSemiring
open import QBS.Model.Discrete
open import QBS.Classical using (LEM)

-- Boolean (possibilistic) weights.
boolStatisticalQBSLike : ∀ (ℓ : Level) → LEM ℓ →
  IsStatisticalQBSLike ℓ (QBSCat (discreteSource ℓ))
boolStatisticalQBSLike ℓ lem = discreteStatisticalQBSLike (boolNormalizable ℓ lem)

-- Viterbi (max, ×) weights over [0,∞]: real numbers, so invertibility is non-trivial.
viterbiStatisticalQBSLike : LEM (L.suc L.zero) →
  IsStatisticalQBSLike (L.suc L.zero) (QBSCat (discreteSource (L.suc L.zero)))
viterbiStatisticalQBSLike lem = discreteStatisticalQBSLike (viterbiNormalizable lem)

-- Additive real weights over [0,∞]: ordinary countably additive discrete measures, with `normalize`.
additiveStatisticalQBSLike : LEM (L.suc L.zero) →
  IsStatisticalQBSLike (L.suc L.zero) (QBSCat (discreteSource (L.suc L.zero)))
additiveStatisticalQBSLike lem = discreteStatisticalQBSLike (additiveNormalizable lem)
