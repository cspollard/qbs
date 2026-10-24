{-# OPTIONS --safe --without-K #-}

-- The discrete model: QBS over the discrete random source R = ℕ, with weights in any
-- normalisable complete semiring (the extended non-negative reals are the intended one),
-- is a statistical QBS-like category, with *no remaining hypotheses* on the monads.
module QBS.Model.Discrete where

open import Level using (Level)

open import QBS.Core
open import QBS.Category
open import QBS.IsStatisticalQBSLike
open import QBS.Instance
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.ProbInstance
open import QBS.Model.StatInstance

discreteStatisticalQBSLike : ∀ {ℓ} (N : NormalizableSemiring ℓ) →
  IsStatisticalQBSLike ℓ (QBSCat (discreteSource ℓ))
discreteStatisticalQBSLike {ℓ} N =
  isStatisticalQBSLike (discreteSource ℓ)
    (discreteProb (NormalizableSemiring.complete N))
    (discreteStat N)
