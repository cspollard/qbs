{-# OPTIONS --safe --without-K #-}

-- The discrete statistical model with Boolean (possibilistic) weights: a concrete instance of
-- `IsStatisticalQBSLike`, so the abstract interface and the discrete model are non-vacuous.
module QBS.Model.BoolModel where

open import Level using (Level)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Category using (QBSCat)
open import QBS.IsStatisticalQBSLike using (IsStatisticalQBSLike)
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.BoolSemiring
open import QBS.Model.Discrete

boolStatisticalQBSLike : ∀ (ℓ : Level) → (∀ (P : Set ℓ) → P ⊎ (P → ⊥ {ℓ})) →
  IsStatisticalQBSLike ℓ (QBSCat (discreteSource ℓ))
boolStatisticalQBSLike ℓ lem = discreteStatisticalQBSLike (boolNormalizable ℓ lem)
