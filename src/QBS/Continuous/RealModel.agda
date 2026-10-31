{-# OPTIONS --safe --without-K #-}

-- The continuous model with values in [0, ∞] (lower cuts of the rationals): quasi-Borel spaces
-- over Cantor space with the Daniell probability monad, as an `IsQBSLike`.
module QBS.Continuous.RealModel where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Category using (QBSCat)
open import QBS.IsQBSLike using (IsQBSLike)
open import QBS.Borel.Source using (cantorSource)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Continuous.ProbInstance
open import QBS.Classical using (LEM₀)

module _ (lem : LEM₀) where
  open ContinuousProb (LowerRealsOmega lem) lem public

  realQBSLike : IsQBSLike (L.suc L.zero) (QBSCat cantorSource)
  realQBSLike = continuousQBSLike
