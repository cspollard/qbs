{-# OPTIONS --safe --without-K #-}

-- The continuous model instantiated at the extended naturals: the hypotheses of the model are
-- satisfiable.  (Probability measures there are {0,1}-valued, so the model is degenerate; it
-- checks the interface, not the measure theory.)
module QBS.Continuous.ExtNatModel where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core using (QBS)
open import QBS.Category using (QBSCat)
open import QBS.IsQBSLike using (IsQBSLike)
open import QBS.Borel.Source using (cantorSource)
open import QBS.Analysis.ExtNat using (module Instance)
open import QBS.Continuous.ProbInstance

module _ (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open ContinuousProb (Instance.ExtNatOmega (L.suc L.zero) lem) lem funext public

  extNatQBSLike : IsQBSLike (L.suc L.zero) (QBSCat cantorSource)
  extNatQBSLike = continuousQBSLike
