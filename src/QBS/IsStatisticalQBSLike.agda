{-# OPTIONS --safe --without-K #-}

-- `IsStatisticalQBSLike`: `IsQBSLike` plus a measure monad containing the probability monad as its normalized part, soft
-- conditioning on it, and countable sums of kernels.  The structures are separate fields: see `QBS.Statistical`.
module QBS.IsStatisticalQBSLike where

open import Level using (suc; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)

open import QBS.IsQBSLike
open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Probability using (ProbMonad)
open import QBS.Statistical using
  (SemiringWeights; SoftConditioning; IsNormalizedInclusion; CountableSums)

-- A QBS-like category that also supports (soft) conditioning: a measure monad
-- containing the probability monad, with `score` and countable sums.
record IsStatisticalQBSLike {o h e} (C : Category o h e) : Set (suc (o ⊔ h ⊔ e)) where
  field
    base : IsQBSLike C
  open IsQBSLike base public
  field
    measures : MeasureMonad ℛ cartesianClosed
    probInclusion : StrongMonad⇒ (ProbMonad.strongMonad prob) (MeasureMonad.strongMonad measures)
    probIsNormalized : IsNormalizedInclusion probInclusion
    weights : SemiringWeights cartesianClosed
    countableSums : CountableSums (MeasureMonad.monad measures)
    conditioning : SoftConditioning weights countableSums
