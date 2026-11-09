{-# OPTIONS --safe --without-K #-}

-- `IsStatisticalQBSLike`: `IsQBSLike` plus a `StatisticalInterface` (soft conditioning and normalisation).
module QBS.IsStatisticalQBSLike where

open import Level using (suc; _⊔_)

open import Categories.Category.Core using (Category)

open import QBS.IsQBSLike
open import QBS.Statistical using (StatisticalInterface)

-- A QBS-like category that also supports (soft) conditioning: a measure monad
-- with `score` and normalisation on top of the probability monad.
record IsStatisticalQBSLike {o h e} (C : Category o h e) : Set (suc (o ⊔ h ⊔ e)) where
  field
    base : IsQBSLike C
  open IsQBSLike base public
  field
    statistical : StatisticalInterface ℛ cartesianClosed prob binaryCoproducts
