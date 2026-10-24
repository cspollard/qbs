{-# OPTIONS --safe --without-K #-}

module QBS.IsStatisticalQBSLike where

open import Level using (suc; _⊔_)

open import Categories.Category.Core using (Category)

open import QBS.IsQBSLike
open import QBS.Statistical using (StatisticalInterface)

-- A QBS-like category that also supports (soft) conditioning: a measure monad
-- with `score` and normalisation on top of the probability monad.
record IsStatisticalQBSLike {o h e} ℓ (C : Category o h e) : Set (suc (o ⊔ h ⊔ e ⊔ ℓ)) where
  field
    base : IsQBSLike ℓ C
  open IsQBSLike base public
  field
    statistical : StatisticalInterface ℓ C ℛ cartesianClosed prob binaryCoproducts
