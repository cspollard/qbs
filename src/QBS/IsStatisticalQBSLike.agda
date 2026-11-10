{-# OPTIONS --safe --without-K #-}

-- `IsStatisticalQBSLike`: `IsQBSLike` plus a measure monad containing the probability monad as its normalized part, with
-- additive kernels (the algebraic monads of the theory of commutative monoids).  The weights are its scalars `M ⊤`.
module QBS.IsStatisticalQBSLike where

open import Level using (suc; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational.CommutativeMonoid using (CommMonoid)

open import QBS.IsQBSLike
open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Probability using (ProbMonad)
open import QBS.Monad.Normalized using (IsNormalizedInclusion)

-- A QBS-like category with a measure monad containing the probability monad, with additive kernels.
record IsStatisticalQBSLike {o h e} (C : Category o h e) : Set (suc (o ⊔ h ⊔ e)) where
  field
    base : IsQBSLike C
  open IsQBSLike base public
  field
    measures : MeasureMonad ℛ cartesianClosed
    probInclusion : StrongMonad⇒ (ProbMonad.strongMonad prob) (MeasureMonad.strongMonad measures)
    probIsNormalized : IsNormalizedInclusion probInclusion
    additive : IsAlgebraic CommMonoid (MeasureMonad.monad measures)
