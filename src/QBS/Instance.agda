{-# OPTIONS --safe --without-K #-}

-- `isQBSLike S` / `isStatisticalQBSLike S`: `QBSCat S` is QBS-like for every random source S, given the probability (resp. statistical) monad as a hypothesis.
-- Every random source gives the category structure for free (cartesian closure, limits, colimits); the monad is
-- the only modelling input.
module QBS.Instance where


import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.CartesianClosed.Canonical as Canonical

open import QBS.Core
open import QBS.Category
open import QBS.Limits
open import QBS.Colimits
open import QBS.Complete
open import QBS.Exponential
open import QBS.Monad.Probability
open import QBS.Monad.Fubini
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational.CommutativeMonoid using (CommMonoid)
open import QBS.RandomElements
open import QBS.IsQBSLike
open import QBS.Monad.Normalized
open import QBS.IsStatisticalQBSLike

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  -- Everything but the probability monad holds for every random source; the
  -- monad is taken as a hypothesis until a concrete one is constructed.
  FubiniOf : ProbMonad (ℛQ S) (cartesianClosed S) → Set _
  FubiniOf P = IsFubini (ℛQ S) (cartesianClosed S) (ProbMonad.commutativeMonad P)

  isQBSLike : (P : ProbMonad (ℛQ S) (cartesianClosed S)) → FubiniOf P →
    IsQBSLike (QBSCat S)
  isQBSLike P F = record
    { ℛ = ℛQ S
    ; cartesianClosed = cartesianClosed S
    ; binaryCoproducts = Cocartesian.Cocartesian.coproducts (cocartesian S)
    ; countableProducts = countableProduct S
    ; countableCoproducts = countableCoproduct S
    ; prob = P
    ; fubini = F
    }

  -- Likewise for conditioning: the measure monad, its inclusion of Prob and additive kernels are hypotheses.
  isStatisticalQBSLike : (P : ProbMonad (ℛQ S) (cartesianClosed S)) → FubiniOf P →
    (MM : MeasureMonad (ℛQ S) (cartesianClosed S)) →
    (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) →
    IsNormalizedInclusion inc →
    (CM : IsAlgebraic CommMonoid (MeasureMonad.monad MM)) →
    IsStatisticalQBSLike (QBSCat S)
  isStatisticalQBSLike P F MM inc isN CM = record
    { base = isQBSLike P F
    ; measures = MM
    ; probInclusion = inc
    ; probIsNormalized = isN
    ; additive = CM
    }
