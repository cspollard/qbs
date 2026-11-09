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
open import QBS.RandomElements
open import QBS.IsQBSLike
open import QBS.Statistical
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

  -- Likewise for conditioning: the measure monad is a hypothesis.
  isStatisticalQBSLike : (P : ProbMonad (ℛQ S) (cartesianClosed S)) → FubiniOf P →
    StatisticalInterface (ℛQ S) (cartesianClosed S) P
      (Cocartesian.Cocartesian.coproducts (cocartesian S))
      (countableCoproduct S (λ _ → Canonical.CartesianClosed.⊤ (cartesianClosed S))) →
    IsStatisticalQBSLike (QBSCat S)
  isStatisticalQBSLike P F St = record { base = isQBSLike P F ; statistical = St }
