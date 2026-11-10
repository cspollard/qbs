{-# OPTIONS --safe --without-K #-}

-- `isQBSLike S`: `QBSCat S` is QBS-like for every random source S, given an additive measure monad with Fubini as hypotheses.
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
open import QBS.Monad.Fubini
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational.CommutativeMonoid using (CommMonoid)
open import QBS.RandomElements
open import QBS.QBSLike

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

    -- Everything but the measure monad holds for every random source; the monad, its Fubini splitting and its additive
  -- kernels are hypotheses until a concrete one is constructed.
  isQBSLike : (MM : MeasureMonad (ℛQ S) (cartesianClosed S)) →
    IsFubini (ℛQ S) (cartesianClosed S) (MeasureMonad.commutativeMonad MM) →
    IsAlgebraic CommMonoid (MeasureMonad.monad MM) →
    IsQBSLike (QBSCat S)
  isQBSLike MM F CM = record
    { ℛ = ℛQ S
    ; structure = record
        { cartesianClosed = cartesianClosed S
        ; binaryCoproducts = Cocartesian.Cocartesian.coproducts (cocartesian S)
        ; countableProducts = countableProduct S
        ; countableCoproducts = countableCoproduct S
        }
    ; measures = MM
    ; fubini = F
    ; additive = CM
    }
