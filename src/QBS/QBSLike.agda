{-# OPTIONS --safe --without-K #-}

-- `IsQBSLike C`: what a category `C` provides for QBS-style probabilistic programming with weights:
--   * category structure: countably bicartesian closed (`CountablyBicartesianClosed`),
--   * randomness: a probe object ℛ and a commutative measure monad on it, with a Fubini splitting of ℛ,
--   * weights: additive kernels, so the scalars `M ⊤` are a commutative semiring (`Monad.Algebraic.Scalars`).
-- `QBSLike` is the bundle (as `Monoid` and `IsMonoid`).  `QBSCat S` is the intended instance (`QBS.Instance`), given the
-- measure monad as hypothesis.  A probability monad is the normalized part of `measures` (`QBS.Monad.Normalized`).
module QBS.QBSLike where

open import Level using (suc; _⊔_)

open import Categories.Category.Core using (Category)
open import Categories.Category.CountablyBicartesianClosed using (CountablyBicartesianClosed)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational.CommutativeMonoid using (CommMonoid)

open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Fubini using (IsFubini)

record IsQBSLike {o h e} (C : Category o h e) : Set (suc (o ⊔ h ⊔ e)) where
  open Category C
  field
    ℛ : Obj
    countablyBicartesianClosed : CountablyBicartesianClosed C

  open CountablyBicartesianClosed countablyBicartesianClosed public

  field
    measures : MeasureMonad ℛ cartesianClosed

  open MeasureMonad measures public

  field
    additive : IsAlgebraic CommMonoid monad
    fubini   : IsFubini ℛ cartesianClosed commutativeMonad

record QBSLike o h e : Set (suc (o ⊔ h ⊔ e)) where
  field
    Carrier : Category o h e
    isQBSLike : IsQBSLike Carrier

  open IsQBSLike isQBSLike public
