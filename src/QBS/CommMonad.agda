{-# OPTIONS --safe --without-K #-}

-- `braidedOf CC` and `ProbMonad CC`: the one spelling of "a commutative monad on a cartesian closed category", for the
-- symmetric monoidal structure of its products.  Use `ProbMonad CC` for every field or parameter of this type in the
-- abstract layer (`Probability`, `Statistical`, `StrongPoint`) rather than writing `CommutativeMonad braided`.
module QBS.CommMonad where

open import Level using (_⊔_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad.Commutative using (CommutativeMonad)

-- the braided monoidal structure of the cartesian product of a cartesian closed category
braidedOf : ∀ {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C) →
  _
braidedOf {C = C} CC = Symmetric.braided (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- a commutative monad on a cartesian closed category, for the symmetric monoidal structure of its products
ProbMonad : ∀ {o h e} {C : Category o h e} → Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
ProbMonad CC = CommutativeMonad (braidedOf CC)
