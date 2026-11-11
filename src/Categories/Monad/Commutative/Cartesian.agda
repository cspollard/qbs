{-# OPTIONS --safe --without-K #-}

-- `braidedOf CC` and `CartCommMonad CC`: the one spelling of "a commutative monad on a cartesian closed category", for the
-- symmetric monoidal structure of its products.  Use `CartCommMonad CC` for every field or parameter of this type in the
-- abstract layer (`Probability`, `Statistical`, `DoubleStrength`) rather than writing `CommutativeMonad braided`.

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical

module Categories.Monad.Commutative.Cartesian
  {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C)
  where

open import Level using (_⊔_)

import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad.Commutative using (CommutativeMonad)

-- the braided monoidal structure of the cartesian product of a cartesian closed category
braidedOf : Braided _
braidedOf = Symmetric.braided (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- a commutative monad on a cartesian closed category, for the symmetric monoidal structure of its products
CartCommMonad : Set (o ⊔ h ⊔ e)
CartCommMonad = CommutativeMonad braidedOf
