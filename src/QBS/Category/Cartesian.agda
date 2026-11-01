{-# OPTIONS --safe --without-K #-}

-- The cartesian, cartesian-monoidal and braided structures of `QBSCat S`, named once.  They are read off the
-- canonical cartesian closed structure (`QBS.Exponential.cartesianClosed`) the way agda-categories reads them
-- off any cartesian closed category; the models that build strengths and commutativity proofs over `QBSCat S`
-- (`Model.Strong`, `Continuous.Strong`, `Continuous.SFiniteCommute`, `IntegralMonad`) share these names instead
-- of each rebuilding them.  (`Probability` and `Statistical` do the same over an abstract category `C`.)
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import QBS.Core
open import QBS.Category
open import QBS.Exponential using (cartesianClosed)

module QBS.Category.Cartesian {ℓ} (S : RandomSource ℓ) where

cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
V = CM.CartesianMonoidal.monoidal cartesian
braided = Symmetric.braided (CSM.symmetric (QBSCat S) cartesian)
{-# INLINE cartesian #-}
{-# INLINE V #-}
{-# INLINE braided #-}
