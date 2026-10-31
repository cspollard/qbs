{-# OPTIONS --safe --without-K #-}

-- `IsQBSLike`: the minimal structure for probability the QBS way: probe object, cartesian closure, (countable) coproducts and products, and a `ProbabilityInterface`.
module QBS.IsQBSLike where

open import Level using (Level; suc; _⊔_)
open import Data.Nat.Base using (ℕ)

open import Categories.Category.Core using (Category)
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Object.Product.Indexed using (IndexedProductOf)
open import Categories.Object.Coproduct.Indexed using (IndexedCoproductOf)

open import QBS.Probability using (ProbabilityInterface)

-- The structure needed to do probability the way QBS does it, and no more:
--   * higher-order programs:    cartesian closure,
--   * discrete data, branching: binary and countable coproducts,
--   * infinite families:        countable products,
--   * randomness:               an object ℛ of probes and a commutative strong
--                               monad of laws (see `ProbabilityInterface`).
record IsQBSLike {o h e} ℓ (C : Category o h e) : Set (suc (o ⊔ h ⊔ e ⊔ ℓ)) where
  open Category C
  field
    ℛ : Obj
    cartesianClosed : Canonical.CartesianClosed C
    binaryCoproducts : Cocartesian.BinaryCoproducts C
    countableProducts : (P : ℕ → Obj) → IndexedProductOf C P
    countableCoproducts : (P : ℕ → Obj) → IndexedCoproductOf C P
    prob : ProbabilityInterface ℓ ℛ cartesianClosed
