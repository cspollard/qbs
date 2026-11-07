{-# OPTIONS --safe --without-K #-}

-- `IsQBSLike ℓ C`: what a category `C` must provide for QBS-style probabilistic programming: cartesian closure
-- (higher-order programs), binary and ℕ-indexed coproducts (branching, discrete data), ℕ-indexed products (infinite
-- families), a probe object ℛ, and a `ProbabilityInterface` on ℛ (a commutative strong monad of laws).  ℛ enters
-- only through that interface.  `QBSCat S` is the intended instance (`QBS.Instance`), given a monad as hypothesis;
-- `Model.ProbInstance` (discrete) and `Continuous.ProbInstance` supply the monads.
module QBS.IsQBSLike where

open import Level using (suc; _⊔_)
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
