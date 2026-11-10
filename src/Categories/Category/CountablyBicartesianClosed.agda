{-# OPTIONS --safe --without-K #-}

-- `CountablyBicartesianClosed C`: `C` is cartesian closed (higher-order programs) and has binary coproducts (branching)
-- and ℕ-indexed products and coproducts (infinite families, discrete data).
module Categories.Category.CountablyBicartesianClosed where

open import Level using (suc; _⊔_)
open import Data.Nat.Base using (ℕ)

open import Categories.Category.Core using (Category)
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Object.Product.Indexed using (IndexedProductOf)
open import Categories.Object.Coproduct.Indexed using (IndexedCoproductOf)

record CountablyBicartesianClosed {o h e} (C : Category o h e) : Set (suc (o ⊔ h ⊔ e)) where
  open Category C
  field
    cartesianClosed     : Canonical.CartesianClosed C
    binaryCoproducts    : Cocartesian.BinaryCoproducts C
    countableProducts   : (P : ℕ → Obj) → IndexedProductOf C P
    countableCoproducts : (P : ℕ → Obj) → IndexedCoproductOf C P
