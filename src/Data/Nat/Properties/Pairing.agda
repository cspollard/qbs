{-# OPTIONS --safe --without-K #-}

-- A pairing function for the natural numbers, a bijection ℕ × ℕ ≅ ℕ given by `pair` with left inverse `unpair`.
--   * `NatPairing`, the record of `pair`, `unpair` and `unpair-pair : unpair (pair n m) ≡ (n , m)`.
-- Route: the record has no dependencies beyond `Data.Nat.Base` and `Data.Product.Base`, so it can be moved
-- to the standard library unchanged; a concrete instance (Cantor's) is `QBS.Model.Pairing`.
module Data.Nat.Properties.Pairing where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

record NatPairing : Set where
  field
    pair : ℕ → ℕ → ℕ
    unpair : ℕ → ℕ × ℕ
    unpair-pair : ∀ n m → unpair (pair n m) ≡ (n , m)
