{-# OPTIONS --safe --without-K #-}

-- The fair-coin measure on the Borel sets of Cantor space, valued in lower cuts of the rationals:
-- σ-additive, with the dyadic value on every finite cylinder.
module QBS.Analysis.CoinSets where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Regular

module CoinSets (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) = Regularity (lowerRealsArch lem) lem
