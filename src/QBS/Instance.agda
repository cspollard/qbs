{-# OPTIONS --safe --without-K #-}

-- `isQBSLike S` / `isStatisticalQBSLike S`: `QBSCat S` is QBS-like for every random source S, given the probability (resp. statistical) monad as a hypothesis.
module QBS.Instance where

open import Level using (Level; suc)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)
import Categories.Category.Cocartesian as Cocartesian

open import QBS.Core
open import QBS.Category
open import QBS.Limits
open import QBS.Colimits
open import QBS.Complete
open import QBS.Exponential
open import QBS.Probability
open import QBS.Probes
open import QBS.IsQBSLike
open import QBS.Statistical
open import QBS.IsStatisticalQBSLike

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  -- Everything but the probability monad holds for every random source; the
  -- monad is taken as a hypothesis until a concrete one is constructed.
  isQBSLike : ProbabilityInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) →
    IsQBSLike ℓ (QBSCat S)
  isQBSLike P = record
    { ℛ = ℛQ S
    ; cartesianClosed = cartesianClosed S
    ; binaryCoproducts = Cocartesian.Cocartesian.coproducts (cocartesian S)
    ; countableProducts = countableProduct S
    ; countableCoproducts = countableCoproduct S
    ; prob = P
    }

  -- Likewise for conditioning: the measure monad is a hypothesis.
  isStatisticalQBSLike : (P : ProbabilityInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S)) →
    StatisticalInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) P
      (Cocartesian.Cocartesian.coproducts (cocartesian S)) →
    IsStatisticalQBSLike ℓ (QBSCat S)
  isStatisticalQBSLike P St = record { base = isQBSLike P ; statistical = St }
