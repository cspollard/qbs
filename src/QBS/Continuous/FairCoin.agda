{-# OPTIONS --safe --without-K #-}

-- The fair-coin measure on Cantor space as a `Measure` (Daniell functional on the measurable
-- functions, values in the extended non-negative reals as lower cuts of ℚ), with its value
-- on finite cylinders.  Classical: one parameter `lem₁ : P ⊎ ¬P` for propositions in Set₁.
module QBS.Continuous.FairCoin where

open import Data.Empty using (⊥)
open import Level using (lift)
open import Data.Sum.Base using (_⊎_)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Sum.Base using (inj₁; inj₂)

open import QBS.Borel.Core
open import QBS.Borel.PiLambda using (Cyl; ⊥ᵖ)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Fun
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.CoinCont using (module Cont)
open import QBS.Analysis.CoinSets using (module CoinSets)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.ClopenMeasure using (module Premeasure)
open import QBS.Analysis.Measure
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.CoinSimple using (module Simple)
open import QBS.Analysis.CoinIntegral
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.Functional
open import QBS.Classical using (LEM₁)

module FairCoin (lem₁ : LEM₁) where
  private A = LowerRealsOmega (lemOf lem₁)
  module F = Functional lem₁ (BM.coinBM (lemOf lem₁))
  open Integration A
  open Indicators A (lemOf lem₁) using (χ; Fun-χ)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open CoinSets (lemOf lem₁) using (μ-cyl; cyl→tree)
  open Premeasure (lowerRealsArch (lemOf lem₁)) using (μ0)

  -- the fair coin: the Daniell functional of the fair-coin Borel measure
  fairCoin : Measure
  fairCoin = F.functional

  -- the value on a finite cylinder is its dyadic measure (2⁻ⁿ for a cylinder fixing n bits)
  fairCoin-cyl : ∀ {U} (c : Cyl U) → I fairCoin (χ U) (Fun-χ (Cyl-borel c)) ≈ μ0 (proj₁ (cyl→tree c))
  fairCoin-cyl {U} c = trans (F.functional-ind (Cyl-borel c)) (μ-cyl c (Cyl-borel c))
