{-# OPTIONS --safe --without-K #-}

-- The Riesz–Daniell correspondence between probability measures as Daniell functionals (`Measure`
-- with `IsProb`) and Borel probability measures as σ-additive set functions (`BorelMeasure`):
--   * `setFun m` restricts a functional to indicators,
--   * `Functional.functional` (`Analysis/Functional.agda`) integrates against a set function,
-- and the two round trips are the identity: `functional-setFun` (on every measurable function,
-- by the uniqueness theorem) and `setFun-functional` (on every Borel set).
module QBS.Analysis.Riesz where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Function.Base using (const)
open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Borel.Core
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Analysis.Omega
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Uniqueness using (module Uniqueness)
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Functional using (module Functional)

module Riesz (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  private A = LowerRealsOmega (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A using (Fun; Fun-const)
  open Integration A
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-cong; χ-⊤; I-⋃; I-χ-⊥)
  open Uniqueness A (lemOf lem₁) using (agree-fun)

  -- a probability functional restricted to indicators is a Borel probability measure
  setFun : (m : Measure) → IsProb m → BM.BorelMeasure (lemOf lem₁)
  setFun m pm = record
    { μ = λ bU → I m (χ _) (Fun-χ bU)
    ; μ-resp = λ bU bV e → I-cong m (χ-cong e) (Fun-χ bU) (Fun-χ bV)
    ; μ-⋃ = λ bs dj → I-⋃ m bs dj
    ; μ-⊤ = trans (I-cong m χ-⊤ (Fun-χ ⊤-borel) (Fun-const 1# ≤-refl)) pm
    ; μ-⊥ = I-χ-⊥ m ⊥-borel
    }

  -- the functional of a Borel probability measure
  module _ (ν : BM.BorelMeasure (lemOf lem₁)) where
    open Functional lem₁ ν using (functional; functional-ind; functional-prob)

    isProb-functional : IsProb functional
    isProb-functional = functional-prob

    -- set functions → functionals → set functions
    setFun-functional : ∀ {U} (bU : Borel U) →
      BM.BorelMeasure.μ (setFun functional isProb-functional) bU ≈ BM.BorelMeasure.μ ν bU
    setFun-functional = functional-ind

  -- functionals → set functions → functionals: equal on every measurable function
  functional-setFun : ∀ (m : Measure) (pm : IsProb m) {h} (f : Fun h) →
    I (Functional.functional lem₁ (setFun m pm)) h f ≈ I m h f
  functional-setFun m pm f =
    agree-fun (Functional.functional lem₁ (setFun m pm)) m
      (trans (isProb-functional (setFun m pm)) (sym pm))
      (λ c → Functional.functional-ind lem₁ (setFun m pm) (Cyl-borel c)) f
