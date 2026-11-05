{-# OPTIONS --safe --without-K #-}

-- Finite samples of signed tests and their moment hypotheses (plan 05, items 46 and 50).  Definitions only, shared by
-- `Continuous/SgSample` (unbiasedness), `Continuous/IID` (iid families satisfy the hypotheses) and `Inference/WeakLaw`.
-- For a probability P on Ω and n signed tests F : Fin n → SgT Ω (unbounded, with E Fᵢ² finite):
--   * `natS n`, the natural number n as a signed value; `sumT n F = F₀ + … + F_{n−1}`; `sqsT n F = F₀² + … + F_{n−1}²`;
--     `ssT n F = n · sqsT n F − (sumT n F)²`, which is n² times the biased sample variance (division-free, as in
--     `Analysis/Estimator`);
--   * `Moments P n F μ σ²`: each Fᵢ has E Fᵢ ≃ μ and E Fᵢ² ≃ σ² + μ², and for i ≢ j the product FᵢFⱼ is integrable with
--     E FᵢFⱼ ≃ μ² (uncorrelated).  A Σ type, not a record (records in parameterised modules are slow to check).
-- This is the signed, unbounded counterpart of `Estimator.Moments`, whose total ring of random variables does not
-- contain the unbounded tests.
module QBS.Continuous.SgMoments where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (Σ; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)

module SgMoments (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; 0S; 1S)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; -T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Int₂)

  -- n as a signed value
  natS : ℕ → Sg
  natS zero = 0S
  natS (suc n) = 1S +S natS n

  -- sums over a finite sample
  sumT : ∀ {Ω : QBS S} n → (Fin n → SgT Ω) → SgT Ω
  sumT zero F = constT 0S
  sumT (suc n) F = F zero +T sumT n (λ i → F (suc i))

  sqsT : ∀ {Ω : QBS S} n → (Fin n → SgT Ω) → SgT Ω
  sqsT n F = sumT n (λ i → F i *T F i)

  ssT : ∀ {Ω : QBS S} n → (Fin n → SgT Ω) → SgT Ω
  ssT n F = scaleT (natS n) (sqsT n F) +T (-T (sumT n F *T sumT n F))

  -- the moment hypotheses
  Moments : ∀ {Ω : QBS S} (P : C.Pre Ω) n → (Fin n → SgT Ω) → Sg → Sg → Set₁
  Moments {Ω} P n F μ σ² = Σ (∀ i → Int₂ {Ω} P (F i)) (λ ij →
    (∀ i → Ex {Ω} (ιPre {Ω} P) (F i) (proj₁ (ij i)) ≃ μ) ×
    (∀ i → Ex {Ω} (ιPre {Ω} P) (F i *T F i) (proj₂ (ij i)) ≃ σ² +S μ *S μ) ×
    (∀ i j → i ≢ j → Σ (Int {Ω} (ιPre {Ω} P) (F i *T F j)) (λ k → Ex {Ω} (ιPre {Ω} P) (F i *T F j) k ≃ μ *S μ)))
