{-# OPTIONS --safe --without-K #-}

-- Unbiased estimators from moment hypotheses, for unbounded signed tests (plan 05, item 46).  For a probability P on Ω
-- and F : Fin n → SgT Ω with `SgMoments.Moments P n F μ σ²`:
--   * the sum is integrable and E Sₙ ≃ n μ (`Int-sum`, `Ex-sum`): the sample mean is unbiased;
--   * Sₙ² is integrable and Var Sₙ ≃ n σ² (`Int₂-sum`, `Var-sum`);
--   * n Qₙ − Sₙ² is integrable and E (n Qₙ − Sₙ²) ≃ (n² − n) σ² (`Int-ss`, `Ex-ss`): the sample variance is unbiased.
-- Route: induction on n.  Sₙ₊₁ = F₀ + S′ and Sₙ₊₁² ≐ F₀² + (F₀S′ + F₀S′) + S′² (`IndepAlg`-style pointwise identities);
-- F₀S′ ≐ Σⱼ F₀Fⱼ₊₁, integrable by `Int-+` with E ≃ n μ² from the uncorrelated pairs; then `SignedExpect.Ex-+`,
-- `Ex-scale`, and identities in the signed ring (`Bounded.signedRing`), as in `Analysis/Estimator`.
--   Skeleton: holes first.
module QBS.Continuous.SgSample where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (proj₁; proj₂)

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
open import QBS.Continuous.SgMoments using (module SgMoments)

module SgSample (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Int₂; Var)
  open SgMoments lem₁ using (natS; sumT; ssT; Moments)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- the sample mean
    Int-sum : ∀ n (F : Fin n → SgT Ω) → (∀ i → Int {Ω} (ιPre {Ω} P) (F i)) → Int {Ω} (ιPre {Ω} P) (sumT n F)
    Int-sum = ?

    Ex-sum : ∀ n F μ σ² (M : Moments P n F μ σ²) →
      Ex {Ω} (ιPre {Ω} P) (sumT n F) (Int-sum n F (λ i → proj₁ (proj₁ M i))) ≃ natS n *S μ
    Ex-sum = ?

    -- the variance of the sum
    Int₂-sum : ∀ n F μ σ² → Moments P n F μ σ² → Int₂ {Ω} P (sumT n F)
    Int₂-sum = ?

    Var-sum : ∀ n F μ σ² (M : Moments P n F μ σ²) → Var {Ω} P (sumT n F) (Int₂-sum n F μ σ² M) ≃ natS n *S σ²
    Var-sum = ?

    -- the sample variance
    Int-ss : ∀ n F μ σ² → Moments P n F μ σ² → Int {Ω} (ιPre {Ω} P) (ssT n F)
    Int-ss = ?

    Ex-ss : ∀ n F μ σ² (M : Moments P n F μ σ²) →
      Ex {Ω} (ιPre {Ω} P) (ssT n F) (Int-ss n F μ σ² M) ≃ (natS n *S natS n +S -S natS n) *S σ²
    Ex-ss = ?
