{-# OPTIONS --safe --without-K #-}

-- Definitions for random vectors (shared by `RandomVector` and `RandomVectorAff`).
--   * `RV n X`: a random vector, i.e. coordinates with finite second moments;
--   * `Int-mul`: the product of two square-integrable tests is integrable;
--   * `meanV`, `covM`: the mean vector and the covariance matrix Cov(Xᵢ, Xⱼ) = E XᵢXⱼ − E Xᵢ E Xⱼ;
--   * `affT`: the affine image AX + b.
-- Route: `Int-mul` is `RandomVectorAlg.Int-mul` (`SignedExpect.Int-dom` with the dominating test f² + g²).
module QBS.Continuous.RandomVectorDefs where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.RandomVectorAlg using (module RandomVectorAlg)

module RandomVectorDefs (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _+S_; _*S_; -S_; signedRing)
  open SgLinAlg signedRing using (Vec; Mat)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Int₂)
  open SgMoments lem₁ using (sumT)

  module Defs {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    -- a random vector with finite second moments
    RV : ∀ n → (Fin n → SgT Ω) → Set₁
    RV n X = ∀ i → Int₂ {Ω} P (X i)

    -- products of square-integrable tests are integrable
    Int-mul : ∀ (f g : SgT Ω) → Int₂ {Ω} P f → Int₂ {Ω} P g → Int {Ω} E (f *T g)
    Int-mul f g i j = RandomVectorAlg.Int-mul lem₁ {Ω} E f g (proj₂ i) (proj₂ j)

    -- the mean vector and the covariance matrix
    meanV : ∀ n X → RV n X → Vec n
    meanV n X r i = Ex {Ω} E (X i) (proj₁ (r i))

    covM : ∀ n X → RV n X → Mat n n
    covM n X r i j = Ex {Ω} E (X i *T X j) (Int-mul (X i) (X j) (r i) (r j)) +S -S (meanV n X r i *S meanV n X r j)

    -- the affine image AX + b
    affT : ∀ {m n} → Mat m n → Vec m → (Fin n → SgT Ω) → Fin m → SgT Ω
    affT {m} {n} M b X k = sumT n (λ i → scaleT (M k i) (X i)) +T constT (b k)
