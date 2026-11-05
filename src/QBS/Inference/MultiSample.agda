{-# OPTIONS --safe --without-K #-}

-- Samples of random vectors (plan 05, item 54).  For a probability law ν on Y and d features F : Fin d → SgT Y with
-- finite second moments under ν (`RandomVector.RV`; population mean vector `meanV ν d F` and covariance matrix
-- `covM ν d F`), and observations Xs : Fin n → Ω ⇒ Y iid with law ν under a probability P on Ω (`Continuous/IID`):
--   * each observed vector Xₖ = F ∘ Xs k (`obsV`) is a random vector with the population mean and covariance
--     (`RV-obs`, `mean-obs`, `cov-obs`);
--   * the sum vector Σₖ Xₖ (`sumV`) has mean n · mean (`mean-sum`, so the sample mean vector is unbiased) and covariance
--     n · Cov (`cov-sum`);
--   * the division-free sample cross-product matrix n Σₖ Xₖ Xₖᵀ − (Σₖ Xₖ)(Σₖ Xₖ)ᵀ (`ssM`, entrywise `crossT`; on the
--     diagonal it is `SgMoments.ssT`, `cross-diag`) has expectation (n² − n) Cov (`ss-unbiased`): the sample covariance
--     matrix is unbiased, as `SgSample.Ex-ss` for one coordinate.
-- Route: `RV-obs`, `mean-obs`, `cov-obs` transport along the law of Xs k (`IID.IID-law`, `SignedTransport.Int-map`,
-- `Ex-map`, `IID.Ex-≈`, with `ProdBridge.ι-mass`); `RV-sum` from `RandomVector.Int₂-sumV` per coordinate;
-- `mean-sum` from `SgSample.Ex-sumG`; `cov-sum` and `ss-unbiased` expand E[(Σₖ Gₖ)(Σₗ Hₗ)] by `RandomVectorSum.ExBil`,
-- with E[Gₖ Hₗ] ≃ E G · E H for k ≢ l (`Independence.Indep-pair`, `Int-indep`, `Ex-indep` with `IID.IID-indep`) and
-- the population cross moment for k = l; the double-sum arithmetic is a ring identity, as `SgSampleRing`.
--   Skeleton: holes first.
module QBS.Inference.MultiSample where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

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
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.IID using (module IID)
open import QBS.Continuous.RandomVector using (module RandomVector)

module MultiSample (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (_≃_; _+S_; _*S_; -S_; signedRing)
  open SgLinAlg signedRing using (_≈V_; _≈M_)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _∘T_; _*T_; _+T_; -T_; scaleT)
  open SignedExpect lem₁ using (Int; Ex)
  open SgMoments lem₁ using (natS; sumT; ssT)
  open IID lem₁ using (IID)
  open RandomVector lem₁ using (RV; meanV; covM)

  -- the observed vectors, the sum vector and the cross-product matrix
  obsV : ∀ {Ω Y : QBS S} d → (Fin d → SgT Y) → ∀ n → (Fin n → Hom S Ω Y) → Fin n → Fin d → SgT Ω
  obsV d F n Xs k a = F a ∘T Xs k

  sumV : ∀ {Ω Y : QBS S} d → (Fin d → SgT Y) → ∀ n → (Fin n → Hom S Ω Y) → Fin d → SgT Ω
  sumV d F n Xs a = sumT n (λ k → F a ∘T Xs k)

  -- n Σₖ Gₖ Hₖ − (Σₖ Gₖ)(Σₖ Hₖ)
  crossT : ∀ {Ω : QBS S} n → (Fin n → SgT Ω) → (Fin n → SgT Ω) → SgT Ω
  crossT n G H = scaleT (natS n) (sumT n (λ k → G k *T H k)) +T (-T (sumT n G *T sumT n H))

  cross-diag : ∀ {Ω : QBS S} n (G : Fin n → SgT Ω) → crossT n G G ≡ ssT n G
  cross-diag n G = refl

  ssM : ∀ {Ω Y : QBS S} d → (Fin d → SgT Y) → ∀ n → (Fin n → Hom S Ω Y) → Fin d → Fin d → SgT Ω
  ssM d F n Xs a b = crossT n (λ k → F a ∘T Xs k) (λ k → F b ∘T Xs k)

  module _ {Ω : QBS S} (P : C.Pre Ω) {Y : QBS S} (ν : C.Pre Y) d (F : Fin d → SgT Y) (rF : RV ν d F) where

    private
      E = ιPre {Ω} P

    -- each observation has the population moments
    RV-obs : ∀ n Xs → IID P (ιPre {Y} ν) n Xs → ∀ k → RV P d (obsV d F n Xs k)
    RV-obs = ?

    mean-obs : ∀ n Xs (D : IID P (ιPre {Y} ν) n Xs) k → meanV P d (obsV d F n Xs k) (RV-obs n Xs D k) ≈V meanV ν d F rF
    mean-obs = ?

    cov-obs : ∀ n Xs (D : IID P (ιPre {Y} ν) n Xs) k → covM P d (obsV d F n Xs k) (RV-obs n Xs D k) ≈M covM ν d F rF
    cov-obs = ?

    -- the sum vector: mean n · mean, covariance n · Cov
    RV-sum : ∀ n Xs → IID P (ιPre {Y} ν) n Xs → RV P d (sumV d F n Xs)
    RV-sum = ?

    mean-sum : ∀ n Xs (D : IID P (ιPre {Y} ν) n Xs) →
      meanV P d (sumV d F n Xs) (RV-sum n Xs D) ≈V (λ a → natS n *S meanV ν d F rF a)
    mean-sum = ?

    cov-sum : ∀ n Xs (D : IID P (ιPre {Y} ν) n Xs) →
      covM P d (sumV d F n Xs) (RV-sum n Xs D) ≈M (λ a b → natS n *S covM ν d F rF a b)
    cov-sum = ?

    -- the sample covariance matrix is unbiased
    Int-ssM : ∀ n Xs → IID P (ιPre {Y} ν) n Xs → ∀ a b → Int {Ω} E (ssM d F n Xs a b)
    Int-ssM = ?

    ss-unbiased : ∀ n Xs (D : IID P (ιPre {Y} ν) n Xs) a b →
      Ex {Ω} E (ssM d F n Xs a b) (Int-ssM n Xs D a b) ≃ (natS n *S natS n +S -S natS n) *S covM ν d F rF a b
    ss-unbiased = ?
