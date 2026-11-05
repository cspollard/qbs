{-# OPTIONS --safe --without-K #-}

-- Random vectors, mean vectors and covariance matrices (plan 05, item 52).  On a probability P on Ω, a random vector
-- is X : Fin n → SgT Ω with finite second moments (`RV n X`, unbounded signed tests); values are vectors and
-- matrices over the signed ring (`Analysis/SgLinAlg` at `Bounded.signedRing`).
--   * the product of two square-integrable tests is integrable (`Int-mul`, from 2|xy| ≤ x² + y²);
--   * the mean vector `meanV` and the covariance matrix `covM`, Cov(Xᵢ, Xⱼ) = E XᵢXⱼ − E Xᵢ E Xⱼ; it is symmetric
--     (`cov-sym`) with the variances on the diagonal (`cov-diag`);
--   * Var(Σᵢ Xᵢ) ≃ Σᵢ Σⱼ Cov(Xᵢ, Xⱼ) (`Int₂-sumV`, `Var-sumV`; no moment hypotheses, unlike `SgSample.Var-sum`);
--   * coordinates u ∘ Zᵢ of mutually independent Zᵢ are uncorrelated (`cov-indep`: the off-diagonal entries vanish);
--   * the affine rule for AX + b (`affT`): mean(AX + b) ≃ A mean(X) + b (`mean-aff`) and Cov(AX + b) ≃ A Cov(X) Aᵀ
--     (`cov-aff`), with `RV-aff`.
-- Route: `Int-mul` by `SignedExpect.Int-dom` with the dominating test f² + g² (pointwise 2 (f⁺ + f⁻)(g⁺ + g⁻) ≤ …,
-- or (f + g)² and (f − g)² as in `IndepAlg`); `cov-diag` by irrelevance of the integrability witness (`Ex-cong`);
-- `Var-sumV` by induction on n with the pointwise identities of `IndepAlg`/`SgSampleAlg` and `SgLinAlg.Σ-+`;
-- `cov-indep` from `Independence.Indep-pair` and `Ex-indep`; `mean-aff` from `Ex-+`, `Ex-scale`, `Ex-const` and
-- `SgMoments.sumT` against `SgLinAlg.Σ`; `cov-aff` expands both sides into double sums (`Σ-scale`, `Σ-swap`).
--   Skeleton: holes first.
module QBS.Continuous.RandomVector where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

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
open import QBS.Continuous.Independence using (module Independence)

module RandomVector (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; 0S; signedRing)
  open SgLinAlg signedRing using (Vec; Mat; Σ; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; _∘T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Int₂; Var)
  open SgMoments lem₁ using (sumT)
  open Independence lem₁ using (Indep)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    -- a random vector with finite second moments
    RV : ∀ n → (Fin n → SgT Ω) → Set₁
    RV n X = ∀ i → Int₂ {Ω} P (X i)

    -- products of square-integrable tests are integrable
    Int-mul : ∀ (f g : SgT Ω) → Int₂ {Ω} P f → Int₂ {Ω} P g → Int {Ω} E (f *T g)
    Int-mul = ?

    -- the mean vector and the covariance matrix
    meanV : ∀ n X → RV n X → Vec n
    meanV n X r i = Ex {Ω} E (X i) (proj₁ (r i))

    covM : ∀ n X → RV n X → Mat n n
    covM n X r i j = Ex {Ω} E (X i *T X j) (Int-mul (X i) (X j) (r i) (r j)) +S -S (meanV n X r i *S meanV n X r j)

    cov-sym : ∀ n X (r : RV n X) i j → covM n X r i j ≃ covM n X r j i
    cov-sym = ?

    cov-diag : ∀ n X (r : RV n X) i → covM n X r i i ≃ Var {Ω} P (X i) (r i)
    cov-diag = ?

    -- the variance of the sum is the sum of the covariances
    Int₂-sumV : ∀ n X → RV n X → Int₂ {Ω} P (sumT n X)
    Int₂-sumV = ?

    Var-sumV : ∀ n X (r : RV n X) → Var {Ω} P (sumT n X) (Int₂-sumV n X r) ≃ Σ n (λ i → Σ n (λ j → covM n X r i j))
    Var-sumV = ?

    -- independent coordinates are uncorrelated
    cov-indep : ∀ n Ys (Zs : ∀ i → Hom S Ω (Ys i)) (u : ∀ i → SgT (Ys i)) → Indep P n Ys Zs →
      (r : RV n (λ i → u i ∘T Zs i)) → ∀ i j → i ≢ j → covM n (λ k → u k ∘T Zs k) r i j ≃ 0S
    cov-indep = ?

    -- the affine image AX + b
    affT : ∀ {m n} → Mat m n → Vec m → (Fin n → SgT Ω) → Fin m → SgT Ω
    affT {m} {n} M b X k = sumT n (λ i → scaleT (M k i) (X i)) +T constT (b k)

    RV-aff : ∀ {m n} (M : Mat m n) b X → RV n X → RV m (affT M b X)
    RV-aff = ?

    mean-aff : ∀ {m n} (M : Mat m n) b X (r : RV n X) → meanV m (affT M b X) (RV-aff M b X r) ≈V (M *Mv meanV n X r) +V b
    mean-aff = ?

    cov-aff : ∀ {m n} (M : Mat m n) b X (r : RV n X) → covM m (affT M b X) (RV-aff M b X r) ≈M (M *M covM n X r) *M (M ᵀ)
    cov-aff = ?
