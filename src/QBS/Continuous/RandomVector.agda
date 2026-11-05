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
-- Route: `RV`, `Int-mul`, `meanV`, `covM`, `affT` are re-exported from `RandomVectorDefs`; `Int-mul` is
-- `RandomVectorAlg.Int-mul` (`SignedExpect.Int-dom` with the dominating test f² + g² and a b ≤ a² + b²);
-- `cov-sym` by `comm-eq`; `cov-diag` by irrelevance of the integrability witness (`Ex-irr`); `Int₂-sumV`, `Var-sumV`,
-- `RV-aff`, `mean-aff`, `cov-aff` are the primed twins in `RandomVectorAff` (expansion of E[(Σᵢ Aᵢ)(Σⱼ Bⱼ)] by
-- `RandomVectorSum.ExBil`, shifts and scalings by `RandomVectorAlg.sh-eq`/`sc-eq`, the double-sum arithmetic in
-- `RandomVectorSumRing`); `cov-indep` from `Independence.Indep-pair`, `Ex-indep` and x − x ≃ 0.
module QBS.Continuous.RandomVector where

open import Algebra using (CommutativeRing)
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
open import QBS.Continuous.RandomVectorAlg using (module RandomVectorAlg)
open import QBS.Continuous.RandomVectorDefs using (module RandomVectorDefs)
open import QBS.Continuous.RandomVectorAff using (module RandomVectorAff)

module RandomVector (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; 0S; signedRing; ≃-refl; ≃-trans; +S-cong; -S-cong; *S-comm)
  module SR = CommutativeRing signedRing
  open SgLinAlg signedRing using (Vec; Mat; Σ; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; _∘T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex; Ex-irr; Ex-cong)
  open SignedVar lem₁ using (Int₂; Var)
  open SgMoments lem₁ using (sumT)
  open Independence lem₁ using (Indep; Indep-pair; Int-indep; Ex-indep)
  open RandomVectorAlg lem₁ using (comm-eq)
  module RA = RandomVectorAff lem₁
  open RandomVectorDefs lem₁ using () renaming (module Defs to RDefs)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    open RDefs {Ω} P public using (RV; Int-mul; meanV; covM; affT)

    cov-sym : ∀ n X (r : RV n X) i j → covM n X r i j ≃ covM n X r j i
    cov-sym n X r i j = +S-cong (Ex-cong {Ω} E _ _ _ _ (comm-eq (X i) (X j))) (-S-cong (*S-comm _ _))

    cov-diag : ∀ n X (r : RV n X) i → covM n X r i i ≃ Var {Ω} P (X i) (r i)
    cov-diag n X r i = +S-cong (Ex-irr {Ω} E (X i *T X i) _ _) ≃-refl

    -- the variance of the sum is the sum of the covariances
    Int₂-sumV : ∀ n X → RV n X → Int₂ {Ω} P (sumT n X)
    Int₂-sumV n X r = RA.Int₂-sumV′ {Ω} P n X r

    Var-sumV : ∀ n X (r : RV n X) → Var {Ω} P (sumT n X) (Int₂-sumV n X r) ≃ Σ n (λ i → Σ n (λ j → covM n X r i j))
    Var-sumV n X r = RA.Var-sumV′ {Ω} P n X r

    -- independent coordinates are uncorrelated
    cov-indep : ∀ n Ys (Zs : ∀ i → Hom S Ω (Ys i)) (u : ∀ i → SgT (Ys i)) → Indep P n Ys Zs →
      (r : RV n (λ i → u i ∘T Zs i)) → ∀ i j → i ≢ j → covM n (λ k → u k ∘T Zs k) r i j ≃ 0S
    cov-indep n Ys Zs u d r i j ne = ≃-trans (+S-cong (≃-trans (Ex-irr {Ω} E _ _ (Int-indep {Ω} P (Zs i) (Zs j) dij
      (u i) (u j) ri rj)) (Ex-indep {Ω} P (Zs i) (Zs j) dij (u i) (u j) ri rj)) ≃-refl) (SR.-‿inverseʳ _)
      where dij = Indep-pair {Ω} P n Ys Zs d i j ne
            ri = proj₁ (r i)
            rj = proj₁ (r j)

    -- the affine image AX + b
    RV-aff : ∀ {m n} (M : Mat m n) b X → RV n X → RV m (affT M b X)
    RV-aff M b X r = RA.RV-aff′ {Ω} P M b X r

    mean-aff : ∀ {m n} (M : Mat m n) b X (r : RV n X) → meanV m (affT M b X) (RV-aff M b X r) ≈V (M *Mv meanV n X r) +V b
    mean-aff M b X r = RA.mean-aff′ {Ω} P M b X r

    cov-aff : ∀ {m n} (M : Mat m n) b X (r : RV n X) → covM m (affT M b X) (RV-aff M b X r) ≈M (M *M covM n X r) *M (M ᵀ)
    cov-aff M b X r = RA.cov-aff′ {Ω} P M b X r
