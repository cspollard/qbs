{-# OPTIONS --safe --without-K #-}

-- Unbiased estimators from moment hypotheses, for unbounded signed tests.  For a probability P on Ω
-- and F : Fin n → SgT Ω with `SgMoments.Moments P n F μ σ²`:
--   * the sum is integrable and E Sₙ ≃ n μ (`Int-sum`, `Ex-sum`): the sample mean is unbiased;
--   * Sₙ² is integrable and Var Sₙ ≃ n σ² (`Int₂-sum`, `Var-sum`);
--   * n Qₙ − Sₙ² is integrable and E (n Qₙ − Sₙ²) ≃ (n² − n) σ² (`Int-ss`, `Ex-ss`): the sample variance is unbiased.
-- Route: induction on n.  Sₙ₊₁ = F₀ + S′ and Sₙ₊₁² ≐ F₀² + (F₀S′ + F₀S′) + S′² (`IndepAlg`-style pointwise identities);
-- F₀S′ ≐ Σⱼ F₀Fⱼ₊₁, integrable by `Int-+` with E ≃ n μ² from the uncorrelated pairs; then `SignedExpect.Ex-+`,
-- `Ex-scale`, and identities in the signed ring (`Bounded.signedRing`), as in `Analysis/Estimator`.
module QBS.Continuous.SgSample where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (refl)

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
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Continuous.IndepAlg using (module IndepAlg)
open import QBS.Continuous.SgSampleAlg using (module SgSampleAlg)
open import QBS.Continuous.SgSampleRing using (module SRing)

module SgSample (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; signedRing; 0S; ≃-refl; ≃-trans; ≃-sym; +S-cong; -S-cong; *S-cong; *S-congʳ)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; -T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex; Ex-cong; Ex-+; Ex-neg; Ex-scale; Ex-const; Int-+; Int-neg; Int-scale; Int-const)
  open SignedVarAlg lem₁ using (Int-via)
  open IndepAlg lem₁ using (sqadd-eq; sqadd-sums)
  open SgSampleAlg lem₁ using (dist-eq; dist-sums; zero-eq; zero-sums)
  module SA = SRing signedRing
  open SignedVar lem₁ using (Int₂; Var)
  open SgMoments lem₁ using (natS; sumT; ssT; Moments)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    tailM : ∀ n F μ σ² → Moments P (suc n) F μ σ² → Moments P n (λ i → F (suc i)) μ σ²
    tailM n F μ σ² (ij , m , sq , c) =
      (λ i → ij (suc i)) , (λ i → m (suc i)) , (λ i → sq (suc i)) , (λ i j ne → c (suc i) (suc j) (λ { refl → ne refl }))

    -- the sample mean
    Int-sum : ∀ n (F : Fin n → SgT Ω) → (∀ i → Int {Ω} (ιPre {Ω} P) (F i)) → Int {Ω} (ιPre {Ω} P) (sumT n F)
    Int-sum zero F iF = Int-const {Ω} P 0S
    Int-sum (suc n) F iF = Int-+ {Ω} E (iF zero) (Int-sum n (λ i → F (suc i)) (λ i → iF (suc i)))

    -- the sum of tests with a common mean
    Ex-sumG : ∀ n (G : Fin n → SgT Ω) ν (iG : ∀ i → Int {Ω} E (G i)) → (∀ i → Ex {Ω} E (G i) (iG i) ≃ ν) →
      Ex {Ω} E (sumT n G) (Int-sum n G iG) ≃ natS n *S ν
    Ex-sumG zero G ν iG e = ≃-trans (Ex-const {Ω} P 0S) (≃-sym (SA.S.zeroˡ ν))
    Ex-sumG (suc n) G ν iG e = ≃-trans (Ex-+ {Ω} E (G zero) _ (iG zero) (Int-sum n _ (λ i → iG (suc i))))
      (≃-trans (+S-cong (e zero) (Ex-sumG n (λ i → G (suc i)) ν (λ i → iG (suc i)) (λ i → e (suc i))))
        (SA.plus1 (natS n) ν))

    Ex-sum : ∀ n F μ σ² (M : Moments P n F μ σ²) →
      Ex {Ω} (ιPre {Ω} P) (sumT n F) (Int-sum n F (λ i → proj₁ (proj₁ M i))) ≃ natS n *S μ
    Ex-sum n F μ σ² M = Ex-sumG n F μ (λ i → proj₁ (proj₁ M i)) (λ i → proj₁ (proj₂ M) i)

    -- the cross terms h Σⱼ Gⱼ
    crossS : ∀ n (h : SgT Ω) (G : Fin n → SgT Ω) m →
      (∀ j → Σ (Int {Ω} E (h *T G j)) (λ k → Ex {Ω} E (h *T G j) k ≃ m)) →
      Σ (Int {Ω} E (h *T sumT n G)) (λ k → Ex {Ω} E (h *T sumT n G) k ≃ natS n *S m)
    crossS zero h G m H = Int-via {Ω} E _ (constT 0S) (Int-const {Ω} P 0S) (zero-sums h) ,
      ≃-trans (Ex-cong {Ω} E _ (constT 0S) _ (Int-const {Ω} P 0S) (zero-eq h))
        (≃-trans (Ex-const {Ω} P 0S) (≃-sym (SA.S.zeroˡ m)))
    crossS (suc n) h G m H = Int-via {Ω} E _ _ (Int-+ {Ω} E (proj₁ (H zero)) (proj₁ r)) (dist-sums h (G zero) _) ,
      ≃-trans (Ex-cong {Ω} E _ _ _ (Int-+ {Ω} E (proj₁ (H zero)) (proj₁ r)) (dist-eq h (G zero) _))
        (≃-trans (Ex-+ {Ω} E _ _ (proj₁ (H zero)) (proj₁ r))
          (≃-trans (+S-cong (proj₂ (H zero)) (proj₂ r)) (SA.plus1 (natS n) m)))
      where r = crossS n h (λ i → G (suc i)) m (λ j → H (suc j))

    -- (f + g)² from f², f g and g²
    sqCons : ∀ (f g : SgT Ω) {m} (i₂ : Int {Ω} E (f *T f)) (fg : Σ (Int {Ω} E (f *T g)) (λ k → Ex {Ω} E (f *T g) k ≃ m))
      (ig : Int {Ω} E (g *T g)) → Σ (Int {Ω} E ((f +T g) *T (f +T g))) (λ k →
      Ex {Ω} E ((f +T g) *T (f +T g)) k ≃ (Ex {Ω} E (f *T f) i₂ +S m) +S (m +S Ex {Ω} E (g *T g) ig))
    sqCons f g i₂ fg ig = Int-via {Ω} E _ _ IG (sqadd-sums f g) ,
      ≃-trans (Ex-cong {Ω} E _ _ _ IG (sqadd-eq f g)) (≃-trans (Ex-+ {Ω} E _ _ I₁ I₂)
        (+S-cong (≃-trans (Ex-+ {Ω} E _ _ i₂ (proj₁ fg)) (+S-cong ≃-refl (proj₂ fg)))
                 (≃-trans (Ex-+ {Ω} E _ _ (proj₁ fg) ig) (+S-cong (proj₂ fg) ≃-refl))))
      where I₁ = Int-+ {Ω} E i₂ (proj₁ fg)
            I₂ = Int-+ {Ω} E (proj₁ fg) ig
            IG = Int-+ {Ω} E I₁ I₂

    -- the square of the sum
    sqS : ∀ n F μ σ² (M : Moments P n F μ σ²) → Σ (Int {Ω} E (sumT n F *T sumT n F)) (λ k →
      Ex {Ω} E (sumT n F *T sumT n F) k ≃ natS n *S σ² +S (natS n *S natS n) *S (μ *S μ))
    sqS zero F μ σ² M = Int-via {Ω} E _ (constT 0S) (Int-const {Ω} P 0S) (zero-sums (constT 0S)) ,
      ≃-trans (Ex-cong {Ω} E _ (constT 0S) _ (Int-const {Ω} P 0S) (zero-eq (constT 0S)))
        (≃-trans (Ex-const {Ω} P 0S) (SA.zero-S σ² (μ *S μ)))
    sqS (suc n) F μ σ² M = proj₁ sc , ≃-trans (proj₂ sc) (≃-trans (+S-cong (+S-cong sq₀ ≃-refl) (+S-cong ≃-refl (proj₂ ih)))
        (SA.var-step (natS n) σ² (μ *S μ)))
      where ih = sqS n (λ i → F (suc i)) μ σ² (tailM n F μ σ² M)
            fg = crossS n (F zero) (λ i → F (suc i)) (μ *S μ) (λ j → proj₂ (proj₂ (proj₂ M)) zero (suc j) (λ ()))
            sc = sqCons (F zero) (sumT n (λ i → F (suc i))) (proj₂ (proj₁ M zero)) fg (proj₁ ih)
            sq₀ = proj₁ (proj₂ (proj₂ M)) zero

    -- the variance of the sum
    Int₂-sum : ∀ n F μ σ² → Moments P n F μ σ² → Int₂ {Ω} P (sumT n F)
    Int₂-sum n F μ σ² M = Int-sum n F (λ i → proj₁ (proj₁ M i)) , proj₁ (sqS n F μ σ² M)

    Var-sum : ∀ n F μ σ² (M : Moments P n F μ σ²) → Var {Ω} P (sumT n F) (Int₂-sum n F μ σ² M) ≃ natS n *S σ²
    Var-sum n F μ σ² M = ≃-trans (+S-cong (proj₂ (sqS n F μ σ² M)) (-S-cong (*S-cong es es)))
      (SA.var-final (natS n) σ² μ)
      where es = Ex-sum n F μ σ² M

    -- the sample variance
    Int-ss : ∀ n F μ σ² → Moments P n F μ σ² → Int {Ω} (ιPre {Ω} P) (ssT n F)
    Int-ss n F μ σ² M = Int-+ {Ω} E (Int-scale {Ω} E (natS n) (Int-sum n (λ i → F i *T F i) (λ i → proj₂ (proj₁ M i))))
      (Int-neg {Ω} E (proj₁ (sqS n F μ σ² M)))

    Ex-ss : ∀ n F μ σ² (M : Moments P n F μ σ²) →
      Ex {Ω} (ιPre {Ω} P) (ssT n F) (Int-ss n F μ σ² M) ≃ (natS n *S natS n +S -S natS n) *S σ²
    Ex-ss n F μ σ² M = ≃-trans (Ex-+ {Ω} E _ _ (Int-scale {Ω} E (natS n) iq) (Int-neg {Ω} E (proj₁ sq)))
      (≃-trans (+S-cong (≃-trans (Ex-scale {Ω} E (natS n) _ iq) (*S-congʳ (natS n) eq))
        (≃-trans (Ex-neg {Ω} E _ (proj₁ sq)) (-S-cong (proj₂ sq)))) (SA.ss-final (natS n) σ² (μ *S μ)))
      where iq = Int-sum n (λ i → F i *T F i) (λ i → proj₂ (proj₁ M i))
            sq = sqS n F μ σ² M
            eq = Ex-sumG n (λ i → F i *T F i) (σ² +S μ *S μ) (λ i → proj₂ (proj₁ M i)) (λ i → proj₁ (proj₂ (proj₂ M)) i)
