{-# OPTIONS --safe --without-K #-}

-- Expectations of sums and of products of sums of signed tests (plan 05, item 52; helper for `RandomVector`).  For a
-- probability P on Ω and tests with the stated integrable products:
--   * `ExL`: E Σᵢ Gᵢ ≃ Σᵢ E Gᵢ (sums of `SgLinAlg`);
--   * `ExR`: h Σⱼ Gⱼ is integrable and E (h Σⱼ Gⱼ) ≃ Σⱼ E (h Gⱼ);
--   * `ExBil`: (Σᵢ Aᵢ)(Σⱼ Bⱼ) is integrable and E[(Σᵢ Aᵢ)(Σⱼ Bⱼ)] ≃ Σᵢ Σⱼ E (Aᵢ Bⱼ).
-- Route: induction on the length with `Ex-+`, `SgSampleAlg.dist-eq`; `ExBil` applies `ExR` twice, commuting factors
-- (`RandomVectorAlg.comm-eq`) and swapping the double sum (`SgLinAlg.Σ-swap`).
module QBS.Continuous.RandomVectorSum where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂) renaming (Σ to Sig)

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
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.SgSampleAlg using (module SgSampleAlg)
open import QBS.Continuous.RandomVectorAlg using (module RandomVectorAlg)

module RandomVectorSum (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; 0S; signedRing; ≃-refl; ≃-trans; ≃-sym; +S-cong)
  open SgLinAlg signedRing using (Σ; Σ-cong; Σ-swap)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; constT)
  open SignedExpect lem₁ using (Int; Ex; Ex-cong; Ex-+; Ex-const; Int-+; Int-const)
  open SignedVarAlg lem₁ using (Int-via)
  open SgMoments lem₁ using (sumT)
  open SgSample lem₁ using (Int-sum)
  open SgSampleAlg lem₁ using (dist-eq; dist-sums; zero-eq; zero-sums)
  open RandomVectorAlg lem₁ using (comm-eq; comm-sums)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    Int-comm : ∀ {f g : SgT Ω} → Int {Ω} E (f *T g) → Int {Ω} E (g *T f)
    Int-comm {f} {g} i = Int-via {Ω} E (g *T f) (f *T g) i (λ x → comm-sums g f x)

    ExL : ∀ n (G : Fin n → SgT Ω) (iG : ∀ i → Int {Ω} E (G i)) →
      Ex {Ω} E (sumT n G) (Int-sum {Ω} P n G iG) ≃ Σ n (λ i → Ex {Ω} E (G i) (iG i))
    ExL zero G iG = Ex-const {Ω} P 0S
    ExL (suc n) G iG = ≃-trans (Ex-+ {Ω} E (G zero) _ (iG zero) (Int-sum {Ω} P n _ (λ i → iG (suc i))))
      (+S-cong ≃-refl (ExL n (λ i → G (suc i)) (λ i → iG (suc i))))

    ExR : ∀ n (h : SgT Ω) (G : Fin n → SgT Ω) (iG : ∀ j → Int {Ω} E (h *T G j)) →
      Sig (Int {Ω} E (h *T sumT n G)) (λ k → Ex {Ω} E (h *T sumT n G) k ≃ Σ n (λ j → Ex {Ω} E (h *T G j) (iG j)))
    ExR zero h G iG = Int-via {Ω} E _ (constT 0S) (Int-const {Ω} P 0S) (zero-sums h) ,
      ≃-trans (Ex-cong {Ω} E _ (constT 0S) _ (Int-const {Ω} P 0S) (zero-eq h)) (Ex-const {Ω} P 0S)
    ExR (suc n) h G iG = Int-via {Ω} E _ _ (Int-+ {Ω} E (iG zero) (proj₁ r)) (dist-sums h (G zero) _) ,
      ≃-trans (Ex-cong {Ω} E _ _ _ (Int-+ {Ω} E (iG zero) (proj₁ r)) (dist-eq h (G zero) _))
        (≃-trans (Ex-+ {Ω} E _ _ (iG zero) (proj₁ r)) (+S-cong ≃-refl (proj₂ r)))
      where r = ExR n h (λ i → G (suc i)) (λ j → iG (suc j))

    ExBil : ∀ n p (A : Fin n → SgT Ω) (B : Fin p → SgT Ω) (iAB : ∀ i j → Int {Ω} E (A i *T B j)) →
      Sig (Int {Ω} E (sumT n A *T sumT p B)) (λ k →
        Ex {Ω} E (sumT n A *T sumT p B) k ≃ Σ n (λ i → Σ p (λ j → Ex {Ω} E (A i *T B j) (iAB i j))))
    ExBil n p A B iAB = proj₁ rS , ≃-trans (proj₂ rS) (≃-trans (Σ-cong p inner) (Σ-swap p n _))
      where
        rB : ∀ j → _
        rB j = ExR n (B j) A (λ i → Int-comm {A i} {B j} (iAB i j))
        iSB : ∀ j → Int {Ω} E (sumT n A *T B j)
        iSB j = Int-comm {B j} {sumT n A} (proj₁ (rB j))
        rS = ExR p (sumT n A) B iSB
        inner : ∀ j → Ex {Ω} E (sumT n A *T B j) (iSB j) ≃ Σ n (λ i → Ex {Ω} E (A i *T B j) (iAB i j))
        inner j = ≃-trans (Ex-cong {Ω} E _ _ (iSB j) (proj₁ (rB j)) (comm-eq (sumT n A) (B j)))
          (≃-trans (proj₂ (rB j)) (Σ-cong n (λ i → Ex-cong {Ω} E _ _ _ (iAB i j) (comm-eq (B j) (A i)))))
