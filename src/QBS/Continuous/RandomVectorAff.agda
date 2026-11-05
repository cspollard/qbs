{-# OPTIONS --safe --without-K #-}

-- Sums and affine images of random vectors (plan 05, item 52; helper for `RandomVector`, whose definitions of `RV`,
-- `meanV`, `covM`, `affT` it repeats under primed names so that the statements agree by unfolding).
--   * `Int₂-sumV′`, `Var-sumV′`: the sum of the coordinates has finite second moment and Var Σᵢ Xᵢ ≃ Σᵢ Σⱼ Cov(Xᵢ, Xⱼ);
--   * `RV-aff′`, `mean-aff′`, `cov-aff′`: the affine image A X + b is a random vector with mean A mean(X) + b and
--     covariance A Cov(X) Aᵀ; `shiftEx`, `meanLin`, `covLin` are the steps for one pair of rows.
-- Route: `RandomVectorSum.ExBil`/`ExL` expand E[(Σᵢ Aᵢ)(Σⱼ Bⱼ)] and E Σᵢ Gᵢ; `RandomVectorAlg.sh-eq`, `sc-eq` expand
-- (f + c)(g + d) and (c f)(d g); the double-sum arithmetic is `RandomVectorSumRing.var-sum-ring` and `cov-ring`.
module QBS.Continuous.RandomVectorAff where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_; proj₁; proj₂)

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
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.RandomVectorAlg using (module RandomVectorAlg)
open import QBS.Continuous.RandomVectorSum using (module RandomVectorSum)
open import QBS.Continuous.RandomVectorSumRing using (module RSum)

module RandomVectorAff (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; signedRing; ≃-refl; ≃-trans; ≃-sym; +S-cong; -S-cong; *S-cong; +S-assoc)
  open SgLinAlg signedRing using (Vec; Mat; Σ; Σ-cong; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ)
  open SFinite (lemOf lem₁) using (XW; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex; Ex-irr; Ex-cong; Ex-+; Ex-scale; Ex-const; Int-+; Int-scale; Int-const)
  open SignedVar lem₁ using (Int₂; Int₂-shift; Int₂-scale)
  open SgMoments lem₁ using (sumT)
  open SgSample lem₁ using (Int-sum)
  open RandomVectorAlg lem₁ using (comm-eq; sc-eq; sh-eq) renaming (Int-mul to Int-mul′)
  open RandomVectorSum lem₁ using (ExL; ExBil)
  module RS = RSum signedRing

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      E = ιPre {Ω} P

    RV′ : ∀ n → (Fin n → SgT Ω) → Set₁
    RV′ n X = ∀ i → Int₂ {Ω} P (X i)

    mulI : ∀ {f g : SgT Ω} → Int₂ {Ω} P f → Int₂ {Ω} P g → Int {Ω} E (f *T g)
    mulI {f} {g} i j = Int-mul′ {Ω} E f g (proj₂ i) (proj₂ j)

    meanV′ : ∀ n X → RV′ n X → Vec n
    meanV′ n X r i = Ex {Ω} E (X i) (proj₁ (r i))

    covM′ : ∀ n X → RV′ n X → Mat n n
    covM′ n X r i j = Ex {Ω} E (X i *T X j) (mulI (r i) (r j)) +S -S (meanV′ n X r i *S meanV′ n X r j)

    -- the sum
    Int₂-sumV′ : ∀ n X → RV′ n X → Int₂ {Ω} P (sumT n X)
    Int₂-sumV′ n X r = Int-sum {Ω} P n X (λ i → proj₁ (r i)) , proj₁ (ExBil P n n X X (λ i j → mulI (r i) (r j)))

    Var-sumV′ : ∀ n X (r : RV′ n X) →
      Ex {Ω} E (sumT n X *T sumT n X) (proj₂ (Int₂-sumV′ n X r)) +S -S (Ex {Ω} E (sumT n X) (proj₁ (Int₂-sumV′ n X r))
        *S Ex {Ω} E (sumT n X) (proj₁ (Int₂-sumV′ n X r))) ≃ Σ n (λ i → Σ n (λ j → covM′ n X r i j))
    Var-sumV′ n X r = ≃-trans (+S-cong (proj₂ (ExBil P n n X X (λ i j → mulI (r i) (r j))))
      (-S-cong (*S-cong es es))) (≃-sym (RS.var-sum-ring n _ _))
      where es = ExL P n X (λ i → proj₁ (r i))

    -- the affine image
    affT′ : ∀ {m n} → Mat m n → Vec m → (Fin n → SgT Ω) → Fin m → SgT Ω
    affT′ {m} {n} M b X k = sumT n (λ i → scaleT (M k i) (X i)) +T constT (b k)

    scY : ∀ {m n} (M : Mat m n) X → RV′ n X → ∀ k → RV′ n (λ i → scaleT (M k i) (X i))
    scY M X r k i = Int₂-scale {Ω} P (X i) (M k i) (r i)

    iSum : ∀ {m n} (M : Mat m n) X → RV′ n X → ∀ k → Int₂ {Ω} P (sumT n (λ i → scaleT (M k i) (X i)))
    iSum {n = n} M X r k = Int₂-sumV′ n (λ i → scaleT (M k i) (X i)) (scY M X r k)

    RV-aff′ : ∀ {m n} (M : Mat m n) b X → RV′ n X → RV′ m (affT′ M b X)
    RV-aff′ M b X r k = Int₂-shift {Ω} P _ (b k) (iSum M X r k)

    -- the mean of one row
    meanRow : ∀ {m n} (M : Mat m n) b X (r : RV′ n X) k → Ex {Ω} E (affT′ M b X k) (proj₁ (RV-aff′ M b X r k))
      ≃ Σ n (λ i → M k i *S meanV′ n X r i) +S b k
    meanRow {n = n} M b X r k = ≃-trans (Ex-+ {Ω} E _ (constT (b k)) _ (Int-const {Ω} P (b k)))
      (+S-cong (≃-trans (ExL P n _ _) (Σ-cong n (λ i → Ex-scale {Ω} E (M k i) (X i) (proj₁ (r i))))) (Ex-const {Ω} P (b k)))

    mean-aff′ : ∀ {m n} (M : Mat m n) b X (r : RV′ n X) →
      meanV′ m (affT′ M b X) (RV-aff′ M b X r) ≈V (M *Mv meanV′ n X r) +V b
    mean-aff′ = meanRow

    -- E[(f + c)(g + d)] = E f g + (d E f + (c E g + c d))
    shiftEx : ∀ (f g : SgT Ω) c d (i : Int₂ {Ω} P f) (j : Int₂ {Ω} P g) (w : Int {Ω} E ((f +T constT c) *T (g +T constT d))) →
      Ex {Ω} E ((f +T constT c) *T (g +T constT d)) w ≃
        Ex {Ω} E (f *T g) (mulI i j) +S (d *S Ex {Ω} E f (proj₁ i) +S (c *S Ex {Ω} E g (proj₁ j) +S c *S d))
    shiftEx f g c d i j w = ≃-trans (Ex-cong {Ω} E _ _ w IG (sh-eq c d f g)) (≃-trans (Ex-+ {Ω} E _ _ I₁ I₂)
      (≃-trans (+S-cong (≃-trans (Ex-+ {Ω} E _ _ (mulI i j) (Int-scale {Ω} E d (proj₁ i)))
          (+S-cong ≃-refl (Ex-scale {Ω} E d f (proj₁ i))))
        (≃-trans (Ex-+ {Ω} E _ _ (Int-scale {Ω} E c (proj₁ j)) (Int-const {Ω} P (c *S d)))
          (+S-cong (Ex-scale {Ω} E c g (proj₁ j)) (Ex-const {Ω} P (c *S d))))) (+S-assoc _ _ _)))
      where I₁ = Int-+ {Ω} E (mulI i j) (Int-scale {Ω} E d (proj₁ i))
            I₂ = Int-+ {Ω} E (Int-scale {Ω} E c (proj₁ j)) (Int-const {Ω} P (c *S d))
            IG = Int-+ {Ω} E I₁ I₂

    -- E[(c f)(d g)] = c d E f g
    scEx : ∀ c d (f g : SgT Ω) (w : Int {Ω} E (f *T g)) (i : Int {Ω} E (scaleT c f *T scaleT d g)) →
      Ex {Ω} E (scaleT c f *T scaleT d g) i ≃ (c *S d) *S Ex {Ω} E (f *T g) w
    scEx c d f g w i = ≃-trans (Ex-cong {Ω} E _ _ i (Int-scale {Ω} E (c *S d) w) (sc-eq c d f g))
      (Ex-scale {Ω} E (c *S d) (f *T g) w)

    -- the expectation of a row sum
    ExS : ∀ {m n} (M : Mat m n) X (r : RV′ n X) k → Ex {Ω} E (sumT n (λ i → scaleT (M k i) (X i))) (proj₁ (iSum M X r k))
      ≃ Σ n (λ i → M k i *S meanV′ n X r i)
    ExS {n = n} M X r k = ≃-trans (ExL P n _ _) (Σ-cong n (λ i → Ex-scale {Ω} E (M k i) (X i) (proj₁ (r i))))

    -- E (S_k S_l) as a double sum
    ExSS : ∀ {m n} (M : Mat m n) X (r : RV′ n X) k l →
      Ex {Ω} E (sumT n (λ i → scaleT (M k i) (X i)) *T sumT n (λ i → scaleT (M l i) (X i))) (mulI (iSum M X r k) (iSum M X r l))
        ≃ Σ n (λ i → Σ n (λ j → (M k i *S M l j) *S Ex {Ω} E (X i *T X j) (mulI (r i) (r j))))
    ExSS {n = n} M X r k l = ≃-trans (Ex-irr {Ω} E _ _ (proj₁ eb)) (≃-trans (proj₂ eb)
      (Σ-cong n (λ i → Σ-cong n (λ j → scEx (M k i) (M l j) (X i) (X j) (mulI (r i) (r j)) (iAB i j)))))
      where iAB = λ i j → mulI (scY M X r k i) (scY M X r l j)
            eb = ExBil P n n (λ i → scaleT (M k i) (X i)) (λ j → scaleT (M l j) (X j)) iAB

    covRow : ∀ {m n} (M : Mat m n) b X (r : RV′ n X) k l → Ex {Ω} E (affT′ M b X k *T affT′ M b X l)
      (mulI (RV-aff′ M b X r k) (RV-aff′ M b X r l)) ≃
        Σ n (λ i → Σ n (λ j → (M k i *S M l j) *S Ex {Ω} E (X i *T X j) (mulI (r i) (r j))))
        +S (b l *S Σ n (λ i → M k i *S meanV′ n X r i) +S (b k *S Σ n (λ j → M l j *S meanV′ n X r j) +S b k *S b l))
    covRow M b X r k l = ≃-trans (shiftEx _ _ (b k) (b l) (iSum M X r k) (iSum M X r l) _)
      (+S-cong (ExSS M X r k l) (+S-cong (*S-cong ≃-refl (ExS M X r k)) (+S-cong (*S-cong ≃-refl (ExS M X r l)) ≃-refl)))

    cov-aff′ : ∀ {m n} (M : Mat m n) b X (r : RV′ n X) →
      covM′ m (affT′ M b X) (RV-aff′ M b X r) ≈M (M *M covM′ n X r) *M (M ᵀ)
    cov-aff′ {n = n} M b X r k l = ≃-trans (+S-cong (covRow M b X r k l)
      (-S-cong (*S-cong (meanRow M b X r k) (meanRow M b X r l))))
      (RS.cov-ring n (M k) (M l) (λ i j → Ex {Ω} E (X i *T X j) (mulI (r i) (r j))) (meanV′ n X r) (b k) (b l))
