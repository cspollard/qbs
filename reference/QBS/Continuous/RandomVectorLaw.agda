{-# OPTIONS --safe --without-K #-}

-- Random vectors and their laws (used by `Inference/GaussVectorLaw`).  On a probability P on Ω:
--   * products of signed tests respect `_≐_`, including infinite values (`mul-cong`, as `SignedSq.sq-cong` for squares);
--   * the moment data of a random vector depend on the tests only up to `_≐_` (`mean-≐`, `cov-≐`, given both witnesses),
--     and ≐ transfers the random-vector property onto tests with one part zero at each point, such as pull-backs of
--     `idT` (`RV-≐`; ≐ alone does not, since (∞, ∞) ≐ anything);
--   * push-forward principle: for h : Ω ⇒ Y the law `mapPre h P` has the expectations of the composite tests (`Int-law`,
--     `Ex-law`), so a family X of tests on Y is a random vector under the law as soon as X ∘ h is one under P (`RV-law`),
--     with the same mean vector and covariance matrix (`mean-law`, `cov-law`).
-- Route: `mul-cong` is `SignedMul.mul-cong` (as `SignedSq.sq-alg`, but a zero factor can kill an infinite one, so
-- the infinite cases are ∞·s plus a remainder, with `TopMulPos.top-pos`); `RV-≐` from `GaussVarAux.Int-norm` at Y i and
-- at (Y i)² (one part zero again, ≐ by `SignedSq.sq-cong`); `mean-≐`, `cov-≐` from `SignedExpect.Ex-cong`, covariances
-- at the products by `mul-cong`.  `Int-law`, `Ex-law` are `RandomVectorLawAux` (`SFiniteIncl.ι-nat` and
-- `SFinite.∫ᴹ-map`, as `GaussVarAux.∫-map` on the real line, then `bnd≈` and `mk≃`); `RV-law` and the moments from them
-- at the tests X i and X i *T X j, using (X i ∘T h) *T (X j ∘T h) = (X i *T X j) ∘T h pointwise (`refl`).
module QBS.Continuous.RandomVectorLaw where

open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (_⊎_; inj₁)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Continuous.SignedSq using (module SignedSq)
open import QBS.Continuous.SignedMul using (module SignedMul)
open import QBS.Continuous.RandomVectorLawAux using (module RandomVectorLawAux)
open import QBS.Inference.GaussVarAux using (module GaussVarAux)

module RandomVectorLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#; refl)
  open Bounded A using (_≃_; ≃-trans; signedRing; +S-cong; -S-cong; *S-cong; _+S_; -S_; _*S_)
  open SgLinAlg signedRing using (_≈V_; _≈M_)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _≐_; _∘T_; _*T_; at⁺; at⁻; ≐-sym)
  open SignedExpect lem₁ using (Int; Ex; Ex-irr; Ex-cong)
  open SignedSq lem₁ using (sq-cong)
  open GaussVarAux lem₁ using (Int-norm; sqz)
  module SM = SignedMul lem₁
  module LA = RandomVectorLawAux lem₁
  open RandomVector lem₁ using (RV; meanV; covM)

  ----------------------------------------------------------------------------
  -- moments depend on the tests only up to ≐

  -- products respect ≐, including infinite values
  mul-cong : ∀ {X : QBS S} {f g f′ g′ : SgT X} → f ≐ g → f′ ≐ g′ → (f *T f′) ≐ (g *T g′)
  mul-cong = SM.mul-cong

  module _ {Ω : QBS S} (P : C.Pre Ω) {n} {X Y : Fin n → SgT Ω} (e : ∀ i → X i ≐ Y i) where

    -- ≐ alone does not transfer integrability ((∞, ∞) ≐ anything); it does onto tests with one part zero
    RV-≐ : (∀ i x → at⁻ (Y i) x ≈ 0# ⊎ at⁺ (Y i) x ≈ 0#) → RV P n X → RV P n Y
    RV-≐ z r i = Int-norm {Ω} (ιPre {Ω} P) (Y i) (X i) (proj₁ (r i)) (≐-sym (e i)) (z i) ,
      Int-norm {Ω} (ιPre {Ω} P) (Y i *T Y i) (X i *T X i) (proj₂ (r i)) (sq-cong (≐-sym (e i)))
        (λ x → inj₁ (sqz (z i x)))

    mean-≐ : ∀ r r′ → meanV P n X r ≈V meanV P n Y r′
    mean-≐ r r′ i = Ex-cong {Ω} (ιPre {Ω} P) (X i) (Y i) (proj₁ (r i)) (proj₁ (r′ i)) (e i)

    cov-≐ : ∀ r r′ → covM P n X r ≈M covM P n Y r′
    cov-≐ r r′ i j = +S-cong (Ex-cong {Ω} (ιPre {Ω} P) (X i *T X j) (Y i *T Y j) _ _ (mul-cong (e i) (e j)))
      (-S-cong (*S-cong (mean-≐ r r′ i) (mean-≐ r r′ j)))

  ----------------------------------------------------------------------------
  -- the push-forward principle

  module _ {Ω Y : QBS S} (P : C.Pre Ω) (h : Hom S Ω Y) where

    Int-law : ∀ f → Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f → Int {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h)
    Int-law = LA.Int-law P h

    Ex-law : ∀ f (i : Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f) →
      Ex {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f i ≃ Ex {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h) (Int-law f i)
    Ex-law = LA.Ex-law P h

    -- a family of tests on Y is a random vector under the law as soon as its pull-back is one under P
    RV-law : ∀ n (X : Fin n → SgT Y) → RV P n (λ i → _∘T_ {Ω} {Y} (X i) h) → RV (C.mapPre {Ω} {Y} h P) n X
    RV-law n X r i = LA.Int-law⁻ P h (X i) (proj₁ (r i)) , LA.Int-law⁻ P h (X i *T X i) (proj₂ (r i))

    mean-law : ∀ n X (r : RV P n (λ i → _∘T_ {Ω} {Y} (X i) h)) →
      meanV (C.mapPre {Ω} {Y} h P) n X (RV-law n X r) ≈V meanV P n (λ i → _∘T_ {Ω} {Y} (X i) h) r
    mean-law n X r i = ≃-trans (Ex-law (X i) _) (Ex-irr {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} (X i) h) _ _)

    cov-law : ∀ n X (r : RV P n (λ i → _∘T_ {Ω} {Y} (X i) h)) →
      covM (C.mapPre {Ω} {Y} h P) n X (RV-law n X r) ≈M covM P n (λ i → _∘T_ {Ω} {Y} (X i) h) r
    cov-law n X r i j = +S-cong (≃-trans (Ex-law (X i *T X j) _)
      (Ex-cong {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} (X i *T X j) h)
        (_∘T_ {Ω} {Y} (X i) h *T _∘T_ {Ω} {Y} (X j) h) _ _ (λ x → refl)))
      (-S-cong (*S-cong (mean-law n X r i) (mean-law n X r j)))
