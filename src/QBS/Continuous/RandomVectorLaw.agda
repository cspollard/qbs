{-# OPTIONS --safe --without-K #-}

-- Random vectors and their laws (plan 05, item 55a; enabler for `Inference/GaussVectorLaw`).  On a probability P on Ω:
--   * products of signed tests respect `_≐_`, including infinite values (`mul-cong`, as `SignedSq.sq-cong` for squares);
--   * the moment data of a random vector depend on the tests only up to `_≐_` (`mean-≐`, `cov-≐`, given both witnesses),
--     and ≐ transfers the random-vector property onto tests with one part zero at each point, such as pull-backs of
--     `idT` (`RV-≐`; ≐ alone does not, since (∞, ∞) ≐ anything);
--   * push-forward principle: for h : Ω ⇒ Y the law `mapPre h P` has the expectations of the composite tests (`Int-law`,
--     `Ex-law`), so a family X of tests on Y is a random vector under the law as soon as X ∘ h is one under P (`RV-law`),
--     with the same mean vector and covariance matrix (`mean-law`, `cov-law`).
-- Route: `mul-cong` as `SignedSq.sq-alg` (all four values bounded: cancel; otherwise excluded middle on `Bnd` and
-- `top-mul`); `RV-≐` from `GaussVarAux.Int-norm` at Y i and at (Y i)² (one part zero again, ≐ by `SignedSq.sq-cong`);
-- `mean-≐`, `cov-≐` from `SignedExpect.Ex-cong`, covariances at the products by `mul-cong`.  `Int-law`, `Ex-law` from
-- `ProdBridge.ι-map` (ιPre (mapPre h P) ≈ᴹ mapM h (ιPre P)) with `SignedTransport.Int-map`, `Int-unmap`, `Ex-map` (`bnd≈`
-- to move along ≈ᴹ; `Ex` unfolds to ∫ᴹ pos − ∫ᴹ neg); `RV-law` and the moments from them at the tests X i and
-- X i *T X j, using (X i ∘T h) *T (X j ∘T h) ≐ (X i *T X j) ∘T h pointwise.
--   Skeleton: holes first.
module QBS.Continuous.RandomVectorLaw where

open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (_⊎_)

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

module RandomVectorLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#)
  open Bounded A using (_≃_; signedRing)
  open SgLinAlg signedRing using (_≈V_; _≈M_)
  open SFinite (lemOf lem₁) using (module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _≐_; _∘T_; _*T_; at⁺; at⁻)
  open SignedExpect lem₁ using (Int; Ex)
  open RandomVector lem₁ using (RV; meanV; covM)

  ----------------------------------------------------------------------------
  -- moments depend on the tests only up to ≐

  -- products respect ≐, including infinite values
  mul-cong : ∀ {X : QBS S} {f g f′ g′ : SgT X} → f ≐ g → f′ ≐ g′ → (f *T f′) ≐ (g *T g′)
  mul-cong = ?

  module _ {Ω : QBS S} (P : C.Pre Ω) {n} {X Y : Fin n → SgT Ω} (e : ∀ i → X i ≐ Y i) where

    -- ≐ alone does not transfer integrability ((∞, ∞) ≐ anything); it does onto tests with one part zero
    RV-≐ : (∀ i x → at⁻ (Y i) x ≈ 0# ⊎ at⁺ (Y i) x ≈ 0#) → RV P n X → RV P n Y
    RV-≐ = ?

    mean-≐ : ∀ r r′ → meanV P n X r ≈V meanV P n Y r′
    mean-≐ = ?

    cov-≐ : ∀ r r′ → covM P n X r ≈M covM P n Y r′
    cov-≐ = ?

  ----------------------------------------------------------------------------
  -- the push-forward principle

  module _ {Ω Y : QBS S} (P : C.Pre Ω) (h : Hom S Ω Y) where

    Int-law : ∀ f → Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f → Int {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h)
    Int-law = ?

    Ex-law : ∀ f (i : Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f) →
      Ex {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f i ≃ Ex {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h) (Int-law f i)
    Ex-law = ?

    -- a family of tests on Y is a random vector under the law as soon as its pull-back is one under P
    RV-law : ∀ n (X : Fin n → SgT Y) → RV P n (λ i → _∘T_ {Ω} {Y} (X i) h) → RV (C.mapPre {Ω} {Y} h P) n X
    RV-law = ?

    mean-law : ∀ n X (r : RV P n (λ i → _∘T_ {Ω} {Y} (X i) h)) →
      meanV (C.mapPre {Ω} {Y} h P) n X (RV-law n X r) ≈V meanV P n (λ i → _∘T_ {Ω} {Y} (X i) h) r
    mean-law = ?

    cov-law : ∀ n X (r : RV P n (λ i → _∘T_ {Ω} {Y} (X i) h)) →
      covM (C.mapPre {Ω} {Y} h P) n X (RV-law n X r) ≈M covM P n (λ i → _∘T_ {Ω} {Y} (X i) h) r
    cov-law = ?
