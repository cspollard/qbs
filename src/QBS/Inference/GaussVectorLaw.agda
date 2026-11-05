{-# OPTIONS --safe --without-K #-}

-- The law of a Gaussian vector as a measure on RQᵐ (plan 05, item 55).  On a probability P on Ω:
--   * push-forward principle for random vectors: for h : Ω ⇒ Y the law `mapPre h P` has the expectations of the composite
--     tests (`Int-law`, `Ex-law`), so a family X of tests on Y is a random vector under the law as soon as X ∘ h is one under
--     P (`RV-law`), with the same mean vector and covariance matrix (`mean-law`, `cov-law`); the moment data depend on the
--     tests only up to `_≐_` (`RV-≐`, `mean-≐`, `cov-≐`);
--   * `coordT n i = idT ∘ projᵢ`, the coordinates on RQⁿ, and the law of A Z + b for any map Z : Ω ⇒ RQⁿ whose coordinates
--     form a random vector (`affLaw`, the push-forward along `RQArith.affRH A b ∘ Z`): its coordinates are a random vector
--     (`affLaw-RV`) with mean A mean(Z) + b (`affLaw-mean`) and covariance A Cov(Z) Aᵀ (`affLaw-cov`), the affine rule of
--     `RandomVector` (`mean-aff`, `cov-aff`) read on the law;
--   * the Gaussian N(b, A Aᵀ) = `Nᴬ A b`, the law of A Z + b under Z ∼ N(0, Iₙ) (`GaussVector.Nⁿ`, Z the identity of RQⁿ): a
--     probability measure on RQᵐ (`Nᴬ-mass`) whose coordinates have mean b and covariance A Aᵀ (`Nᴬ-RV`, `Nᴬ-mean`,
--     `Nᴬ-cov`), matching `GaussVector.gaussV-mean`/`gaussV-cov`, which compute the same moments on the Ω side.
-- Route: `Int-law`, `Ex-law` from `ProdBridge.ι-map` (ιPre (mapPre h P) ≈ᴹ mapM h (ιPre P)) with `SignedTransport.Int-map`,
-- `Int-unmap`, `Ex-map` (`bnd≈` to move along ≈ᴹ; `Ex` unfolds to ∫ᴹ pos − ∫ᴹ neg); `RV-law` and the moments from them at the
-- tests X i and (X i)², using (X i ∘T h) *T (X i ∘T h) ≐ (X i *T X i) ∘T h pointwise; `RV-≐`, `mean-≐`, `cov-≐` from
-- `SignedExpect.Ex-cong` and `Int-dom` (≐ gives two-sided domination), covariances through `Ex-cong` at the products.
-- `affLaw-*`: `mean-law`, `cov-law` at h = affRH A b ∘ Z and X = coordT m, then `RQArith.idT-affRH` with `RV-≐`, `mean-≐`,
-- `cov-≐` to replace the coordinates by `affT`, and `RandomVector.RV-aff`, `mean-aff`, `cov-aff`.  `Nᴬ-*` are `affLaw-*` at
-- Z = idH, P = Nⁿ n, with `GaussVector.std-mean`, `std-cov` for the moments of Z and `SgLinAlg.*Mv-0`, `*M-idM`, as in
-- `GaussVector.gaussV-mean`/`gaussV-cov`; `Nᴬ-mass` is `ProdBridge.ι-mass`.
--   Skeleton: holes first.
module QBS.Inference.GaussVectorLaw where

open import Algebra using (CommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Continuous.RQArith using (module RQArith)
open import QBS.Inference.GaussVector using (module GaussVector)

module GaussVectorLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Bounded A using (Sg; _≃_; signedRing)
  open SgLinAlg signedRing using (Vec; Mat; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open SignedTest lem₁ using (SgT; _≐_; _∘T_; idT)
  open SignedExpect lem₁ using (Int; Ex)
  open FinProd lem₁ using (ΠQ; projQ)
  open ProdBridge lem₁ using (ι-mass)
  open RandomVector lem₁ using (RV; meanV; covM)
  open RQArith lem₁ using (RQⁿ; affRH)
  open GaussVector lem₁ using (Nⁿ)
  open QBS
  open Hom

  -- the coordinates idT ∘ projᵢ on RQⁿ
  coordT : ∀ n → Fin n → SgT (RQⁿ n)
  coordT n i = _∘T_ {RQⁿ n} {RQ} idT (projQ n (λ _ → RQ) i)

  ----------------------------------------------------------------------------
  -- moments depend on the tests only up to ≐

  module _ {Ω : QBS S} (P : C.Pre Ω) {n} {X Y : Fin n → SgT Ω} (e : ∀ i → X i ≐ Y i) where

    RV-≐ : RV P n X → RV P n Y
    RV-≐ = ?

    mean-≐ : ∀ r → meanV P n X r ≈V meanV P n Y (RV-≐ r)
    mean-≐ = ?

    cov-≐ : ∀ r → covM P n X r ≈M covM P n Y (RV-≐ r)
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

  ----------------------------------------------------------------------------
  -- the law of A Z + b on RQᵐ

  module _ {Ω : QBS S} (P : C.Pre Ω) {m n} (M : Mat m n) (b : Vec m) (Z : Hom S Ω (RQⁿ n))
    (r : RV P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z)) where

    affLaw : C.Pre (RQⁿ m)
    affLaw = C.mapPre {Ω} {RQⁿ m} (_∘H_ S (affRH M b) Z) P

    affLaw-RV : RV affLaw m (coordT m)
    affLaw-RV = ?

    affLaw-mean : meanV affLaw m (coordT m) affLaw-RV ≈V (M *Mv meanV P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z) r) +V b
    affLaw-mean = ?

    affLaw-cov : covM affLaw m (coordT m) affLaw-RV ≈M (M *M covM P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z) r) *M (M ᵀ)
    affLaw-cov = ?

  ----------------------------------------------------------------------------
  -- the Gaussian N(b, A Aᵀ)

  -- the law of A Z + b for Z ∼ N(0, Iₙ), a probability measure on RQᵐ
  Nᴬ : ∀ {m n} → Mat m n → Vec m → C.Pre (RQⁿ m)
  Nᴬ {m} {n} M b = C.mapPre {RQⁿ n} {RQⁿ m} (affRH M b) (Nⁿ n)

  Nᴬ-mass : ∀ {m n} (M : Mat m n) b → ∫ᴹ {RQⁿ m} (ιPre {RQⁿ m} (Nᴬ M b)) (constW {RQⁿ m} 1#) ≈ 1#
  Nᴬ-mass {m} {n} M b = ι-mass {RQⁿ m} (Nᴬ M b)

  Nᴬ-RV : ∀ {m n} (M : Mat m n) b → RV (Nᴬ M b) m (coordT m)
  Nᴬ-RV = ?

  Nᴬ-mean : ∀ {m n} (M : Mat m n) b → meanV (Nᴬ M b) m (coordT m) (Nᴬ-RV M b) ≈V b
  Nᴬ-mean = ?

  Nᴬ-cov : ∀ {m n} (M : Mat m n) b → covM (Nᴬ M b) m (coordT m) (Nᴬ-RV M b) ≈M M *M (M ᵀ)
  Nᴬ-cov = ?
