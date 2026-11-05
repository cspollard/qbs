{-# OPTIONS --safe --without-K #-}

-- The law of a Gaussian vector as a measure on RQᵐ (plan 05, item 55).  On a probability P on Ω:
--   * `coordT n i = idT ∘ projᵢ`, the coordinates on RQⁿ, and the law of A Z + b for any map Z : Ω ⇒ RQⁿ whose coordinates
--     form a random vector (`affLaw`, the push-forward along `RQArith.affRH A b ∘ Z`): its coordinates are a random vector
--     (`affLaw-RV`) with mean A mean(Z) + b (`affLaw-mean`) and covariance A Cov(Z) Aᵀ (`affLaw-cov`), the affine rule of
--     `RandomVector` (`mean-aff`, `cov-aff`) read on the law;
--   * the Gaussian N(b, A Aᵀ) = `Nᴬ A b`, the law of A Z + b under Z ∼ N(0, Iₙ) (`GaussVector.Nⁿ`, Z the identity of RQⁿ): a
--     probability measure on RQᵐ (`Nᴬ-mass`) whose coordinates have mean b and covariance A Aᵀ (`Nᴬ-RV`, `Nᴬ-mean`,
--     `Nᴬ-cov`), matching `GaussVector.gaussV-mean`/`gaussV-cov`, which compute the same moments on the Ω side.
-- Route: `affLaw-*`: `RandomVectorLaw.RV-law`, `mean-law`, `cov-law` at h = affRH A b ∘ Z and X = coordT m, then
-- `RQArith.idT-affRH` (≐ is symmetric) with `RandomVectorLaw.RV-≐` (coordT is a pull-back of `idT`), `mean-≐`, `cov-≐`
-- to replace the coordinates by `affT`, and `RandomVector.RV-aff`, `mean-aff`, `cov-aff`.  `Nᴬ-*` are `affLaw-*` at
-- Z = idH, P = Nⁿ n, with `GaussVector.std-mean`, `std-cov` for the moments of Z and `SgLinAlg.*Mv-0`, `*M-idM`, as in
-- `GaussVector.gaussV-mean`/`gaussV-cov`; `Nᴬ-mass` is `ProdBridge.ι-mass`.
--   Skeleton: holes first.
module QBS.Inference.GaussVectorLaw where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

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
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Continuous.RQArith using (module RQArith)
open import QBS.Inference.GaussVector using (module GaussVector)

module GaussVectorLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Bounded A using (signedRing)
  open SgLinAlg signedRing using (Vec; Mat; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open SignedTest lem₁ using (SgT; _∘T_; idT)
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
