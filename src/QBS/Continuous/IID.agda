{-# OPTIONS --safe --without-K #-}

-- Independent and identically distributed families (plan 05, item 46).  On a probability P on Ω, for an s-finite
-- measure μ on Y (a probability law in the theorems: ∫ 1 dμ ≈ 1):
--   * `IID μ n Xs`: the law of the tuple (X₀, …, X_{n−1}) is ≈ᴹ μ^{⊗n} (`FinProd.prodⁿ`); `IIDSeq μ Xs`: every finite
--     prefix of a sequence is iid;
--   * each Xᵢ has law μ (`IID-law`), and the family is mutually independent (`IID-indep`, `Independence.Indep`);
--   * functions of an iid family are iid, with the push-forward law (`IID-map`);
--   * for a signed test f with ∫ f, ∫ f² finite under μ, the observations f ∘ Xᵢ satisfy `SgMoments.Moments` with the
--     mean and variance of f under μ (`IID-moments`); `Continuous/SgSample` then gives the unbiased sample mean and
--     sample variance for every iid family.
-- Route: `IID-law` from `FinProd.margⁿ` with `ProdMap.mapM-comp` and `FinProd.proj-tuple`; `IID-indep` is
-- `FinProd.prodⁿ-cong` with `IID-law`; `IID-map` from `mapM-comp` and push-forward of `prodⁿ` along the coordinatewise
-- map (by induction on n, `ProdMap.map-prod`); `IID-moments` transports integrals along the law
-- (`SignedTransport.Int-map`, `Ex-map`) and uses `Independence.Indep-pair`, `Int-indep`, `Ex-indep` for i ≢ j.
--   Skeleton: holes first.
module QBS.Continuous.IID where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin; toℕ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.SgMoments using (module SgMoments)

module IID (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Bounded A using (Sg; _≃_; _+S_; _*S_)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open SignedTest lem₁ using (SgT; _∘T_; _*T_)
  open SignedExpect lem₁ using (Int; Ex)
  open FinProd lem₁ using (ΠQ; tupleQ; prodⁿ)
  open Independence lem₁ using (law; Indep)
  open SgMoments lem₁ using (Moments)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    IID : ∀ {Y : QBS S} → C.Pre (XW Y) → ∀ n → (Fin n → Hom S Ω Y) → Set₁
    IID {Y} μ n Xs = _≈ᴹ_ {ΠQ n (λ _ → Y)} (law P (tupleQ n (λ _ → Y) Xs)) (prodⁿ n (λ _ → Y) (λ _ → μ))

    IIDSeq : ∀ {Y : QBS S} → C.Pre (XW Y) → (ℕ → Hom S Ω Y) → Set₁
    IIDSeq μ Xs = ∀ n → IID μ n (λ i → Xs (toℕ i))

    -- identically distributed, and mutually independent
    IID-law : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID μ n Xs → ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# →
      ∀ i → _≈ᴹ_ {Y} (law P (Xs i)) μ
    IID-law = ?

    IID-indep : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID μ n Xs → ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# →
      Indep P n (λ _ → Y) Xs
    IID-indep = ?

    -- functions of an iid family
    IID-map : ∀ {Y Z : QBS S} (μ : C.Pre (XW Y)) n Xs (f : Hom S Y Z) → IID μ n Xs →
      IID (mapM {Y} {Z} f μ) n (λ i → _∘H_ S f (Xs i))
    IID-map = ?

    -- the observations of a signed test satisfy the moment hypotheses
    IID-moments : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs (f : SgT Y) (m s : Sg) → IID μ n Xs →
      ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1# → (i : Int {Y} μ f) (j : Int {Y} μ (f *T f)) → Ex {Y} μ f i ≃ m →
      Ex {Y} μ (f *T f) j ≃ s +S m *S m → Moments P n (λ k → f ∘T Xs k) m s
    IID-moments = ?
