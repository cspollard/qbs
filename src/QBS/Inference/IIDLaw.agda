{-# OPTIONS --safe --without-K #-}

-- Moments of sums of iid draws: E Sₙ = n m, Var Sₙ = n s (plan 05 item 46b in `plans/`).  On a probability P on Ω, for an iid family
-- Xs : Fin n → Ω ⇒ Y with law μ (`Continuous/IID`) and a signed test f with ∫ f ≃ m and ∫ f² ≃ s + m² under μ, the
-- observations f ∘ Xᵢ (`obs`) satisfy the moment hypotheses (`mom`, which is `IID.IID-moments`), so:
--   * E Sₙ ≃ n m (`iid-mean`), Var Sₙ ≃ n s (`iid-var`), E (n Qₙ − Sₙ²) ≃ (n² − n) s (`iid-ss`);
--   * the weak law in rate form, n ε² P{(Sₙ − n m)² ≥ (n ε)²} ≤ s for n ≥ 1 (`iid-weak-law`; `devS` is (Sₙ − n m)²).
-- For a sampler s : Θ × ℛ ⇒ X and θ, the draws at the coin coordinates are iid with the law of one draw
-- (`CoinCoordsJoint.draws-iid`), which has mass 1 (`draw-mass`), so the same holds for the samplers' observations
-- (`draws-mean`, `draws-weak-law`).
-- Route: `SgSample.Ex-sum`, `Var-sum`, `Ex-ss` and `WeakLaw.weak-law-rate` applied to `mom`; `draw-mass` from
-- `SFinite.∫ᴹ-map` and `ProdBridge.ι-mass`.
module QBS.Inference.IIDLaw where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Product.Base using (proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.IID using (module IID)
open import QBS.Continuous.CoinCoordsJoint using (module CoinCoordsJoint)
open import QBS.Inference.Sampler using (module Sampler)
open import QBS.Inference.WeakLaw using (module WeakLaw)
open import QBS.Continuous.ProdBridge using (module ProdBridge)

module IIDLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 1#; refl; trans)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; nat)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; mapM; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _∘T_; _*T_; at⁺; at⁻)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Var)
  open SgMoments lem₁ using (natS; sumT; ssT; Moments)
  open SgSample lem₁ using (Int-sum; Int₂-sum; Int-ss; Ex-sum; Var-sum; Ex-ss)
  open ProdBridge lem₁ using (ι-mass)
  open IID lem₁ using (IID; IID-moments)
  open CoinCoordsJoint lem₁ using (ℛ; coinPre; coin; coordH; drawH; draws-iid)
  open Sampler lem₁ using () renaming (Sampler to SamplerQ)
  open WeakLaw lem₁ using (_≤ᵛ_; dev; weak-law-rate)
  open QBS
  open Hom

  -- the observations f ∘ Xᵢ
  obs : ∀ {Ω Y : QBS S} → SgT Y → ∀ n → (Fin n → Hom S Ω Y) → Fin n → SgT Ω
  obs f n Xs k = f ∘T Xs k

  -- (Sₙ − n m)², the squared deviation of the sum
  devS : ∀ {Ω Y : QBS S} → C.Pre Ω → SgT Y → Sg → ∀ n → (Fin n → Hom S Ω Y) → SgT Ω
  devS P f m n Xs = dev P (sumT n (obs f n Xs)) (natS n *S m)

  module _ {Ω : QBS S} (P : C.Pre Ω) {Y : QBS S} (μ : C.Pre (XW Y)) (h : ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1#)
    (f : SgT Y) (m s : Sg) (i : Int {Y} μ f) (j : Int {Y} μ (f *T f))
    (em : Ex {Y} μ f i ≃ m) (es : Ex {Y} μ (f *T f) j ≃ s +S m *S m) where

    private
      E = ιPre {Ω} P

    -- the moments of the observations
    mom : ∀ n Xs → IID P μ n Xs → Moments P n (obs f n Xs) m s
    mom n Xs d = IID-moments P μ n Xs f m s d h i j em es

    -- the sample mean and the sample variance are unbiased
    iid-mean : ∀ n Xs (d : IID P μ n Xs) →
      Ex {Ω} E (sumT n (obs f n Xs)) (Int-sum P n (obs f n Xs) (λ k → proj₁ (proj₁ (mom n Xs d) k))) ≃ natS n *S m
    iid-mean n Xs d = Ex-sum P n (obs f n Xs) m s (mom n Xs d)

    iid-var : ∀ n Xs (d : IID P μ n Xs) →
      Var {Ω} P (sumT n (obs f n Xs)) (Int₂-sum P n (obs f n Xs) m s (mom n Xs d)) ≃ natS n *S s
    iid-var n Xs d = Var-sum P n (obs f n Xs) m s (mom n Xs d)

    iid-ss : ∀ n Xs (d : IID P μ n Xs) →
      Ex {Ω} E (ssT n (obs f n Xs)) (Int-ss P n (obs f n Xs) m s (mom n Xs d)) ≃ (natS n *S natS n +S -S natS n) *S s
    iid-ss n Xs d = Ex-ss P n (obs f n Xs) m s (mom n Xs d)

    -- the weak law, n ε² P{(Sₙ − n m)² ≥ (n ε)²} ≤ s
    iid-weak-law : ∀ k Xs → IID P μ (suc k) Xs → ∀ (χ : Hom S Ω WQ) e →
      (∀ ω → ((nat (suc k) * e) * (nat (suc k) * e)) * (map χ ⟨$⟩ ω)
        + at⁻ (devS P f m (suc k) Xs) ω ≤ at⁺ (devS P f m (suc k) Xs) ω) →
      (nat (suc k) * (e * e)) * ∫ᴹ {Ω} E χ ≤ᵛ s
    iid-weak-law k Xs d χ e hyp = weak-law-rate P k (obs f (suc k) Xs) m s (mom (suc k) Xs d) χ e hyp

  -- the draws of a sampler
  draw-mass : ∀ {Θ X : QBS S} (σ : SamplerQ Θ X) θ → ∫ᴹ {X} (mapM {ℛ} {X} (drawH σ θ) coin) (constW {X} 1#) ≈ 1#
  draw-mass {Θ} {X} σ θ = trans (∫ᴹ-map {ℛ} {X} (drawH σ θ) coin (constW {X} 1#))
    (trans (∫ᴹ-cong {ℛ} coin {_∘H_ S (constW {X} 1#) (drawH σ θ)} {constW {ℛ} 1#} (λ _ → refl)) (ι-mass {ℛ} coinPre))

  module _ {Θ X : QBS S} (σ : SamplerQ Θ X) (θ : ∣ Θ ∣) (f : SgT X) (m s : Sg)
    (i : Int {X} (mapM {ℛ} {X} (drawH σ θ) coin) f) (j : Int {X} (mapM {ℛ} {X} (drawH σ θ) coin) (f *T f))
    (em : Ex {X} (mapM {ℛ} {X} (drawH σ θ) coin) f i ≃ m)
    (es : Ex {X} (mapM {ℛ} {X} (drawH σ θ) coin) (f *T f) j ≃ s +S m *S m) where

    private
      μ = mapM {ℛ} {X} (drawH σ θ) coin
      Ds : ∀ n → Fin n → Hom S ℛ X
      Ds n k = _∘H_ S (drawH σ θ) (coordH (toℕ k))
      M : ∀ n → Moments coinPre n (obs f n (Ds n)) m s
      M n = mom coinPre μ (draw-mass σ θ) f m s i j em es n (Ds n) (draws-iid σ θ n)

    draws-mean : ∀ n →
      Ex {ℛ} coin (sumT n (obs f n (Ds n))) (Int-sum coinPre n (obs f n (Ds n)) (λ k → proj₁ (proj₁ (M n) k))) ≃ natS n *S m
    draws-mean n = iid-mean coinPre μ (draw-mass σ θ) f m s i j em es n (Ds n) (draws-iid σ θ n)

    draws-weak-law : ∀ k (χ : Hom S ℛ WQ) e →
      (∀ r → ((nat (suc k) * e) * (nat (suc k) * e)) * (map χ ⟨$⟩ r)
        + at⁻ (devS coinPre f m (suc k) (Ds (suc k))) r ≤ at⁺ (devS coinPre f m (suc k) (Ds (suc k))) r) →
      (nat (suc k) * (e * e)) * ∫ᴹ {ℛ} coin χ ≤ᵛ s
    draws-weak-law k χ e hyp = iid-weak-law coinPre μ (draw-mass σ θ) f m s i j em es k (Ds (suc k))
      (draws-iid σ θ (suc k)) χ e hyp
