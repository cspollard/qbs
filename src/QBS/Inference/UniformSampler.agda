{-# OPTIONS --safe --without-K #-}

-- Validation of `Inference/Sampler`: the uniform distribution on [0,1] as a sampler.  The sampler `(⋆ , r) ↦ expansion r`
-- from the one-point parameter space into the unit interval and the identity test (`pos = id`, `neg = 0`) have, for a
-- single draw, the mean ½ and the variance of `Continuous/UniformVariance` (the signed function of the draw is `u`).  The
-- unbiasedness theorems of `Inference/Frequentist` for the iid experiment therefore follow from the general
-- `Sampler.iid-moments`; they are the statements of `Continuous/UniformSample` for the same estimators.
module QBS.Inference.UniformSampler where

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import QBS.Classical using (LEM₁)

open import QBS.Core
open import QBS.Limits using (1Q)
import QBS.Probes as Probes
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.Archimedean using (module Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Variance using (module Variance)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.UniformVariance using (module UniformVariance)
open import QBS.Continuous.UniformSample using (module UniformSample)
open import QBS.Inference.Frequentist
open import QBS.Inference.Sampler using (module Sampler)

module UniformSampler (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open UnitInterval A using (AQ)
  open Measurable A using (Fun-pre)
  open Meas (lemOf lem₁) using (Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open Bounded A using (Sg; _≃_; ≃-trans; _+S_; _*S_; -S_; nat)
  open SignedIntegral (lemOf lem₁) using (E; E-cong)
  open Variance (lemOf lem₁) using (_*SF_[_])
  open OmegaSemiring A using (_≤_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; +-identityʳ; 0-least)
  open Uniform lem₁ using (expansionProbe)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh using (Fun-expansion)
  open UniformVariance lem₁ using (u; u⁺; u⁻; u-bdd; uu; varU; vf)
  open UniformSample lem₁ using (shift-sub)
  open SignedTests (lemOf lem₁) using (STest; CutQ)
  open Sampler lem₁

  -- the sampler: forget the (trivial) parameter and read the binary expansion of the coin
  uniformSampler : Sampler (1Q S) AQ
  uniformSampler = record
    { map = record { to = λ p → expansionProbe ⟨$⟩ proj₂ p ; cong = λ { (_ , e) → Func.cong expansionProbe e } }
    ; map-random = λ {γ} (_ , m₂) → Fun-pre {f = λ x → proj₂ (γ ⟨$⟩ x)} Fun-expansion m₂
    }

  -- the identity test on the unit interval, bounded by 1
  idTest : STest AQ
  idTest = record
    { pos = record { map = record { to = proj₁ ; cong = λ e → e } ; map-random = λ f → LS f }
    ; neg = record { map = record { to = λ _ → 0# ; cong = λ _ → OmegaSemiring.refl A } ; map-random = λ _ → Meas-const 0# }
    ; bound = 1
    ; pos-bdd = λ x → ≤-trans (proj₂ x) (≤-reflexive (sym (+-identityʳ 1#)))
    ; neg-bdd = λ _ → 0-least
    }

  -- the moments of one draw: mean E u (= ½) and variance Var u (= 1/12); the signed function of the draw is `u`
  singleMoments : SingleMoments uniformSampler idTest (λ _ → E u) (λ _ → varU)
  singleMoments = (λ _ → E-cong (λ x → trans (+-cong refl (u⁻ x)) (+-cong (sym (u⁺ x)) refl)))
                , (λ _ → ≃-trans {_} {E uu} {_} (E-cong {_} {_} {uu} second-parts) (shift-sub vf))
    where
    second-parts = λ x → trans (+-cong refl (+-cong (*-cong (u⁺ x) (u⁻ x)) (*-cong (u⁻ x) (u⁺ x))))
      (sym (+-cong (+-cong (*-cong (u⁺ x) (u⁺ x)) (*-cong (u⁻ x) (u⁻ x))) refl))

  -- the iid experiment of the sampler has the moments of the frequentist layer
  moments : F.Moments (iidExperiment uniformSampler idTest) (λ _ → E u) (λ _ → varU)
  moments = iid-moments uniformSampler idTest (λ _ → E u) (λ _ → varU) singleMoments

  -- the theorems of the generic layer for the sampler: Sₙ / n is unbiased for the mean, and (n Qₙ − Sₙ²) / (n² − n) for the
  -- variance (compare `UniformSample.sample-mean-unbiased` and `sample-variance`)
  sample-mean-unbiased : ∀ n → F.ScaledUnbiased (iidExperiment uniformSampler idTest) (λ _ → F.natS n) (λ _ → E u) (sumT n)
  sample-mean-unbiased = F.sample-mean-unbiased moments

  sample-variance-unbiased : ∀ n → F.ScaledUnbiased (iidExperiment uniformSampler idTest)
    (λ _ → F.natS n *S F.natS n +S -S F.natS n) (λ _ → varU) (ssT n)
  sample-variance-unbiased = F.sample-variance-unbiased moments
