{-# OPTIONS --safe --without-K #-}

-- The two views of inference on one model: is the coin fair or two-headed?  (`plans/03-bayesian-frequentist.md`, 3c.)
--
-- Bayesian (`Inference/CoinBias`): the likelihood `heads` of a head is 1 under "two-headed" and ½ under "fair"; the evidence is
-- the prior-weighted sum ½·1 + ½·½ (`evidence-heads`).
-- Frequentist (`Inference/Sampler`): each hypothesis is a sampler of a head indicator, the draw `[expansion r ≤ t]` of the
-- cumulative distribution function (`Continuous/UniformCDF.cdfTest`) with t = 1 for "two-headed" and t = ½ for "fair".  The
-- indicator is valued in {0,1} ⊆ [0,1] = `AQ` and read off by the identity test, as in `Inference/ExpectationExamples`.
--
-- The bridge (`likelihood-is-expectation`): for each hypothesis h, the expectation of a single draw of the sampler of h is the
-- likelihood `heads h` (from `UniformCDF.cdf`: P(u ≤ t) = t).  The Bayesian evidence is then the prior expectation of the
-- frequentist one (`evidence-is-prior-expectation`).  `CoinBias` is used directly (`heads`, `half`, `evidence-heads`).
module QBS.Inference.BernoulliCompare where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Product.Base using (_,_; proj₁)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
import Level as L
open import Level using (lift)

open import QBS.Core
open import QBS.Classical using (LEM₁; LEM)
open import QBS.Limits using (1Q)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.CoinIndep using (module CoinIndep)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.UniformCDF using (module UniformCDF)
open import QBS.Continuous.SubModel using (module SubModel)
open import QBS.Inference.Sampler using (module Sampler)
open import QBS.Inference.UniformSampler using (module UniformSampler)
open import QBS.Inference.CoinBias using (module Additive)

module BernoulliCompare (lem₁ : LEM₁) where
  -- `CoinBias` states classical logic with the polymorphic empty type
  lemP : LEM (L.suc L.zero)
  lemP P with lem₁ P
  ... | inj₁ p = inj₁ p
  ... | inj₂ n = inj₂ (λ p → L.lift (n p))

  open Lebesgue (lemOf lem₁) using (A; J; J-irrel; J-fun)
  open UnitInterval A using (AQ)
  open Bounded A using (Sg; Bnd; _≃_; ≃-trans; ≃-sym; ≃-refl; _+S_; _*S_; *S-cong; +S-cong; ι; ι-+; ι-*; finite; mk≃)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _*_; _+_; 0#; 1#; refl; sym; trans; +-cong; ≤-refl; ≤-trans; ≤-reflexive; +-identityʳ)
  open BoundedRing (lemOf lem₁) using (E-B)
  open FairCoin lem₁ using (fairCoin)
  open Sampler lem₁
  open UniformSampler lem₁ using (uniformSampler; idTest)
  open UniformCDF lem₁ using (cdfTest; cdf)
  open Measurable A using (Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open Uniform lem₁ using (expansionProbe)
  open SubModel lem₁ using (uniformSub)
  open Additive lemP using (heads)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh using (Fun-expansion)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open CoinIndep lem₁ using (fairCoin-prob)
  open SignedIntegral (lemOf lem₁) using (J-const)

  -- the head indicator of one uniform draw: `[expansion r ≤ t]`
  headSampler : ∣A∣ → Sampler (1Q S) AQ
  headSampler t = _∘H_ S (cdfTest t) uniformSampler

  b1 : ∀ {a} → a ≤ 1# → Bnd a
  b1 le = 1 , ≤-trans le (≤-reflexive (sym (+-identityʳ 1#)))

  -- the threshold of the hypothesis: 1 for "two-headed" (`true`), ½ for "fair" (`false`)
  thr : Bool → ∣A∣
  thr true = 1#
  thr false = half

  thr≤1 : ∀ h → thr h ≤ 1#
  thr≤1 true = ≤-refl
  thr≤1 false = half≤1

  -- the two samplers
  twoHeadedS fairS : Sampler (1Q S) AQ
  twoHeadedS = headSampler 1#
  fairS = headSampler half

  sampler : Bool → Sampler (1Q S) AQ
  sampler h = headSampler (thr h)

  Fb : ∀ h → Fun (λ r → proj₁ (Hom.map (cdfTest (thr h)) ⟨$⟩ (expansionProbe ⟨$⟩ r)))
  Fb h = Hom.map-random (cdfTest (thr h)) {expansionProbe} Fun-expansion

  -- the expectation of a single draw: ∫ of the indicator is the threshold, by `UniformCDF.cdf`
  -- the positive part integrates to the threshold, the negative part to 0
  single-draw : ∀ h → E-B fairCoin fairCoin-prob (single (sampler h) idTest (lift tt)) ≃ ι (b1 (thr≤1 h))
  single-draw h = mk≃ 0# (SubSemiring.Is-0 finite) (+-cong (+-cong pos neg) refl)
    where
    pos = trans (J-irrel fairCoin _ (LS (Fb h))) (trans (J-fun fairCoin (Fb h)) (cdf (thr h) (thr≤1 h)))
    neg = sym (trans (J-irrel fairCoin _ _) (J-const fairCoin-prob 0#))

  -- the Bayesian likelihood is the frequentist expectation: E[head | h] = P(head | h)
  hb : ∀ h → Bnd (heads (lift h))
  hb true = b1 ≤-refl
  hb false = b1 half≤1

  likelihood-is-expectation : ∀ h → E-B fairCoin fairCoin-prob (single (sampler h) idTest (lift tt)) ≃ ι (hb h)
  likelihood-is-expectation true = single-draw true
  likelihood-is-expectation false = single-draw false

  ----------------------------------------------------------------------------
  -- the evidence

  -- the Bayesian evidence (the right-hand side of `CoinBias.evidence-heads`: ½·1 + ½·½) with its bound
  ev : ∣A∣
  ev = half * 1# + half * half

  ev-bnd : Bnd ev
  ev-bnd = SubSemiring.Is-+ finite (SubSemiring.Is-* finite (b1 half≤1) (b1 ≤-refl))
                                   (SubSemiring.Is-* finite (b1 half≤1) (b1 half≤1))

  -- the Bayesian evidence is the prior expectation of the frequentist one, with prior weights ½, ½:
  -- ½·E[head | two-headed] + ½·E[head | fair] ≃ ½·1 + ½·½
  evidence-is-prior-expectation :
    (ι (b1 half≤1) *S E-B fairCoin fairCoin-prob (single twoHeadedS idTest (lift tt))) +S
    (ι (b1 half≤1) *S E-B fairCoin fairCoin-prob (single fairS idTest (lift tt))) ≃ ι ev-bnd
  evidence-is-prior-expectation =
    ≃-trans (+S-cong (*S-cong ≃-refl (likelihood-is-expectation true)) (*S-cong ≃-refl (likelihood-is-expectation false)))
    (≃-trans (+S-cong (≃-sym (ι-* (b1 half≤1) (b1 ≤-refl))) (≃-sym (ι-* (b1 half≤1) (b1 half≤1))))
    (≃-sym (ι-+ (SubSemiring.Is-* finite (b1 half≤1) (b1 ≤-refl)) (SubSemiring.Is-* finite (b1 half≤1) (b1 half≤1)))))
