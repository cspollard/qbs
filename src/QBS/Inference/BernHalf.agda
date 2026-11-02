{-# OPTIONS --safe --without-K #-}

-- The biased coin at θ = ½ is the fair coin: `bernθ ½ ≈ᵖ bernB` (both of `Inference/BoolDist`).
--
-- For a test f : BoolQ → [0,1] with a = f(true), b = f(false), the integral against `bernB` is ½a + ½b (`I-hB`).
-- Against `bernθ ½`, whose probe is the indicator of W = {expansion ≤ ½}, the integrand is a·χ_W + b·χ_{Wᶜ};
-- ∫ χ_W = ½ is the uniform CDF at ½ (`UniformCDF.cdf`) and ∫ χ_{Wᶜ} = ½ because the two add up to the total
-- mass 1 and ½ can be cancelled.
module QBS.Inference.BernHalf where

open import Data.Bool.Base as Bool using ()
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⟨$⟩_)
open import Level using (lower)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Core using (compl)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Threshold using (module Threshold)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.FairCoin using (module FairCoin)
import QBS.Continuous.UniformCDF as UC
import QBS.Inference.BoolDist as BD
import QBS.BoolQ as BQ
open BQ.BoolOn S

module BernHalf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass; I; I-cong; I-add; I-scale)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _*_; _+_; 1#; refl; sym; trans; +-cong; *-cong;
    +-comm; *-comm; cancel; ≤-refl; +-identityʳ; +-identityˡ; *-identityʳ; zeroʳ)
  open SignedTests (lemOf lem₁) using (CutQ)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; _≈ᵖ_; ∫)
  open Pre
  open Measurable A using (Fun-scale)
  open Daniell lem₁ using (L-one)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-in; χ-out; I-const; I-χ-compl)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open FairCoin lem₁ using (fairCoin)
  open Threshold (lemOf lem₁) using (Below-borel)
  open Expansion A half hh using (expansion; Fun-expansion)
  open UC.UniformCDF lem₁ using (cdf; ι-χ)
  open BD.BoolDist lem₁ using (bernθ; bernB; indθ; decθ; belowθ; hB; I-hB; Fun-hB; cdfVal; Fun-cdfVal)

  W = belowθ half
  bW = Below-borel Fun-expansion half

  -- ∫ χ_W = ½ (the uniform CDF at ½)
  I-W : I fairCoin (χ W) (Fun-χ bW) ≈ half
  I-W = trans (I-cong fairCoin (λ r → sym (ι-χ expansion half r)) (Fun-χ bW) (Fun-cdfVal half)) (cdf half half≤1)

  -- ∫ χ_{Wᶜ} = ½: the two add up to the mass 1
  I-nW : I fairCoin (χ (λ y → W y → ⊥)) (Fun-χ (compl bW)) ≈ half
  I-nW = cancel half≤1 (trans (+-comm half _) (trans (+-cong refl (sym I-W))
    (trans (I-χ-compl fairCoin bW) (trans (I-const fairCoin L-one 1# ≤-refl) (sym hh)))))

  -- the integrand is a·χ_W + b·χ_{Wᶜ} pointwise
  θ-go : ∀ (f : Hom S BoolQ AQ) r (d : W (lower r) ⊎ (W (lower r) → ⊥)) →
    proj₁ (Hom.map f ⟨$⟩ boolQ (BD.flag d))
      ≈ proj₁ (Hom.map f ⟨$⟩ trueQ) * χ W r + proj₁ (Hom.map f ⟨$⟩ falseQ) * χ (λ y → W y → ⊥) r
  θ-go f r (inj₁ p) = trans (sym (+-identityʳ _)) (+-cong (sym (trans (*-cong refl (χ-in W r p)) (*-identityʳ _)))
    (sym (trans (*-cong refl (χ-out (λ y → W y → ⊥) r (λ n → n p))) (zeroʳ _))))
  θ-go f r (inj₂ np) = trans (sym (+-identityˡ _)) (+-cong (sym (trans (*-cong refl (χ-out W r np)) (zeroʳ _)))
    (sym (trans (*-cong refl (χ-in (λ y → W y → ⊥) r np)) (*-identityʳ _))))

  θ-split : ∀ (f : Hom S BoolQ AQ) r → proj₁ (Hom.map f ⟨$⟩ (indθ half ⟨$⟩ r))
    ≈ proj₁ (Hom.map f ⟨$⟩ trueQ) * χ W r + proj₁ (Hom.map f ⟨$⟩ falseQ) * χ (λ y → W y → ⊥) r
  θ-split f r = θ-go f r (decθ half (lower r))

  -- the integral of a·χ_W + b·χ_{Wᶜ}, the integrand against `bernθ ½`
  I-θ : ∀ f → ∫ (bernθ half) f ≈ half * proj₁ (Hom.map f ⟨$⟩ trueQ) + half * proj₁ (Hom.map f ⟨$⟩ falseQ)
  I-θ f = trans (I-add fairCoin LF F₁ F₂ (θ-split f))
    (trans (+-cong (I-scale fairCoin a (Fun-χ bW) F₁ (λ _ → refl))
                   (I-scale fairCoin b (Fun-χ (compl bW)) F₂ (λ _ → refl)))
    (trans (+-cong (*-cong refl I-W) (*-cong refl I-nW)) (+-cong (*-comm a half) (*-comm b half))))
    where
    a = proj₁ (Hom.map f ⟨$⟩ trueQ)
    b = proj₁ (Hom.map f ⟨$⟩ falseQ)
    LF = Hom.map-random f {α (bernθ half)} (α-random (bernθ half))
    F₁ = Fun-scale a (proj₂ (Hom.map f ⟨$⟩ trueQ)) (Fun-χ bW)
    F₂ = Fun-scale b (proj₂ (Hom.map f ⟨$⟩ falseQ)) (Fun-χ (compl bW))

  -- the integral against `bernB` is ½a + ½b
  I-B : ∀ f → ∫ bernB f ≈ half * proj₁ (Hom.map f ⟨$⟩ trueQ) + half * proj₁ (Hom.map f ⟨$⟩ falseQ)
  I-B f = trans (I-cong fairCoin pt (Hom.map-random f {α bernB} (α-random bernB)) (Fun-hB a b a≤1 b≤1))
    (I-hB a b a≤1 b≤1)
    where
    a = proj₁ (Hom.map f ⟨$⟩ trueQ)
    b = proj₁ (Hom.map f ⟨$⟩ falseQ)
    a≤1 = proj₂ (Hom.map f ⟨$⟩ trueQ)
    b≤1 = proj₂ (Hom.map f ⟨$⟩ falseQ)
    pt-b : ∀ x → proj₁ (Hom.map f ⟨$⟩ boolQ x) ≈ Hom.map (ifQ {CutQ} a b) ⟨$⟩ boolQ x
    pt-b Bool.true = refl
    pt-b Bool.false = refl
    pt : ∀ r → proj₁ (Hom.map f ⟨$⟩ (α bernB ⟨$⟩ r)) ≈ hB a b r
    pt r = pt-b (lower r 0)

  -- the biased coin at ½ is the fair coin
  bernθ-half≈bernB : bernθ half ≈ᵖ bernB
  bernθ-half≈bernB f = trans (I-θ f) (sym (I-B f))
