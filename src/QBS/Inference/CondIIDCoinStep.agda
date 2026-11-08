{-# OPTIONS --safe --without-K #-}

-- One step of the coin kernel through the inclusion into s-finite measures (helper for `CondIIDCoin`; plan 05 item 48a).
--   * `nextK-ι`: for K : AQ ⇒ T F of the probability monad, the law `nextK K θ` (one more flip in front, then the flips
--     of K) integrates, through `SFiniteIncl.ιPre`, like the iterated integral over the first flip b ~ coinKernel θ of
--     ∫ h(b, ·) dK(θ), the s-finite product of `coinKernel θ` and `K θ` in the order of `Product.∫-prod′`.
-- Route: `ι-mult`, `∫ᴹ-join`, `ι-nat` and `∫ᴹ-map` unfold the join and the map, `ι-strong` and `∫ᴹ-σ` the two strengths.
module QBS.Inference.CondIIDCoinStep where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Limits using (_×Q_)
open import QBS.BoolQ using (module BoolOn)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Inference.CoinUniformPrior using (module CoinUniformPrior)
open import QBS.Inference.CoinUniformPriorN using (module CoinUniformPriorN)

module CondIIDCoinStep (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open Integration A using (probClass)
  open UnitInterval A using (AQ)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; TQ; ∫ᴹ; ∫ᶠ; ∫ᴹ-map; ∫ᴹ-join; ∫ᴹ-cong; mapM; joinPre; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ιH; ι-nat; ι-mult; ι-strong)
  open Product (lemOf lem₁) using (intR; intR-pt)
  open SFiniteStrong (lemOf lem₁) using (σPre; ∫ᴹ-σ; fixH)
  open Strength A (lemOf lem₁) probClass using () renaming (σPre to σPreC)
  open CoinUniformPrior lem₁ using (coinKernel)
  open CoinUniformPriorN lem₁ using (nextK; flipPairN)
  open BoolOn S using (BoolQ)
  open QBS
  open Hom

  -- the integrand over the first flip
  nextK-pw : ∀ {F : QBS S} (K : Hom S AQ (C.TQ F)) θ (h : Hom S (_×Q_ S BoolQ F) WQ) b →
    map (fixH {AQ} {BoolQ} θ (_∘H_ S (_∘H_ S (∫ᶠ {_×Q_ S BoolQ F} h) (ιH (_×Q_ S BoolQ F))) (flipPairN K))) ⟨$⟩ b
      ≈ map (intR {BoolQ} {F} (ιPre {F} (map K ⟨$⟩ θ)) h) ⟨$⟩ b
  nextK-pw {F} K θ h b = trans (ι-strong {BoolQ} {F} b (map K ⟨$⟩ θ) h) (trans (∫ᴹ-σ {BoolQ} {F} b (ιPre {F} (map K ⟨$⟩ θ)) h)
    (sym (intR-pt {BoolQ} {F} (ιPre {F} (map K ⟨$⟩ θ)) h b)))

  nextK-ι : ∀ {F : QBS S} (K : Hom S AQ (C.TQ F)) θ (h : Hom S (_×Q_ S BoolQ F) WQ) →
    ∫ᴹ {_×Q_ S BoolQ F} (ιPre {_×Q_ S BoolQ F} (map (nextK K) ⟨$⟩ θ)) h
      ≈ ∫ᴹ {BoolQ} (ιPre {BoolQ} (map coinKernel ⟨$⟩ θ)) (intR {BoolQ} {F} (ιPre {F} (map K ⟨$⟩ θ)) h)
  nextK-ι {F} K θ h = trans (ι-mult {BF} _ h)
    (trans (∫ᴹ-join {BF} _ h)
      (trans (ι-nat {C.TQ BF} {TQ BF} (ιH BF) _ (∫ᶠ {BF} h))
        (trans (∫ᴹ-map {C.TQ BF} {TQ BF} (ιH BF) _ (∫ᶠ {BF} h))
          (trans (ι-nat {AQ×B} {C.TQ BF} fp w T)
            (trans (∫ᴹ-map {AQ×B} {C.TQ BF} fp (ιPre {AQ×B} w) T)
              (trans (ι-strong {AQ} {BoolQ} θ (map coinKernel ⟨$⟩ θ) (_∘H_ S T fp))
                (trans (∫ᴹ-σ {AQ} {BoolQ} θ (ιPre {BoolQ} (map coinKernel ⟨$⟩ θ)) (_∘H_ S T fp))
                  (∫ᴹ-cong {BoolQ} (ιPre {BoolQ} (map coinKernel ⟨$⟩ θ)) (nextK-pw K θ h)))))))))
    where
      AQ×B = _×Q_ S AQ BoolQ
      BF = _×Q_ S BoolQ F
      fp = flipPairN K
      w = σPreC {AQ} {BoolQ} (θ , map coinKernel ⟨$⟩ θ)
      T = _∘H_ S (∫ᶠ {BF} h) (ιH BF)
