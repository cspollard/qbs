{-# OPTIONS --safe --without-K #-}

-- Uniqueness of measures on the whole real line `RQ = WQ +Q WQ` (plan 03, "Tests and the real line").
-- A measure μ on RQ has two halves on the half-line, `restrL μ` and `restrR μ`: reweight by the indicator of the left
-- (right) summand and fold RQ onto WQ (`foldH = [id , id]`), so `∫-restrL : ∫ (restrL μ) g ≈ ∫ μ [g , 0]`.
--   * `∫-split : ∫ μ f ≈ ∫ μ [f∘inl , 0] + ∫ μ [0 , f∘inr]` (every test on RQ is the sum of its two halves);
--   * `uniqRQ`: measures with equal halves are equal;
--   * `lebR-unique`: a measure whose halves have the interval masses of Lebesgue measure and no mass at ±∞ is `lebR`
--     (through `LebesgueInterval.leb-unique` on each half, `restrL-lebR`, `restrR-lebR`).
-- Route for `∫-split`: f ≈ [f∘inl , 0] + [0 , f∘inr] pointwise on each summand (`copair` computes on `inl`, `inr`), and
-- `∫ᴹ` is additive in the test (`SFinite.∫ᴹ-series` with the sequence f₁, f₂, 0, 0, …, or the sum of tests by `copair`).
module QBS.Continuous.UniquenessRQ where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Sum.Base using (inj₁; inj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.UniquenessRQAlg using (module UniquenessRQAlg)

module UniquenessRQ (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#
    ; refl; sym; trans; +-cong; ≤-trans; ≤-reflexive; ≤-antisym; ≤-+ʳ; 0-least; *-identityˡ; zeroˡ; +-identityˡ; +-identityʳ; +-comm) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; ∫ᴹ-map; ∫ᴹ-cong; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open HalfLine lem₁ using (lebPre)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χIv; χInf)
  open RealLine lem₁ using (RQ; inlH; inrH; copairH; lebR; ∫ᴹ-lebR)
  open LebesgueInterval lem₁ using (leb-unique)
  open LebesgueIntervalAlg (lemOf lem₁) using (∫ᴹ-zero′)
  open UniquenessRQAlg (lemOf lem₁) using (addX; ∫ᴹ-addX)
  open QBS
  open Hom

  zeroW : Hom S WQ WQ
  zeroW = constW 0#

  -- fold the two summands onto the half-line, and the indicators of the summands
  foldH : Hom S RQ WQ
  foldH = copairH idW idW

  oneL oneR : Hom S RQ WQ
  oneL = copairH (constW 1#) zeroW
  oneR = copairH zeroW (constW 1#)

  -- the two halves of a measure on RQ
  restrL restrR : Pre (XW RQ) → Pre (XW WQ)
  restrL μ = mapM {RQ} {WQ} foldH (reweightPre {RQ} oneL μ)
  restrR μ = mapM {RQ} {WQ} foldH (reweightPre {RQ} oneR μ)

  ∫-restrL : ∀ (μ : Pre (XW RQ)) (g : Hom S WQ WQ) → ∫ᴹ {WQ} (restrL μ) g ≈ ∫ᴹ {RQ} μ (copairH g zeroW)
  ∫-restrL μ g = trans (∫ᴹ-map {RQ} {WQ} foldH (reweightPre {RQ} oneL μ) g)
    (trans (∫ᴹ-reweight {RQ} oneL μ (_∘H_ S g foldH))
      (∫ᴹ-cong {RQ} μ {mulH {RQ} oneL (_∘H_ S g foldH)} {copairH g zeroW} pt))
    where
      pt : ∀ x → map (mulH {RQ} oneL (_∘H_ S g foldH)) ⟨$⟩ x ≈ map (copairH g zeroW) ⟨$⟩ x
      pt (inj₁ a) = *-identityˡ _
      pt (inj₂ b) = zeroˡ _

  ∫-restrR : ∀ (μ : Pre (XW RQ)) (g : Hom S WQ WQ) → ∫ᴹ {WQ} (restrR μ) g ≈ ∫ᴹ {RQ} μ (copairH zeroW g)
  ∫-restrR μ g = trans (∫ᴹ-map {RQ} {WQ} foldH (reweightPre {RQ} oneR μ) g)
    (trans (∫ᴹ-reweight {RQ} oneR μ (_∘H_ S g foldH))
      (∫ᴹ-cong {RQ} μ {mulH {RQ} oneR (_∘H_ S g foldH)} {copairH zeroW g} pt))
    where
      pt : ∀ x → map (mulH {RQ} oneR (_∘H_ S g foldH)) ⟨$⟩ x ≈ map (copairH zeroW g) ⟨$⟩ x
      pt (inj₁ a) = zeroˡ _
      pt (inj₂ b) = *-identityˡ _

  -- every test is the sum of its two halves
  ∫-split : ∀ (μ : Pre (XW RQ)) (f : Hom S RQ WQ) →
    ∫ᴹ {RQ} μ f ≈ ∫ᴹ {RQ} μ (copairH (_∘H_ S f inlH) zeroW) + ∫ᴹ {RQ} μ (copairH zeroW (_∘H_ S f inrH))
  ∫-split μ f = trans (∫ᴹ-cong {RQ} μ {f} {addX {RQ} (copairH (_∘H_ S f inlH) zeroW) (copairH zeroW (_∘H_ S f inrH))} pt)
    (∫ᴹ-addX {RQ} μ (copairH (_∘H_ S f inlH) zeroW) (copairH zeroW (_∘H_ S f inrH)))
    where
      pt : ∀ x → map f ⟨$⟩ x ≈ (map (copairH (_∘H_ S f inlH) zeroW) ⟨$⟩ x) + (map (copairH zeroW (_∘H_ S f inrH)) ⟨$⟩ x)
      pt (inj₁ a) = sym (+-identityʳ _)
      pt (inj₂ b) = sym (+-identityˡ _)

  uniqRQ : ∀ (μ ν : Pre (XW RQ)) → _≈ᴹ_ {WQ} (restrL μ) (restrL ν) → _≈ᴹ_ {WQ} (restrR μ) (restrR ν) →
    _≈ᴹ_ {RQ} μ ν
  uniqRQ μ ν hL hR f = trans (∫-split μ f)
    (trans (+-cong (sym (∫-restrL μ (_∘H_ S f inlH))) (sym (∫-restrR μ (_∘H_ S f inrH))))
      (trans (+-cong (hL (_∘H_ S f inlH)) (hR (_∘H_ S f inrH)))
        (trans (+-cong (∫-restrL ν (_∘H_ S f inlH)) (∫-restrR ν (_∘H_ S f inrH))) (sym (∫-split ν f)))))

  -- the halves of Lebesgue measure on RQ
  restrL-lebR : _≈ᴹ_ {WQ} (restrL lebR) lebPre
  restrL-lebR g = trans (∫-restrL lebR g) (trans (∫ᴹ-lebR (copairH g zeroW))
    (trans (+-cong (∫ᴹ-cong {WQ} lebPre {_∘H_ S (copairH g zeroW) inlH} {g} (λ x → refl))
                   (∫ᴹ-zero′ lebPre (_∘H_ S (copairH g zeroW) inrH) (λ x → refl)))
      (+-identityʳ _)))

  restrR-lebR : _≈ᴹ_ {WQ} (restrR lebR) lebPre
  restrR-lebR g = trans (∫-restrR lebR g) (trans (∫ᴹ-lebR (copairH zeroW g))
    (trans (+-cong (∫ᴹ-zero′ lebPre (_∘H_ S (copairH zeroW g) inlH) (λ x → refl))
                   (∫ᴹ-cong {WQ} lebPre {_∘H_ S (copairH zeroW g) inrH} {g} (λ x → refl)))
      (+-identityˡ _)))

  -- Lebesgue measure on RQ from its interval masses
  lebR-unique : ∀ (μ : Pre (XW RQ)) →
    (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {RQ} μ (copairH (χIv a b) zeroW) ≈ b) →
    (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {RQ} μ (copairH zeroW (χIv a b)) ≈ b) →
    ∫ᴹ {RQ} μ (copairH χInf χInf) ≈ 0# → _≈ᴹ_ {RQ} μ lebR
  lebR-unique μ hL hR hinf = uniqRQ μ lebR
    (λ f → trans (leb-unique (restrL μ) (λ a b le B → trans (+-cong refl (∫-restrL μ (χIv a b))) (hL a b le B)) infL f)
                 (sym (restrL-lebR f)))
    (λ f → trans (leb-unique (restrR μ) (λ a b le B → trans (+-cong refl (∫-restrR μ (χIv a b))) (hR a b le B)) infR f)
                 (sym (restrR-lebR f)))
    where
      sp : ∫ᴹ {RQ} μ (copairH (_∘H_ S (copairH χInf χInf) inlH) zeroW)
         + ∫ᴹ {RQ} μ (copairH zeroW (_∘H_ S (copairH χInf χInf) inrH)) ≈ 0#
      sp = trans (sym (∫-split μ (copairH χInf χInf))) hinf
      cL : ∫ᴹ {RQ} μ (copairH (_∘H_ S (copairH χInf χInf) inlH) zeroW) ≈ ∫ᴹ {RQ} μ (copairH χInf zeroW)
      cL = ∫ᴹ-cong {RQ} μ {copairH (_∘H_ S (copairH χInf χInf) inlH) zeroW} {copairH χInf zeroW} pt
        where pt : ∀ x → map (copairH (_∘H_ S (copairH χInf χInf) inlH) zeroW) ⟨$⟩ x ≈ map (copairH χInf zeroW) ⟨$⟩ x
              pt (inj₁ a) = refl
              pt (inj₂ b) = refl
      cR : ∫ᴹ {RQ} μ (copairH zeroW (_∘H_ S (copairH χInf χInf) inrH)) ≈ ∫ᴹ {RQ} μ (copairH zeroW χInf)
      cR = ∫ᴹ-cong {RQ} μ {copairH zeroW (_∘H_ S (copairH χInf χInf) inrH)} {copairH zeroW χInf} pt
        where pt : ∀ x → map (copairH zeroW (_∘H_ S (copairH χInf χInf) inrH)) ⟨$⟩ x ≈ map (copairH zeroW χInf) ⟨$⟩ x
              pt (inj₁ a) = refl
              pt (inj₂ b) = refl
      infL : ∫ᴹ {WQ} (restrL μ) χInf ≈ 0#
      infL = trans (∫-restrL μ χInf)
        (≤-antisym (≤-trans (≤-reflexive (sym cL)) (≤-trans ≤-+ʳ (≤-reflexive sp))) 0-least)
      infR : ∫ᴹ {WQ} (restrR μ) χInf ≈ 0#
      infR = trans (∫-restrR μ χInf) (≤-antisym (≤-trans (≤-reflexive (sym cR))
        (≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))) (≤-reflexive sp))) 0-least)
