{-# OPTIONS --safe --without-K #-}

-- Densities on the whole real line `RQ = WQ +Q WQ` (`Continuous/RealLine`) built from half-line densities.
--   * `∫ᴹ-lebR-dens d e f : ∫ᴹ lebR (mulH [d , e] f) ≈ ∫ᴹ lebPre (d · f∘inl) + ∫ᴹ lebPre (e · f∘inr)`;
--   * `lebR-sym d c : ∫ᴹ lebPre d ≈ c → ∫ᴹ lebR [d , d] ≈ c + c`;
--   * for a symmetric density `[d , d]` with `∫ᴹ lebPre d ≈ c` and any `n` with `(c + c) · n ≈ 1#`
--     (`module Sym d c hc n nn`): `symDist : Pre RQ`, `normPre` of Lebesgue measure with density `[d , d]` by `n`, with
--     `∫-sym f : ∫ᴹ (ιPre symDist) f ≈ n · (∫ᴹ lebPre (d · f∘inl) + ∫ᴹ lebPre (d · f∘inr))`, and `J-sym g`, the same for
--     the pulled-back integral of a non-negative part `g : RQ ⇒ WQ` (`toR g : RQ ⇒ CutQ`).
module QBS.Continuous.RealDensity where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (proj₁)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)

module RealDensity (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; sym; trans; +-cong; *-cong; *-identityˡ; *-identityʳ)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; ψ; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteNorm (lemOf lem₁) using (massP; normPre; ∫-normPre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH; copairH; lebR; ∫ᴹ-lebR)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open Hom

  -- a non-negative test on `RQ` as a `CutQ`-valued one
  toR : Hom S RQ WQ → Hom S RQ CutQ
  toR g = record { map = map g ; map-random = λ {γ} mγ → map-random g {γ} mγ }

  -- the integral of a copaired density against a test, half by half
  ∫ᴹ-lebR-dens : ∀ (d e : Hom S WQ WQ) (f : Hom S RQ WQ) →
    ∫ᴹ {RQ} lebR (mulH {RQ} (copairH d e) f)
      ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S f inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} e (_∘H_ S f inrH))
  ∫ᴹ-lebR-dens d e f = trans (∫ᴹ-lebR (mulH {RQ} (copairH d e) f))
    (+-cong (∫ᴹ-cong {WQ} lebPre {_∘H_ S (mulH {RQ} (copairH d e) f) inlH} {mulH {WQ} d (_∘H_ S f inlH)} (λ x → refl))
            (∫ᴹ-cong {WQ} lebPre {_∘H_ S (mulH {RQ} (copairH d e) f) inrH} {mulH {WQ} e (_∘H_ S f inrH)} (λ x → refl)))

  -- total mass of a symmetric density
  lebR-sym : ∀ (d : Hom S WQ WQ) c → ∫ᴹ {WQ} lebPre d ≈ c → ∫ᴹ {RQ} lebR (copairH d d) ≈ c + c
  lebR-sym d c hc = trans (∫ᴹ-lebR (copairH d d))
    (+-cong (trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S (copairH d d) inlH} {d} (λ x → refl)) hc)
            (trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S (copairH d d) inrH} {d} (λ x → refl)) hc))

  module Sym (d : Hom S WQ WQ) (c : _) (hc : ∫ᴹ {WQ} lebPre d ≈ c) (n : _) (nn : (c + c) * n ≈ 1#) where
    dR : Hom S RQ WQ
    dR = copairH d d

    massR : massP {RQ} (reweightPre {RQ} dR lebR) * n ≈ 1#
    massR = trans (*-cong (trans (∫ᴹ-reweight {RQ} dR lebR (constW 1#))
      (trans (∫ᴹ-cong {RQ} lebR {mulH {RQ} dR (constW 1#)} {dR} (λ x → *-identityʳ _)) (lebR-sym d c hc))) refl) nn

    abstract
      symDist : Pre RQ
      symDist = normPre {RQ} (reweightPre {RQ} dR lebR) n massR

      ∫-sym : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} symDist) f ≈
        n * (∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S f inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S f inrH)))
      ∫-sym f = trans (∫-normPre {RQ} (reweightPre {RQ} dR lebR) n massR f)
        (*-cong refl (trans (∫ᴹ-reweight {RQ} dR lebR f) (∫ᴹ-lebR-dens d d f)))

    J-sym : ∀ (g : Hom S RQ WQ) →
      J (m symDist) (λ r → map (toR g) ⟨$⟩ (α symDist ⟨$⟩ r)) (map-random (toR g) {α symDist} (α-random symDist))
        ≈ n * (∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S g inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S g inrH)))
    J-sym g = trans (J-cong (m symDist) {λ r → map (toR g) ⟨$⟩ (α symDist ⟨$⟩ r)} {ψ {RQ} (ιPre {RQ} symDist) g}
      (map-random (toR g) {α symDist} (α-random symDist)) (mψ {RQ} (ιPre {RQ} symDist) g)
      (λ r → sym (*-identityˡ _))) (∫-sym g)
