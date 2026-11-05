{-# OPTIONS --safe --without-K #-}

-- The half-normal distribution, normalised by an abstract inverse of `Z = ∫₀^∞ e^{−x²/2} dλ` (so `√(π/2)` is not used).
-- Take any `n` with `Z · n ≈ 1#` (`module WithInverse n nZ`; the canonical choice is `n = LowerInverse.invC Z`, as Z is finite and
-- positive: `GaussInverse.Z-inv`, giving `module HN`).  Then
--   * `halfNormal : Pre WQ`, `normPre` of the Lebesgue measure with density `e^{−x²/2}` by `n`, with
--     `∫-hn f : ∫ᴹ (ιPre halfNormal) f ≈ n · ∫ᴹ lebPre (e^{−x²/2} · f)`;
--   * the second moment through the expectation API: `E-atᴵ-hn : E-atᴵ halfNormal sqI ≃ (1# − 0# [ … ])`, i.e. `E[X²] ≃ 1`,
--     from `GaussMoment.∫-x²φ : ∫ x² e^{−x²/2} = Z` and `n Z = 1` (so `Var X = 1`, whatever the value of Z).
-- The parts of the integrable test are `x²` and `0` (as in `Inference/DensityExpectation`).
module QBS.Inference.HalfNormal where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.GaussInverse using (module GaussInverse)
import QBS.Inference.ExpectationInt as EI

module HalfNormal (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; 0#; 1#; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-identityˡ; *-identityʳ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1)
  open Meas (lemOf lem₁) using (Meas-const)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong; ψ; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteNorm (lemOf lem₁) using (massP; normPre; ∫-normPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open DensityDist lem₁ using (densW; ∫ᴹ-densW)
  open ExpDistSq lem₁ using (sqW)
  open GaussHalfLine lem₁ using (phiH; gMomH)
  open GaussMoment lem₁ using (Z; ∫-x²φ)
  open GaussInverse lem₁ using (Z-inv)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open Hom

  toC : Hom S WQ WQ → Hom S WQ CutQ
  toC g = record { map = map g ; map-random = λ {γ} mγ → map-random g {γ} mγ }

  module WithInverse (n : ∣A∣) (nZ : Z * n ≈ 1#) where
    massP-hn : massP {WQ} (densW phiH) ≈ Z
    massP-hn = trans (∫ᴹ-densW phiH (constW 1#))
      (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (constW 1#)} {phiH} (λ x → *-identityʳ _))

    mass-inv-hn : massP {WQ} (densW phiH) * n ≈ 1#
    mass-inv-hn = trans (*-cong massP-hn refl) nZ

    -- the half-normal distribution
    abstract
      halfNormal : Pre WQ
      halfNormal = normPre {WQ} (densW phiH) n mass-inv-hn

      ∫-hn : ∀ (f : Hom S WQ WQ) → ∫ᴹ {WQ} (ιPre {WQ} halfNormal) f ≈ n * ∫ᴹ {WQ} lebPre (mulH {WQ} phiH f)
      ∫-hn f = trans (∫-normPre {WQ} (densW phiH) n mass-inv-hn f) (*-cong refl (∫ᴹ-densW phiH f))

    J-hn : ∀ (g : Hom S WQ WQ) →
      J (m halfNormal) (λ r → map (toC g) ⟨$⟩ (α halfNormal ⟨$⟩ r)) (map-random (toC g) {α halfNormal} (α-random halfNormal))
        ≈ n * ∫ᴹ {WQ} lebPre (mulH {WQ} phiH g)
    J-hn g = trans (J-cong (m halfNormal) {λ r → map (toC g) ⟨$⟩ (α halfNormal ⟨$⟩ r)}
      {ψ {WQ} (ιPre {WQ} halfNormal) g} (map-random (toC g) {α halfNormal} (α-random halfNormal))
      (mψ {WQ} (ιPre {WQ} halfNormal) g) (λ r → sym (*-identityˡ _))) (∫-hn g)

    -- E[X²] = n Z = 1
    sq-eq : ∀ x → map (mulH {WQ} phiH sqW) ⟨$⟩ x ≈ map (gMomH 2) ⟨$⟩ x
    sq-eq x = trans (*-comm _ _) (*-cong (sym (*-cong refl (*-identityʳ x))) refl)

    J-sq : J (m halfNormal) (λ r → map (toC sqW) ⟨$⟩ (α halfNormal ⟨$⟩ r))
      (map-random (toC sqW) {α halfNormal} (α-random halfNormal)) ≈ 1#
    J-sq = trans (J-hn sqW) (trans (*-cong refl (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH sqW} {gMomH 2} sq-eq))
      (trans (*-cong refl ∫-x²φ) (trans (*-comm n Z) nZ)))

    J-zero : J (m halfNormal) (λ r → map (toC (constW 0#)) ⟨$⟩ (α halfNormal ⟨$⟩ r))
      (map-random (toC (constW 0#)) {α halfNormal} (α-random halfNormal)) ≈ 0#
    J-zero = trans (J-irrel (m halfNormal) (map-random (toC (constW 0#)) {α halfNormal} (α-random halfNormal))
      (Meas-const 0#)) (J-const (ok halfNormal) 0#)

    sqI : ITest halfNormal
    sqI = record
      { pos = toC sqW ; neg = toC (constW 0#)
      ; pos-int = Is-resp finite (sym J-sq) (Is-1 finite)
      ; neg-int = Is-resp finite (sym J-zero) (Is-0 finite) }

    -- E[X²] ≃ 1
    E-atᴵ-hn : E-atᴵ halfNormal sqI ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
    E-atᴵ-hn = mk≃ 0# (Is-0 finite) (trans (+-cong (+-cong J-sq refl) refl) (sym (+-cong (+-cong refl J-zero) refl)))

  -- the canonical instance: `n = LowerInverse.invC Z` (Z is finite and positive, `Continuous/GaussInverse`)
  module HN = WithInverse (proj₁ Z-inv) (proj₂ Z-inv)
