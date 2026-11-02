{-# OPTIONS --safe --without-K #-}

-- Expectations under a normalised density on [0,∞) through the expectation API of `Inference/ExpectationInt`.
-- For `d` with `∫ᴹ lebPre d ≈ 1#` (`Continuous/DensityDist`) and two parts `g⁺ g⁻ : Hom S WQ WQ` whose
-- density-weighted Lebesgue integrals `a = ∫ᴹ lebPre (d·g⁺)`, `b = ∫ᴹ lebPre (d·g⁻)` are finite:
--   * `densI : ITest (densDist d nrm)` with `pos = g⁺`, `neg = g⁻`;
--   * `E-atᴵ-dens : E-atᴵ (densDist d nrm) (densI …) ≃ a − b`.
-- Validation: the exponential density `negExpH` gives the mean `≃ 1` (`E-atᴵ-idD`) and the second moment `≃ 2`
-- (`E-atᴵ-sqD`), with the same integrals as `Inference/ExpDistMean` and `ExpDistVar` (`idD-integral`, `sqD-integral`).
module QBS.Inference.DensityExpectation where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
import QBS.Inference.ExpectationInt as EI

module DensityExpectation (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; 0#; 1#; _+_; refl; sym; trans; +-cong; *-identityˡ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open Meas (lemOf lem₁) using (Meas-const)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ψ; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineNorm lem₁ using (∫ᴹ-leb-negExp-norm)
  open DensityDist lem₁ using (densDist; ∫-dens)
  open ExpDist lem₁ using (∫-expDist; ∫-expDist-id; idW)
  open ExpDistSq lem₁ using (sqW; ∫-expDist-sq)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open Hom

  -- a non-negative test as a `CutQ`-valued one
  toC : Hom S WQ WQ → Hom S WQ CutQ
  toC g = record { map = map g ; map-random = λ {γ} mγ → map-random g {γ} mγ }

  -- the pulled-back integral of a part is the density-weighted Lebesgue integral
  J-dens : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (g : Hom S WQ WQ) →
    J (m (densDist d nrm)) (λ r → map (toC g) ⟨$⟩ (α (densDist d nrm) ⟨$⟩ r))
      (map-random (toC g) {α (densDist d nrm)} (α-random (densDist d nrm))) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} d g)
  J-dens d nrm g = trans (J-cong (m (densDist d nrm)) {λ r → map (toC g) ⟨$⟩ (α (densDist d nrm) ⟨$⟩ r)}
    {ψ {WQ} (ιPre {WQ} (densDist d nrm)) g}
    (map-random (toC g) {α (densDist d nrm)} (α-random (densDist d nrm)))
    (mψ {WQ} (ιPre {WQ} (densDist d nrm)) g) (λ r → sym (*-identityˡ _))) (∫-dens d nrm g)

  -- the integrable test with the given parts
  densI : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (g⁺ g⁻ : Hom S WQ WQ) →
    Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁺)) → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁻)) → ITest (densDist d nrm)
  densI d nrm g⁺ g⁻ b⁺ b⁻ = record
    { pos = toC g⁺ ; neg = toC g⁻
    ; pos-int = Is-resp finite (sym (J-dens d nrm g⁺)) b⁺
    ; neg-int = Is-resp finite (sym (J-dens d nrm g⁻)) b⁻ }

  -- the expectation is the signed value of the two Lebesgue integrals
  E-atᴵ-dens : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (g⁺ g⁻ : Hom S WQ WQ)
    (b⁺ : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁺))) (b⁻ : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁻))) →
    E-atᴵ (densDist d nrm) (densI d nrm g⁺ g⁻ b⁺ b⁻)
      ≃ (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁺) − ∫ᴹ {WQ} lebPre (mulH {WQ} d g⁻) [ b⁺ , b⁻ ])
  E-atᴵ-dens d nrm g⁺ g⁻ b⁺ b⁻ = mk≃ 0# (Is-0 finite)
    (trans (+-cong (+-cong (J-dens d nrm g⁺) refl) refl) (sym (+-cong (+-cong refl (J-dens d nrm g⁻)) refl)))

  ------------------------------------------------------------------------
  -- the exponential density as an instance

  expNrm : ∫ᴹ {WQ} lebPre negExpH ≈ 1#
  expNrm = ∫ᴹ-leb-negExp-norm

  -- the integral against the zero test vanishes
  zero-integral : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) → ∫ᴹ {WQ} lebPre (mulH {WQ} d (constW 0#)) ≈ 0#
  zero-integral d nrm = trans (sym (J-dens d nrm (constW 0#)))
    (trans (J-irrel (m (densDist d nrm)) (map-random (toC (constW 0#)) {α (densDist d nrm)} (α-random (densDist d nrm)))
      (Meas-const 0#)) (J-const (ok (densDist d nrm)) 0#))

  -- the integrals agree with those of `ExpDist`/`ExpDistSq`
  idD-integral : ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH idW) ≈ 1#
  idD-integral = trans (sym (∫-expDist idW)) ∫-expDist-id

  sqD-integral : ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH sqW) ≈ 1# + 1#
  sqD-integral = trans (sym (∫-expDist sqW)) ∫-expDist-sq

  idB : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH idW))
  idB = Is-resp finite (sym idD-integral) (Is-1 finite)

  sqB : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH sqW))
  sqB = Is-resp finite (sym sqD-integral) (Is-+ finite (Is-1 finite) (Is-1 finite))

  zeroB : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (constW 0#)))
  zeroB = Is-resp finite (sym (zero-integral negExpH expNrm)) (Is-0 finite)

  -- the mean, as an instance of `E-atᴵ-dens`
  idD : ITest (densDist negExpH expNrm)
  idD = densI negExpH expNrm idW (constW 0#) idB zeroB

  E-atᴵ-idD : E-atᴵ (densDist negExpH expNrm) idD
    ≃ (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH idW) − ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (constW 0#)) [ idB , zeroB ])
  E-atᴵ-idD = E-atᴵ-dens negExpH expNrm idW (constW 0#) idB zeroB

  -- the second moment
  sqD : ITest (densDist negExpH expNrm)
  sqD = densI negExpH expNrm sqW (constW 0#) sqB zeroB

  E-atᴵ-sqD : E-atᴵ (densDist negExpH expNrm) sqD
    ≃ (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH sqW) − ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (constW 0#)) [ sqB , zeroB ])
  E-atᴵ-sqD = E-atᴵ-dens negExpH expNrm sqW (constW 0#) sqB zeroB
