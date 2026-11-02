{-# OPTIONS --safe --without-K #-}

-- The mean of the half-normal distribution: `E[X] ≃ n` where `n = proj₁ Z-inv` is the normaliser (`Z · n ≈ 1`).
-- The expectation of the identity statistic `xI` (`Inference/PolyDominationOdd`, integrable by domination) reduces to
-- `n ∫₀^∞ x e^{−x²/2} dx` (`HalfNormal.J-hn`), and `Continuous/GaussMean.∫-xφ` gives `∫ x φ = 1`.  So `E[X] ≃ n`, that is
-- `Z · E[X] ≃ 1`-style: `n` is the reciprocal of the Gaussian mass `Z`, and `E[X]` equals it (`√(2/π)` in classical terms).
--   * `E-atᴵ-xI : E-atᴵ halfNormal xI ≃ (n − 0# [ nB , Is-0 finite ])`, with `nB : Bnd n` read off from the integrability of x.
module QBS.Inference.HalfNormalMean where

open import Data.Product.Base using (proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMean using (module GaussMean)
open import QBS.Continuous.GaussInverse using (module GaussInverse)
open import QBS.Inference.HalfNormal using (module HalfNormal)
open import QBS.Inference.PolyDominationOdd using (module PolyDominationOdd)
open import QBS.Inference.ExpectationInt using (module ExpectationInt)

module HalfNormalMean (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; 0#; 1#; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-identityʳ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0)
  open Weights (lemOf lem₁) using (WQ)
  open ExpDist lem₁ using (idW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open GaussHalfLine lem₁ using (phiH; gMomH)
  open GaussMean lem₁ using (∫-xφ)
  open GaussInverse lem₁ using (Z-inv)
  open HalfNormal lem₁ using (toC; module WithInverse)
  open WithInverse (proj₁ Z-inv) (proj₂ Z-inv) using (halfNormal; J-hn; J-zero)
  open PolyDominationOdd lem₁ using (xI)
  open ExpectationInt lem₁ using (E-atᴵ; ITest)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open ITest
  open Hom

  -- the normaliser
  n : ∣A∣
  n = proj₁ Z-inv

  x-eq : ∀ x → map (mulH {WQ} phiH idW) ⟨$⟩ x ≈ map (gMomH 1) ⟨$⟩ x
  x-eq x = trans (*-comm _ _) (*-cong (sym (*-identityʳ x)) refl)

  -- n ∫ φ x = n
  ∫-hnX : n * ∫ᴹ {WQ} lebPre (mulH {WQ} phiH idW) ≈ n
  ∫-hnX = trans (*-cong refl (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH idW} {gMomH 1} x-eq) ∫-xφ)) (*-identityʳ n)

  J-X : J (m halfNormal) (λ r → map (toC idW) ⟨$⟩ (α halfNormal ⟨$⟩ r))
      (map-random (toC idW) {α halfNormal} (α-random halfNormal)) ≈ n
  J-X = trans (J-hn idW) ∫-hnX

  nB : Bnd n
  nB = Is-resp finite J-X (pos-int xI)

  -- E[X] ≃ n
  E-atᴵ-xI : E-atᴵ halfNormal xI ≃ (n − 0# [ nB , Is-0 finite ])
  E-atᴵ-xI = mk≃ 0# (Is-0 finite) (trans (+-cong (+-cong J-X refl) refl) (sym (+-cong (+-cong refl J-zero) refl)))
