{-# OPTIONS --safe --without-K #-}

-- The Gaussian absolute moment on the real line: `E|X| ≃ n′ (1 + 1)`, where `n′ = n · ½` is the normaliser of `gaussR`
-- (`(Z + Z) · n′ ≈ 1`, `Inference/GaussReal`), so `(Z + Z) · E|X| ≃ 2` (`√(2/π)` classically).
-- The statistic `|x|` is `absR = copairH idW idW` (`inl x ↦ x`, `inr x ↦ x`, negative part 0).  Each half-line integral is
-- `∫₀^∞ x e^{−x²/2} dx = 1` (`Continuous/GaussMean.∫-xφ`), so `RH absR = n′ (1 + 1)`; integrability follows from
-- `Bnd n′` (read off from the integrability of the one-sided statistic `Xp`, whose value is `n′ · 1`).
--   * `E-atᴵ-abs : E-atᴵ gaussR absI ≃ (n′ (1 + 1) − 0 [ … ])`;
--   * `Z2-abs : (Z + Z) · (n′ (1 + 1)) ≈ 1 + 1`.
module QBS.Inference.GaussRealAbs where

open import Data.Product.Base using (proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.GaussMean using (module GaussMean)
open import QBS.Inference.SymExpectation using (module SymExpectation)
open import QBS.Inference.GaussReal using (module GaussReal)
import QBS.Inference.ExpectationInt as EI

module GaussRealAbs (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
    using (_≈_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-assoc; *-identityˡ; *-identityʳ; +-identityʳ)
  open Bounded A using (Bnd; finite; _≃_; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+; Is-*)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH; copairH)
  open ExpDist lem₁ using (idW)
  open GaussHalfLine lem₁ using (phiH; gMomH)
  open GaussMoment lem₁ using (Z)
  open GaussMean lem₁ using (∫-xφ)
  open SymExpectation lem₁ using (≃-≈)
  open GaussReal lem₁ using (module G; gaussR; n′; nn; zeroW; zeroR; Xp; bXp; Xp-l; Xp-r; RH-zero; bZero)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open Hom

  absR : Hom S RQ WQ
  absR = copairH idW idW

  x-eq : ∀ x → map (mulH {WQ} phiH idW) ⟨$⟩ x ≈ map (gMomH 1) ⟨$⟩ x
  x-eq x = trans (*-comm _ _) (*-cong (sym (*-identityʳ x)) refl)

  -- ∫₀^∞ x φ = 1, in the form of the half-line integrals of the statistics
  A1 : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH idW) ≈ 1#
  A1 = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH idW} {gMomH 1} x-eq) ∫-xφ

  Abs-l : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S absR inlH)) ≈ 1#
  Abs-l = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S absR inlH)} {mulH {WQ} phiH idW} (λ x → refl)) A1

  Abs-r : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S absR inrH)) ≈ 1#
  Abs-r = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S absR inrH)} {mulH {WQ} phiH idW} (λ x → refl)) A1

  RH-abs : G.RH absR ≈ n′ * (1# + 1#)
  RH-abs = *-cong refl (+-cong Abs-l Abs-r)

  -- the one-sided statistic has value n′, so n′ is finite
  RH-Xp : G.RH Xp ≈ n′
  RH-Xp = trans (*-cong refl (trans (+-cong (trans Xp-l A1) Xp-r) (+-identityʳ 1#))) (*-identityʳ n′)

  n′B : Bnd n′
  n′B = Is-resp finite RH-Xp bXp

  two : Bnd (n′ * (1# + 1#))
  two = Is-* finite n′B (Is-+ finite (Is-1 finite) (Is-1 finite))

  bAbs : Bnd (G.RH absR)
  bAbs = Is-resp finite (sym RH-abs) two

  absI : ITest gaussR
  absI = G.symI absR zeroR bAbs bZero

  -- E|X| ≃ n′ (1 + 1)
  E-atᴵ-abs : E-atᴵ gaussR absI ≃ ((n′ * (1# + 1#)) − 0# [ two , Is-0 finite ])
  E-atᴵ-abs = ≃-trans′ (G.E-atᴵ-sym absR zeroR bAbs bZero) (≃-≈ RH-abs RH-zero)
    where open Bounded A using () renaming (≃-trans to ≃-trans′)

  -- (Z + Z) · E|X| = 2
  Z2-abs : (Z + Z) * (n′ * (1# + 1#)) ≈ 1# + 1#
  Z2-abs = trans (sym (*-assoc (Z + Z) n′ (1# + 1#))) (trans (*-cong nn refl) (*-identityˡ (1# + 1#)))
