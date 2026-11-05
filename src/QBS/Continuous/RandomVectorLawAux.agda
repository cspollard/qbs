{-# OPTIONS --safe --without-K #-}

-- Push-forward of expectations along a map into any space (plan 05, item 55b; helper for `RandomVectorLaw`).
--   * `∫-law`: ∫ f d(ιPre (mapPre h P)) ≈ ∫ f ∘ h d(ιPre P);
--   * `Int-law`, `Int-law⁻`, `Ex-law`: integrability both ways, and the expectation of f against the image is that of f ∘ h.
-- Route: `SFiniteIncl.ι-nat` then `SFinite.∫ᴹ-map`, as `GaussVarAux.∫-map` (there on the real line only); the rest is
-- `bnd≈` and `mk≃` along it.
module QBS.Continuous.RandomVectorLawAux where

open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module RandomVectorLawAux (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#; sym; trans; +-cong)
  open Bounded A using (_≃_; mk≃; finite)
  open SubSemiring finite using (Is-0)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-map; XW; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-nat)
  open SignedTest lem₁ using (SgT; posT; negT; _∘T_)
  open SignedExpect lem₁ using (Int; Ex; bnd≈)
  open QBS
  open Hom

  module _ {Ω Y : QBS S} (P : C.Pre Ω) (h : Hom S Ω Y) where

    ∫-law : ∀ f → ∫ᴹ {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f ≈ ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S f h)
    ∫-law f = trans (ι-nat {Ω} {Y} h P f) (∫ᴹ-map {Ω} {Y} h (ιPre {Ω} P) f)

    Int-law : ∀ f → Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f → Int {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h)
    Int-law f (i⁺ , i⁻) = bnd≈ {Ω} (sym (∫-law (posT f))) i⁺ , bnd≈ {Ω} (sym (∫-law (negT f))) i⁻

    Int-law⁻ : ∀ f → Int {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h) → Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f
    Int-law⁻ f (i⁺ , i⁻) = bnd≈ {Y} (∫-law (posT f)) i⁺ , bnd≈ {Y} (∫-law (negT f)) i⁻

    Ex-law : ∀ f (i : Int {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f) →
      Ex {Y} (ιPre {Y} (C.mapPre {Ω} {Y} h P)) f i ≃ Ex {Ω} (ιPre {Ω} P) (_∘T_ {Ω} {Y} f h) (Int-law f i)
    Ex-law f i = mk≃ 0# Is-0 (+-cong (+-cong (∫-law (posT f)) (sym (∫-law (negT f)))) (OmegaSemiring.refl A))
