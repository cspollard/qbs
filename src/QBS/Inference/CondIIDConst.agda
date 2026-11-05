{-# OPTIONS --safe --without-K #-}

-- A constant test integrates to the constant times the mass (plan 05, item 48 helper):
--   `∫-constW`: ∫ c dq ≈ c · ∫ 1 dq, for an s-finite measure q (compare `SFiniteSum.∫ᴹ-scale`).
-- Used by `CondIID.joint-fst`.
-- Route: `J-cong` pointwise on the samples (w · c ≈ (c · w) · 1) against `scalePre c q`, then `∫ᴹ-scale`.

module QBS.Inference.CondIIDConst where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Core
open import QBS.Analysis.Omega
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Classical using (LEM₀)

module CondIIDConst (lem : LEM₀) where
  open JParam lem
  open Weights lem using (WQ; constW)
  open OmegaSemiring A using (_≈_; _*_; 1#; trans; *-comm; *-identityʳ; sym) renaming (Carrier to ∣A∣)
  open SFinite lem using (XW; ∫ᴹ; ψ; mψ; module C)
  open SFiniteSum lem using (scalePre; ∫ᴹ-scale)
  open C using (Pre)
  open C.Pre
  open QBS
  open Hom

  ∫-constW : ∀ {X : QBS S} (q : Pre (XW X)) (c : ∣A∣) → ∫ᴹ {X} q (constW {X} c) ≈ c * ∫ᴹ {X} q (constW {X} 1#)
  ∫-constW {X} q c = trans
    (J-cong (m q) {ψ {X} q (constW {X} c)} {ψ {X} (scalePre {X} c q) (constW {X} 1#)}
      (mψ {X} q (constW {X} c)) (mψ {X} (scalePre {X} c q) (constW {X} 1#))
      (λ r → trans (*-comm _ _) (sym (*-identityʳ _))))
    (∫ᴹ-scale {X} c q (constW {X} 1#))
