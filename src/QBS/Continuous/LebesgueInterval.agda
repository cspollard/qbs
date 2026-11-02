{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure of every interval, and the characterisation of Lebesgue measure by its interval masses (plan 03,
-- "Uniqueness on the half-line").  Skeleton: holes first.  No subtraction: "λ[a,b) = b − a" is stated as
-- `a + λ[a,b) ≈ b`.
--   * `leb-Iv`: for cuts a ≤ b with b finite, `a + ∫ lebPre χ[a,b) ≈ b`.  Approximate [a,b) from inside by unions of
--     dyadic intervals (`LebesgueDyadic.leb-χI`) and pass to the limit (`J-⨆`).
--   * `leb-unique`: a measure with these interval masses and no mass at ∞ is Lebesgue measure
--     (`UniquenessWQ.uniqWQ`; the dyadic masses follow by cancelling the finite left endpoint).  This is the tool for
--     scaling, translation and change of variables: compute interval masses only.
module QBS.Continuous.LebesgueInterval where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)

module LebesgueInterval (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; module C)
  open C using (Pre)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (χIv; χInf)
  open QBS
  open Hom

  leb-Iv : ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} lebPre (χIv a b) ≈ b
  leb-Iv = ?

  leb-unique : ∀ (μ : Pre (XW WQ)) → (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} μ (χIv a b) ≈ b) →
    ∫ᴹ {WQ} μ χInf ≈ 0# → _≈ᴹ_ {WQ} μ lebPre
  leb-unique = ?
