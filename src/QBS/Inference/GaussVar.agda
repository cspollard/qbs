{-# OPTIONS --safe --without-K #-}

-- The variance of N(μ, s²) under the measure itself (plan 03, "Information quantities").  For finite s, l (s l ≈ 1)
-- and finite μ ≥ 0, with `gaussμ` (mean μ) and `gaussμ⁻` (mean −μ) from `Inference/GaussShift`:
--   * centred second moments as values in [0, ∞]: ∫ (x − μ)² dN(μ, s²) ≈ s² (`cvar`) and ∫ (x + μ)² dN(−μ, s²) ≈ s²
--     (`cvar⁻`);
--   * the signed mean and variance of the identity test (`SignedTest.idT`): E X ≃ μ, Var X ≃ s² (`Ex-id`,
--     `Var-gaussμ`), and E X ≃ −μ, Var X ≃ s² under N(−μ, s²) (`Ex-id⁻`, `Var-gaussμ⁻`).
-- Route: `GaussShift.∫-gaussμ` moves the shift into the test; (x ↦ x − μ) ∘ (x ↦ x + μ) is the identity on RQ
-- pointwise (`RealShift.shift-inl`/`shift-inr-le`/`shift-inr-gt` and the matching facts for `shiftNegRH`), so `cvar`
-- is `GaussScale.second`.  For the signed form, idT ∘ shift ≐ idT + μ (as `GaussShift.shift-id`), then
-- `SignedExpect.Ex-cong`/`Ex-+`/`Ex-const`, E X ≃ 0 under N(0, s²) (`GaussShift.sym-X`), and `SignedVar.Var-shift`
-- with the variance under N(0, s²) from `second`.
--   Skeleton: holes first.
module QBS.Inference.GaussVar where

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
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealShift using (module RealShift)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Inference.GaussReal using (module GaussReal)
open import QBS.Inference.GaussShift using (module GaussShift)

module GaussVar (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; _≃_; ι; -S_; finite)
  open SubSemiring finite using (Is-*)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open RealShift lem₁ using (shiftRH; shiftNegRH)
  open SignedTest lem₁ using (idT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Var)
  open GaussReal lem₁ using (Q2)
  open GaussShift lem₁ using (gaussμ; gaussμ⁻)

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) (μ : ∣A∣) (μB : Bnd μ) where

    -- centred second moments
    cvar : ∫ᴹ {RQ} (ιPre {RQ} (gaussμ s l sl sB lB μ μB)) (_∘H_ S Q2 (shiftNegRH μ μB)) ≈ s * s
    cvar = ?

    cvar⁻ : ∫ᴹ {RQ} (ιPre {RQ} (gaussμ⁻ s l sl sB lB μ μB)) (_∘H_ S Q2 (shiftRH μ μB)) ≈ s * s
    cvar⁻ = ?

    -- mean μ and variance s² of the identity
    Int-id : Int (ιPre {RQ} (gaussμ s l sl sB lB μ μB)) idT
    Int-id = ?

    Int-sq : Int (ιPre {RQ} (gaussμ s l sl sB lB μ μB)) (SignedTest._*T_ lem₁ idT idT)
    Int-sq = ?

    Ex-id : Ex (ιPre {RQ} (gaussμ s l sl sB lB μ μB)) idT Int-id ≃ ι μB
    Ex-id = ?

    Var-gaussμ : Var (gaussμ s l sl sB lB μ μB) idT (Int-id , Int-sq) ≃ ι (Is-* sB sB)
    Var-gaussμ = ?

    -- mean −μ and variance s²
    Int-id⁻ : Int (ιPre {RQ} (gaussμ⁻ s l sl sB lB μ μB)) idT
    Int-id⁻ = ?

    Int-sq⁻ : Int (ιPre {RQ} (gaussμ⁻ s l sl sB lB μ μB)) (SignedTest._*T_ lem₁ idT idT)
    Int-sq⁻ = ?

    Ex-id⁻ : Ex (ιPre {RQ} (gaussμ⁻ s l sl sB lB μ μB)) idT Int-id⁻ ≃ -S (ι μB)
    Ex-id⁻ = ?

    Var-gaussμ⁻ : Var (gaussμ⁻ s l sl sB lB μ μB) idT (Int-id⁻ , Int-sq⁻) ≃ ι (Is-* sB sB)
    Var-gaussμ⁻ = ?
