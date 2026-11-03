{-# OPTIONS --safe --without-K #-}

-- The Gaussian N(μ, s²) on the real line for every finite mean μ and scale s, and its mean (plan 03, "Translation and
-- products").  `gaussμ = mapPre (x ↦ x + μ) (GaussScale.gaussσ)` for μ ≥ 0 and `gaussμ⁻` with x ↦ x − μ, so
--   * `∫-gaussμ f : ∫ f dN(μ, s²) ≈ ∫ f(x + μ) dN(0, s²)` (`SFiniteIncl.ι-nat`, `SFinite.∫ᴹ-map`);
--   * the mean without subtraction: `mean : E[X⁺] ≈ μ + E[X⁻]` (X⁺ = `Xp`, X⁻ = `Xn` of `GaussReal`), and
--     `mean⁻ : μ + E[X⁺] ≈ E[X⁻]` for N(−μ, s²).
-- Route for `mean`: pointwise X⁺(y + μ) + X⁻(y) ≈ X⁺(y) + X⁻(y + μ) + μ on RQ (`shift-id`, by cases on y with
-- `RealShift.shift-inl`/`shift-inr-le`/`shift-inr-gt`), integrate (`UniquenessRQAlg.∫ᴹ-addX`), use the symmetry
-- E[X⁺] ≈ E[X⁻] under N(0, s²) (`sym-X`) and cancel the finite E[X⁻] (`fin-X`, `BoundedCancel.cancel-bnd`).
--   Skeleton: holes first.
module QBS.Inference.GaussShift where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealShift using (module RealShift)
open import QBS.Continuous.UniquenessRQAlg using (module UniquenessRQAlg)
open import QBS.Inference.GaussReal using (module GaussReal)
open import QBS.Inference.GaussScale using (module GaussScale)

module GaussShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open RealShift lem₁ using (shiftRH; shiftNegRH)
  open UniquenessRQAlg (lemOf lem₁) using (addX)
  open GaussReal lem₁ using (Xp; Xn)
  open GaussScale lem₁ using (gaussσ)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) (μ : ∣A∣) (μB : Bnd μ) where

    N₀ : Pre RQ
    N₀ = gaussσ s l sl sB lB

    -- symmetry and finiteness of the halves of the identity under N(0, s²)
    sym-X : ∫ᴹ {RQ} (ιPre {RQ} N₀) Xp ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) Xn
    sym-X = ?

    fin-X : Bnd (∫ᴹ {RQ} (ιPre {RQ} N₀) Xn)
    fin-X = ?

    -- N(μ, s²) and N(−μ, s²)
    gaussμ gaussμ⁻ : Pre RQ
    gaussμ = C.mapPre {RQ} {RQ} (shiftRH μ μB) N₀
    gaussμ⁻ = C.mapPre {RQ} {RQ} (shiftNegRH μ μB) N₀

    ∫-gaussμ : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} gaussμ) f ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S f (shiftRH μ μB))
    ∫-gaussμ = ?

    ∫-gaussμ⁻ : ∀ (f : Hom S RQ WQ) →
      ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) f ≈ ∫ᴹ {RQ} (ιPre {RQ} N₀) (_∘H_ S f (shiftNegRH μ μB))
    ∫-gaussμ⁻ = ?

    -- X⁺(y + μ) + X⁻(y) ≈ X⁺(y) + X⁻(y + μ) + μ
    shift-id : ∀ y → map (addX {RQ} (_∘H_ S Xp (shiftRH μ μB)) Xn) ⟨$⟩ y
      ≈ (map (addX {RQ} Xp (_∘H_ S Xn (shiftRH μ μB))) ⟨$⟩ y) + μ
    shift-id = ?

    -- E[X] = μ and E[X] = −μ, without subtraction
    mean : ∫ᴹ {RQ} (ιPre {RQ} gaussμ) Xp ≈ μ + ∫ᴹ {RQ} (ιPre {RQ} gaussμ) Xn
    mean = ?

    mean⁻ : μ + ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) Xp ≈ ∫ᴹ {RQ} (ιPre {RQ} gaussμ⁻) Xn
    mean⁻ = ?
