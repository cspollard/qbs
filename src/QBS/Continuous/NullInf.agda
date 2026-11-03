{-# OPTIONS --safe --without-K #-}

-- Where an integrable test is infinite nothing is seen by the integral (plan 03, "Signed dominated convergence").
-- For a test g on X with ∫ g finite:
--   * `finχ g`: the indicator of {x | g x is bounded by a rational} (`indH` after g), with `finχ-in`/`finχ-out`;
--   * `∫-infχ`: the complementary indicator integrates to 0;  `∫-null`: so does u · [g = ∞] for every test u;
--   * `∫-off-inf`: tests that agree wherever g is finite have the same integral;  `∫-fin-cut`: ∫ (finχ g · u) ≈ ∫ u.
-- Route: k · [g = ∞] ≤ g for every k, so k · ∫ [g = ∞] ≤ ∫ g ≤ N and ∫ [g = ∞] ≤ ½ᵏ (`Fatou.approx`); u · [g = ∞] is
-- the supremum of j · [g = ∞] ⊓ u (`SupTest.∫ᴹ-sup`); pointwise u ≈ finχ g · u + [g = ∞] · u by excluded middle on
-- finiteness of g x.  Borel: {r | BndQ (α r)} is ⋃_M {r | M ∉ α r}, the complement of a level set (`Meas`).
--   Skeleton: holes first.
module QBS.Continuous.NullInf where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty using (⊥)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)

module NullInf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open QBS
  open Hom

  module _ {X : QBS S} where

    -- [g x finite] and [g x = ∞]
    finχ infχ : Hom S X WQ → Hom S X WQ
    finχ = ?
    infχ = ?

    finχ-in : ∀ g x → BndQ (map g ⟨$⟩ x) → map (finχ g) ⟨$⟩ x ≈ 1#
    finχ-in = ?

    finχ-out : ∀ g x → (BndQ (map g ⟨$⟩ x) → ⊥) → map (finχ g) ⟨$⟩ x ≈ 0#
    finχ-out = ?

    infχ-in : ∀ g x → (BndQ (map g ⟨$⟩ x) → ⊥) → map (infχ g) ⟨$⟩ x ≈ 1#
    infχ-in = ?

    infχ-out : ∀ g x → BndQ (map g ⟨$⟩ x) → map (infχ g) ⟨$⟩ x ≈ 0#
    infχ-out = ?

    ∫-infχ : ∀ (p : C.Pre (XW X)) g → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (infχ g) ≈ 0#
    ∫-infχ = ?

    ∫-null : ∀ (p : C.Pre (XW X)) g u → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (mulH {X} (infχ g) u) ≈ 0#
    ∫-null = ?

    ∫-fin-cut : ∀ (p : C.Pre (XW X)) g u → Bnd (∫ᴹ {X} p g) → ∫ᴹ {X} p (mulH {X} (finχ g) u) ≈ ∫ᴹ {X} p u
    ∫-fin-cut = ?

    ∫-off-inf : ∀ (p : C.Pre (XW X)) g u v → Bnd (∫ᴹ {X} p g) →
      (∀ x → BndQ (map g ⟨$⟩ x) → map u ⟨$⟩ x ≈ map v ⟨$⟩ x) → ∫ᴹ {X} p u ≈ ∫ᴹ {X} p v
    ∫-off-inf = ?
