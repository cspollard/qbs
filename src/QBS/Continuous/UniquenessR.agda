{-# OPTIONS --safe --without-K #-}

-- Uniqueness of s-finite measures on Cantor space `ℛ = Probes.ℛQ S`, in the σ-finite form (plan 03, "Uniqueness on the
-- half-line").  Skeleton: holes first.  Cantor space is the disjoint union of the blocks `Blk k = {trueᵏ false …}` and
-- the all-true point `Top` (`Borel/Cells`).  Two measures `μ ν : Pre (XW ℛ)` are equal (`uniqR : μ ≈ᴹ ν`) when
--   * they agree on every cell `Cell k w` (`agreeCell`),
--   * each block has finite μ-mass (`finBlk`), and
--   * they agree on `Top` (`agreeTop`).
-- Route.
--   * `∫ᴹ-split`: every test splits as its part on `Top` plus the series of its parts on the blocks.
--   * `agree-blkCyl`: on a block, agreement on cells gives agreement on every cylinder (`Cells.cyl-refine`).
--   * `agree-blk`: on a block, agreement on cylinders gives agreement on every test.  The part of `p` on the block is
--     the weighted pushforward of `m p` with weight `w · χ Blk` along the probe of p, which has finite mass, so
--     `Analysis/UniquenessWeighted.uniqW` applies.
--   * `agree-top`: `Top` is a single point, so the part of a test g on it is `g(all-true)` times the mass of `Top`.
module QBS.Continuous.UniquenessR where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ)

open import QBS.Core
import QBS.Probes as Probes
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Borel)
open import QBS.Borel.PiLambda using (Cyl; Cyl-∩)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Borel.Cells using (Word; Blk; Cell; Top; cylBlk; borelBlk; borelCell; borelTop)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.UniquenessWeighted using (module UniquenessWeighted)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)

module UniquenessR (lem : LEM₀) where
  open Lebesgue lem using (A; J)
  open OmegaSemiring A using (_≈_; _+_; _*_) renaming (Carrier to ∣A∣)
  open Series A using (∑ᶠ)
  open Bounded A using (Bnd)
  open Indicators A lem using (χ)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; _≈ᴹ_; module C)
  open C using (Pre)
  open SFiniteReweight lem using (mulH)
  open UniquenessWeighted lem using (uniqW)
  open QBS
  open Hom

  ℛ : QBS S
  ℛ = Probes.ℛQ S

  -- the indicator test of a Borel set of Cantor space
  χR : ∀ {U} → Borel U → Hom S ℛ WQ
  χR = ?

  χR-pt : ∀ {U} (b : Borel U) r → map (χR b) ⟨$⟩ r ≈ χ U r
  χR-pt = ?

  -- the part of a test on the all-true point, and on the k-th block
  onTop : Hom S ℛ WQ → Hom S ℛ WQ
  onTop g = mulH {ℛ} (χR borelTop) g

  onBlk : ℕ → Hom S ℛ WQ → Hom S ℛ WQ
  onBlk k g = mulH {ℛ} (χR (borelBlk k)) g

  -- every test splits along the all-true point and the blocks (excluded middle: a sequence is all-true or in a block)
  ∫ᴹ-split : ∀ (p : Pre (XW ℛ)) (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} p g ≈ ∫ᴹ {ℛ} p (onTop g) + ∑ᶠ (λ k → ∫ᴹ {ℛ} p (onBlk k g))
  ∫ᴹ-split = ?

  module _ (μ ν : Pre (XW ℛ))
           (agreeCell : ∀ k w → ∫ᴹ {ℛ} μ (χR (borelCell k w)) ≈ ∫ᴹ {ℛ} ν (χR (borelCell k w)))
           (finBlk : ∀ k → Bnd (∫ᴹ {ℛ} μ (χR (borelBlk k))))
           (agreeTop : ∫ᴹ {ℛ} μ (χR borelTop) ≈ ∫ᴹ {ℛ} ν (χR borelTop)) where

    -- on a block, agreement on the cells gives agreement on every cylinder
    agree-blkCyl : ∀ k {C} (c : Cyl C) →
      ∫ᴹ {ℛ} μ (χR (Cyl-borel (Cyl-∩ (cylBlk k) c))) ≈ ∫ᴹ {ℛ} ν (χR (Cyl-borel (Cyl-∩ (cylBlk k) c)))
    agree-blkCyl = ?

    -- on a block, every test (by `UniquenessWeighted.uniqW`)
    agree-blk : ∀ k (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} μ (onBlk k g) ≈ ∫ᴹ {ℛ} ν (onBlk k g)
    agree-blk = ?

    -- on the all-true point, every test
    agree-top : ∀ (g : Hom S ℛ WQ) → ∫ᴹ {ℛ} μ (onTop g) ≈ ∫ᴹ {ℛ} ν (onTop g)
    agree-top = ?

    uniqR : _≈ᴹ_ {ℛ} μ ν
    uniqR = ?
