{-# OPTIONS --safe --without-K #-}

-- Uniqueness of measures on the half-line `WQ = [0,∞]` (plan 03, "Uniqueness on the half-line"; `docs/UniquenessLit.md`).
-- Skeleton: holes first.  Two measures `μ ν : Pre (XW WQ)` are equal (`uniqWQ : μ ≈ᴹ ν`) when
--   * they agree on every dyadic interval [m/2ⁿ, (m+1)/2ⁿ) (`agreeI`),
--   * μ is finite on each [k, k+1) (`finI`), and
--   * they agree on {∞} (`agreeInf`; Lebesgue measure and every density give it mass 0).
-- Route: every test h equals `(h ∘ decode) ∘ code` (`DigitCode.decode-code`), so `∫ᴹ μ h ≈ ∫ᴹ (mapM code μ) (h ∘ decode)`
-- (`SFinite.∫ᴹ-map`).  The pushforwards along `code` are measures on Cantor space whose cells and all-true point have the
-- masses of dyadic intervals and of {∞} (`pushCell`, `pushTop`), so `UniquenessR.uniqR` applies.
module QBS.Continuous.UniquenessWQ where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; _+_; _*_; _^_)
open import Data.List.Base using (length)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Cells using (borelBlk; borelCell; borelTop)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitCode using (module DigitCode)
open import QBS.Continuous.UniquenessR using (module UniquenessR)

module UniquenessWQ (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open C using (Pre)
  open Intervals lem using (χI; χInf)
  open DigitCode lem using (ℛ; code; decode; val)
  open UniquenessR lem using (χR; uniqR)
  open QBS
  open Hom

  -- every test factors through the code
  test-factor : ∀ (h : Hom S WQ WQ) x → map h ⟨$⟩ x ≈ map (_∘H_ S (_∘H_ S h decode) code) ⟨$⟩ x
  test-factor = ?

  -- the pushforward along the code: cells are dyadic intervals, blocks are unit intervals, the all-true point is ∞
  pushCell : ∀ (p : Pre (XW WQ)) k w →
    ∫ᴹ {ℛ} (mapM code p) (χR (borelCell k w)) ≈ ∫ᴹ {WQ} p (χI (length w) (k * 2 ^ length w + val w))
  pushCell = ?

  pushBlk : ∀ (p : Pre (XW WQ)) k → ∫ᴹ {ℛ} (mapM code p) (χR (borelBlk k)) ≈ ∫ᴹ {WQ} p (χI 0 k)
  pushBlk = ?

  pushTop : ∀ (p : Pre (XW WQ)) → ∫ᴹ {ℛ} (mapM code p) (χR borelTop) ≈ ∫ᴹ {WQ} p χInf
  pushTop = ?

  module _ (μ ν : Pre (XW WQ))
           (agreeI : ∀ n m → ∫ᴹ {WQ} μ (χI n m) ≈ ∫ᴹ {WQ} ν (χI n m))
           (finI : ∀ k → Bnd (∫ᴹ {WQ} μ (χI 0 k)))
           (agreeInf : ∫ᴹ {WQ} μ χInf ≈ ∫ᴹ {WQ} ν χInf) where

    -- the pushforwards are equal as measures on Cantor space
    uniqPush : _≈ᴹ_ {ℛ} (mapM code μ) (mapM code ν)
    uniqPush = ?

    uniqWQ : _≈ᴹ_ {WQ} μ ν
    uniqWQ = ?
