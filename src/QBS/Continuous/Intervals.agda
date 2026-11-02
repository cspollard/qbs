{-# OPTIONS --safe --without-K #-}

-- Interval tests on `WQ = [0,∞]` (plan 03, "Uniqueness on the half-line").  Skeleton: holes first.
--   * `χIv a b`, the indicator of [a, b) (for cuts a, b), and `χInf`, the indicator of {∞};
--   * `dy n m = m / 2ⁿ` and the dyadic intervals `χI n m = χIv (dy n m) (dy n (m+1))`, with `χI-split`, the halving of a
--     dyadic interval.
-- Membership `a ≤ x` (`Ge`, the order of cuts at the level of `Set`) is decided by excluded middle.  The tests are
-- measurable because `{r | a ≤ h r}` is Borel for every threshold-measurable h: it is the countable intersection of the
-- threshold sets {r | q ∈ h r} over the rationals q ∈ a (`ge-borel`).
module QBS.Continuous.Intervals where

open import Level using (lift)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc; _*_)
open import Data.Product.Base using (_×_)
open import Data.Empty using (⊥)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Borel)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (module Cut)
open Cut using (mem)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)

module Intervals (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#) renaming (Carrier to ∣A∣; _*_ to _·_)
  open Meas lem using (Meas)
  open Exp A using (natE)
  open Arch (lowerRealsArch lem) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open Weights lem using (WQ)
  open QBS
  open Hom

  -- `a ≤ x`, at the level of `Set` (it is `_≤_` of the cuts, unfolded to membership, so that it can be a Borel predicate)
  Ge : ∣A∣ → ∣A∣ → Set
  Ge a x = ∀ q → mem a q → mem x q

  -- membership of a point of [0,∞] in [a, b), and in {∞}
  InIv : ∣A∣ → ∣A∣ → ∣A∣ → Set
  InIv a b x = Ge a x × (Ge b x → ⊥)

  InInf : ∣A∣ → Set
  InInf x = ∀ k → Ge (natE k) x

  -- `a ≤ h r` is a Borel condition on r
  ge-borel : ∀ a {h : R₁ → ∣A∣} → Meas h → Borel (λ c → Ge a (h (lift c)))
  ge-borel = ?

  ----------------------------------------------------------------------------
  -- the indicator tests

  χIv : ∣A∣ → ∣A∣ → Hom S WQ WQ
  χIv = ?

  χIv-in : ∀ a b x → InIv a b x → map (χIv a b) ⟨$⟩ x ≈ 1#
  χIv-in = ?

  χIv-out : ∀ a b x → (InIv a b x → ⊥) → map (χIv a b) ⟨$⟩ x ≈ 0#
  χIv-out = ?

  χInf : Hom S WQ WQ
  χInf = ?

  χInf-in : ∀ x → InInf x → map χInf ⟨$⟩ x ≈ 1#
  χInf-in = ?

  χInf-out : ∀ x → (InInf x → ⊥) → map χInf ⟨$⟩ x ≈ 0#
  χInf-out = ?

  ----------------------------------------------------------------------------
  -- dyadic intervals

  dy : ℕ → ℕ → ∣A∣
  dy n m = natE m · hp n

  χI : ℕ → ℕ → Hom S WQ WQ
  χI n m = χIv (dy n m) (dy n (suc m))

  -- [m/2ⁿ, (m+1)/2ⁿ) is the disjoint union of its two halves
  χI-split : ∀ n m x → map (χI n m) ⟨$⟩ x ≈ (map (χI (suc n) (2 * m)) ⟨$⟩ x) + (map (χI (suc n) (suc (2 * m))) ⟨$⟩ x)
  χI-split = ?
