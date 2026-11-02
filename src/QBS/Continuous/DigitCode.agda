{-# OPTIONS --safe --without-K #-}

-- The digit code of `[0,∞]` into Cantor space, and its decoding (plan 03, "Uniqueness on the half-line").  Skeleton:
-- holes first.  `docs/UniquenessLit.md` has the route.
--   * `digits x`: the unary integer part `true^⌊x⌋ false`, then the binary digits of the fractional part of x (most
--     significant first, never ending in all `true`); ∞ goes to the all-true sequence.  Digits are decided by excluded
--     middle.
--   * `code : Hom S WQ ℛ`.  It is a morphism because every bit of `digits (α r)` is, as a function of r, a finite Boolean
--     combination of the Borel sets `{r | q ≤ α r}` (`Intervals.ge-borel`) for dyadic q (`meas-digits`).
--   * `decode : Hom S ℛ WQ`, a `Meas` function (the length of the leading run of `true`s plus the expansion of the bits
--     after the block), with `decode-code : decode (code x) ≈ x`.  So every test h equals `(h ∘ decode) ∘ code`.
--   * `code-cell`: the cell `Cell k w` pulls back to the dyadic interval [k + val w / 2ⁿ, k + (val w + 1) / 2ⁿ), n = |w|;
--     `code-top`: the all-true point pulls back to {∞}.
module QBS.Continuous.DigitCode where

open import Level using (lift; lower)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.List.Base using ([]; _∷_; length)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import QBS.Core
import QBS.Probes as Probes
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Cantor; Measurable)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cells using (Word; Cell; Top)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.Intervals using (module Intervals)

module DigitCode (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_) renaming (Carrier to ∣A∣)
  open Meas lem using (Meas)
  open Indicators A lem using (χ)
  open Weights lem using (WQ)
  open Intervals lem using (χI; χInf)
  open QBS
  open Hom

  ℛ : QBS S
  ℛ = Probes.ℛQ S

  -- the binary value of a word, most significant bit first
  val : Word → ℕ
  val [] = zero
  val (b ∷ w) = (if b then 2 ^ length w else zero) + val w

  ----------------------------------------------------------------------------
  -- the code

  digits : ∣A∣ → Cantor
  digits = ?

  -- equal points have equal digits
  digits-cong : ∀ {x y} → x ≈ y → ∀ i → digits x i ≡ digits y i
  digits-cong = ?

  -- the digits of a random point are a measurable map
  meas-digits : ∀ {h : R₁ → ∣A∣} → Meas h → Measurable (λ c → digits (h (lift c)))
  meas-digits = ?

  code : Hom S WQ ℛ
  code = ?

  code-pt : ∀ x i → lower (map code ⟨$⟩ x) i ≡ digits x i
  code-pt = ?

  ----------------------------------------------------------------------------
  -- the decoding

  decode : Hom S ℛ WQ
  decode = ?

  decode-code : ∀ x → map decode ⟨$⟩ (map code ⟨$⟩ x) ≈ x
  decode-code = ?

  ----------------------------------------------------------------------------
  -- cells are dyadic intervals, the all-true point is ∞

  code-cell : ∀ k w x → χ (Cell k w) (map code ⟨$⟩ x) ≈ map (χI (length w) (k * 2 ^ length w + val w)) ⟨$⟩ x
  code-cell = ?

  code-top : ∀ x → χ Top (map code ⟨$⟩ x) ≈ map χInf ⟨$⟩ x
  code-top = ?
