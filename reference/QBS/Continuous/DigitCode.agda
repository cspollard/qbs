{-# OPTIONS --safe --without-K #-}

-- The digit code of `[0,∞]` into Cantor space, and its decoding (used for the uniqueness of measures on the half-line; measure-construction material that lives here for import reasons).
-- `docs/UniquenessLit.md` has the route.  The work is in `Continuous/DigitStream` (the code), `Continuous/DigitDecode` (the
-- decoding), `Analysis/DigitAlg` and `Continuous/DigitCut` (algebra and cut facts); this module assembles the statements.
--   * `digits x`: the unary integer part `true^⌊x⌋ false`, then the binary digits of the fractional part of x (most
--     significant first, never ending in all `true`); ∞ goes to the all-true sequence.  It is the output of a machine that
--     asks "is the threshold ≤ x?" (decided by excluded middle) and halves the dyadic interval containing x.
--   * `code : Hom S WQ ℛ`.  It is a morphism because every bit of `digits (α r)` is, as a function of r, a finite Boolean
--     combination of the Borel sets `{r | a ≤ α r}` (`Intervals.ge-borel`) for dyadic a (`meas-digits`).
--   * `decode : Hom S ℛ WQ`, a `Meas` function (the length of the leading run of `true`s plus the expansion of the bits
--     after the block), with `decode-code : decode (code x) ≈ x`.  So every test h equals `(h ∘ decode) ∘ code`.
--   * `code-cell`: the cell `Cell k w` pulls back to the dyadic interval [k + val w / 2ⁿ, k + (val w + 1) / 2ⁿ), n = |w|;
--     `code-top`: the all-true point pulls back to {∞}.
module QBS.Continuous.DigitCode where

open import Level using (lift; lower)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; _+_; _*_; _^_)
open import Data.List.Base using (length)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

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
import QBS.Continuous.DigitStream as DS
open import QBS.Continuous.DigitStream using (module DigitStream)
open import QBS.Continuous.DigitDecode using (module DigitDecode)

module DigitCode (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; trans; sym) renaming (Carrier to ∣A∣)
  open Meas lem using (Meas; Meas-resp)
  open Indicators A lem using (χ; χ-in; χ-out; case)
  open Weights lem using (WQ)
  open Intervals lem using (χI; χInf; χIv-in; χIv-out; χInf-in; χInf-out)
  open DigitStream lem using (cell-iff; top-iff)
  open DigitDecode lem using (decPt; Meas-dec; decode-digits)
  open QBS
  open Hom

  ℛ : QBS S
  ℛ = Probes.ℛQ S

  -- the binary value of a word, most significant bit first
  val : Word → ℕ
  val = DS.val

  ----------------------------------------------------------------------------
  -- the code

  digits : ∣A∣ → Cantor
  digits = DS.DigitStream.digits lem

  -- equal points have equal digits
  digits-cong : ∀ {x y} → x ≈ y → ∀ i → digits x i ≡ digits y i
  digits-cong = DS.DigitStream.digits-cong lem

  -- the digits of a random point are a measurable map
  meas-digits : ∀ {h : R₁ → ∣A∣} → Meas h → Measurable (λ c → digits (h (lift c)))
  meas-digits mh i b = DS.DigitStream.meas-digits lem mh i b

  code : Hom S WQ ℛ
  code = record
    { map = record { to = λ x → lift (digits x) ; cong = λ e → lift (digits-cong e) }
    ; map-random = λ {α} m → meas-digits {α ⟨$⟩_} m
    }

  code-pt : ∀ x i → lower (map code ⟨$⟩ x) i ≡ digits x i
  code-pt x i = refl

  ----------------------------------------------------------------------------
  -- the decoding

  decode : Hom S ℛ WQ
  decode = Probes.probe S {WQ} {record { to = decPt ; cong = λ e → Meas-resp {decPt} Meas-dec (lower e) }} Meas-dec

  decode-code : ∀ x → map decode ⟨$⟩ (map code ⟨$⟩ x) ≈ x
  decode-code x = decode-digits x

  ----------------------------------------------------------------------------
  -- cells are dyadic intervals, the all-true point is ∞

  code-cell : ∀ k w x → χ (Cell k w) (map code ⟨$⟩ x) ≈ map (χI (length w) (k * 2 ^ length w + val w)) ⟨$⟩ x
  code-cell k w x = case {Cell k w (digits x)}
    (λ c → trans (χ-in (Cell k w) (map code ⟨$⟩ x) c) (sym (χIv-in _ _ x (proj₁ (cell-iff x k w) c))))
    (λ nc → trans (χ-out (Cell k w) (map code ⟨$⟩ x) nc) (sym (χIv-out _ _ x (λ t → nc (proj₂ (cell-iff x k w) t)))))

  code-top : ∀ x → χ Top (map code ⟨$⟩ x) ≈ map χInf ⟨$⟩ x
  code-top x = case {Top (digits x)}
    (λ c → trans (χ-in Top (map code ⟨$⟩ x) c) (sym (χInf-in x (proj₁ (top-iff x) c))))
    (λ nc → trans (χ-out Top (map code ⟨$⟩ x) nc) (sym (χInf-out x (λ t → nc (proj₂ (top-iff x) t)))))
