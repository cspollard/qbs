{-# OPTIONS --safe --without-K #-}

-- All polynomial moments of the exponential (part 2): `∫₀^∞ xⁿ e^{−x} dλ(x) = n!`, multiplied out, for every n.
--   * `∫ᴹ-pw-moment : ∫ᴹ lebPre (pwNegExpH n) ≈ fact n`, with `fact 0 = 1`, `fact (n+1) = (n+1) · fact n`;
--   * `∫-x`, `∫-x²`: the cases n = 1, 2, with the statements of `HalfLineMean` (`∫ x e^{−x} = 1`) and
--     `HalfLineMoment2` (`∫ x² e^{−x} = 2`), re-derived here without their self-similarity recursions.
-- The step `∫ xʲ⁺¹ e^{−x} = (j+1) ∫ xʲ e^{−x}` is `TailFTCLipHalf.glue` (integration by parts on the half-line) applied
-- to the unit-interval identities of `HalfLineMomentN`, with `G = xʲ⁺¹ e^{−x}`: `G 0 = 0`, and `G(N) → 0` along the
-- multiples of j+2 (`Analysis/ExpTail`).  The base case is `TailFTCExpHalf.∫-negExp`.
module QBS.Continuous.HalfLineMomentFact where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (1+≤expC)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.ExpTail using (module AlgTail)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMean using (module HalfLineMean)
open import QBS.Continuous.HalfLineMoment2 using (module HalfLineMoment2)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipHalf using (module TailFTCLipHalf)
open import QBS.Continuous.TailFTCExpHalf using (module TailFTCExpHalf)

module HalfLineMomentFact (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgP A R using (natE-+; pw)
  open AlgTail A R using (module Tail)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; negExp-expC-nat; negExp-zero)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineNegExp lem₁ using (negExp-add; negExpH)
  open HalfLineMomentN lem₁ using (negExp-cong; pwNegExpH; kH; hx; module AtInterval)
  open TailFTCLipHalf lem₁ using (module Glue)
  open TailFTCExpHalf lem₁ using (∫-negExp)
  open HalfLineMean lem₁ using (xNegExpH)
  open HalfLineMoment2 lem₁ using (x²NegExpH)
  open QBS
  open Hom

  fact : ℕ → ∣A∣
  fact zero = 1#
  fact (suc n) = natE (suc n) * fact n

  ----------------------------------------------------------------------------
  -- the tail of `xⁿ e^{−x}` along the integers

  E-addN : ∀ a b → negExp (natE a + natE b) ≈ negExp (natE a) * negExp (natE b)
  E-addN a b = negExp-add {natE a} {natE b} {a} {b} {a ℕ.+ b} ≤-refl ≤-refl (≤-reflexive (sym (natE-+ a b)))

  E-L : ∀ n → negExp (natE n) * natE n ≤ 1#
  E-L n = ≤-trans (*-mono (negExp (natE n)) (≤-trans ≤-+ʳ (≤-reflexive (+-comm (natE n) 1#))))
    (≤-trans (*-mono (negExp (natE n)) (1+≤expC (lemOf lem₁) (natE n)))
      (≤-reflexive (negExp-expC-nat (natE n) n ≤-refl)))

  module T = Tail negExp negExp≤1 negExp-zero negExp-cong E-addN E-L

  ----------------------------------------------------------------------------
  -- ∫ xʲ⁺¹ e^{−x} = (j+1) ∫ xʲ e^{−x}

  -- ∫ k = (j+1) ∫ xʲ e^{−x}
  k-scale : ∀ j → ∫ᴹ {WQ} lebPre (kH j) ≈ natE (suc j) * ∫ᴹ {WQ} lebPre (pwNegExpH j)
  k-scale j = trans (∫ᴹ-leb (kH j)) (trans (∑ᶠ-cong term) (trans (sym (∑ᶠ-scale (natE (suc j)) _))
    (*-cong refl (sym (∫ᴹ-leb (pwNegExpH j))))))
    where
    term : ∀ n → J fairCoin (λ r → map (kH j) ⟨$⟩ shiftPt n r) (Meas-hshift n (kH j))
      ≈ natE (suc j) * J fairCoin (λ r → map (pwNegExpH j) ⟨$⟩ shiftPt n r) (Meas-hshift n (pwNegExpH j))
    term n = trans (J-irrel fairCoin (Meas-hshift n (kH j))
        (Meas-⊗ {λ _ → natE (suc j)} {λ r → map (pwNegExpH j) ⟨$⟩ shiftPt n r} (Meas-const (natE (suc j))) (Meas-hshift n (pwNegExpH j))))
      (J-scale fairCoin (natE (suc j)) {λ r → map (pwNegExpH j) ⟨$⟩ shiftPt n r} (Meas-hshift n (pwNegExpH j)))

  moment-succ : ∀ j → ∫ᴹ {WQ} lebPre (pwNegExpH (suc j)) ≈ natE (suc j) * ∫ᴹ {WQ} lebPre (pwNegExpH j)
  G0 : ∀ j → hx (suc j) 0# ≈ 0#
  G0 j = trans (*-cong (zeroˡ (pw j 0#)) refl) (zeroˡ (negExp 0#))

  moment-succ j = trans (Glue.glue (pwNegExpH (suc j)) (kH j) (hx (suc j)) (λ n → AtInterval.ibp-unit n j) (G0 j)
      (λ m N₀ → T.tail (suc j) m N₀))
    (k-scale j)

  ----------------------------------------------------------------------------
  -- the moments

  ∫ᴹ-pw-moment : ∀ n → ∫ᴹ {WQ} lebPre (pwNegExpH n) ≈ fact n
  ∫ᴹ-pw-moment zero = trans (∫ᴹ-cong lebPre {pwNegExpH 0} {negExpH} (λ x → *-identityˡ (negExp x))) ∫-negExp
  ∫ᴹ-pw-moment (suc j) = trans (moment-succ j) (*-cong refl (∫ᴹ-pw-moment j))

  -- n = 1: `∫ x e^{−x} = 1` (the statement of `HalfLineMean.∫ᴹ-leb-xNegExp`)
  fact-1 : fact 1 ≈ 1#
  fact-1 = trans (*-identityʳ _) (+-identityˡ 1#)

  ∫-x : ∫ᴹ {WQ} lebPre xNegExpH ≈ 1#
  ∫-x = trans (∫ᴹ-cong lebPre {xNegExpH} {pwNegExpH 1} (λ x → *-cong (sym (*-identityʳ x)) refl))
    (trans (∫ᴹ-pw-moment 1) fact-1)

  -- n = 2: `∫ x² e^{−x} = 2` (the statement of `HalfLineMoment2.∫ᴹ-leb-x²NegExp`)
  ∫-x² : ∫ᴹ {WQ} lebPre x²NegExpH ≈ 1# + 1#
  ∫-x² = trans (∫ᴹ-cong lebPre {x²NegExpH} {pwNegExpH 2} (λ x → *-cong (*-cong refl (sym (*-identityʳ x))) refl))
    (trans (∫ᴹ-pw-moment 2) (trans (*-cong refl fact-1) (trans (*-identityʳ _) (+-cong (+-identityˡ 1#) refl))))
