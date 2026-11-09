{-# OPTIONS --safe --without-K #-}

-- All polynomial moments of the exponential (part 2): `∫₀^∞ xⁿ e^{−x} dλ(x) = n!`, multiplied out, for every n.
--   * `∫ᴹ-pw-moment : ∫ᴹ lebPre (pwNegExpH n) ≈ fact n`, with `fact 0 = 1`, `fact (n+1) = (n+1) · fact n`;
--   * `∫-x`, `∫-x²`: the cases n = 1, 2 (`∫ x e^{−x} = 1`, `∫ x² e^{−x} = 2`) for the tests `xNegExpH`, `x²NegExpH`.
--     (This is the single route to the exponential moments; the self-similarity modules `HalfLineMean` and
--     `HalfLineMoment2`, and `Analysis/GeometricMoment2`, were deleted as superseded.)
-- The step `∫ xʲ⁺¹ e^{−x} = (j+1) ∫ xʲ e^{−x}` is `DerivBridge.OnHalfLine.glue-D` (integration by parts on the half-line)
-- applied to `dvn j n = DerivExp.xjE`, the certificate `G′ = k − h` for `G = h = xʲ⁺¹ e^{−x}` built from the rules of
-- `Analysis/Deriv*` on `[0, n+1]`, with `G 0 = 0` and `G(N) → 0` along the multiples of j+2 (`Analysis/ExpTail`).
-- The base case is `TailFTCExpHalf.∫-negExp`.
module QBS.Continuous.HalfLineMomentFact where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)

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
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivExp using (module AlgDE)
open import QBS.Analysis.ExpTail using (module AlgTail)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.DerivBridge using (module DerivBridge)
open import QBS.Continuous.TailFTCExpHalf using (module TailFTCExpHalf)

module HalfLineMomentFact (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgP A R using (natE-+; pw; natE≤P)
  open AlgTail A R using (module Tail)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; Meas-negExp;negExp-anti; negExp-expC-nat; negExp-zero; negExp-cong)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineNegExp lem₁ using (negExp-add; negExpH)
  open HalfLineMomentN lem₁ using (pwNegExpH; kH; hx; facts; eadd)
  open AlgD A R using (Deriv)
  open AlgDE A R using (module Expo)
  open DerivBridge lem₁ using (module OnHalfLine)
  open TailFTCExpHalf lem₁ using (∫-negExp)
  open QBS
  open Hom

  -- the tests `x ↦ x e^{−x}` and `x ↦ x² e^{−x}` (for the mean and second moment of Exp(1))
  xNegExpH : Hom S WQ WQ
  xNegExpH = record
    { map = record { to = λ x → x * negExp x ; cong = λ e → *-cong e (negExp-cong e) }
    ; map-random = λ {γ} m → Meas-⊗ {γ ⟨$⟩_} {λ r → negExp (γ ⟨$⟩ r)} m (Meas-negExp {γ ⟨$⟩_} m) }

  x²NegExpH : Hom S WQ WQ
  x²NegExpH = record
    { map = record { to = λ x → (x * x) * negExp x ; cong = λ e → *-cong (*-cong e e) (negExp-cong e) }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → (γ ⟨$⟩ r) * (γ ⟨$⟩ r)} {λ r → negExp (γ ⟨$⟩ r)}
        (Meas-⊗ {γ ⟨$⟩_} {γ ⟨$⟩_} m m) (Meas-negExp {γ ⟨$⟩_} m) }

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

  -- the data on [0, n+1]: `xʲ⁺¹ e^{−x}` has derivative data `(j+1) xʲ e^{−x}`, from the rules of `Analysis/Deriv*`
  dvn : ∀ j n → Deriv (natE (suc n)) (hx (suc j)) (λ x → map (pwNegExpH (suc j)) ⟨$⟩ x) (λ x → map (kH j) ⟨$⟩ x)
  dvn j n = Expo.xjE negExp (natE (suc n)) (suc n) (natE≤P (suc n)) negExp≤1 negExp-anti negExp-cong (eadd (suc n))
    (λ t1 → proj₁ (facts t1)) (λ t1 → proj₂ (facts t1)) (suc n , natE≤P (suc n)) j

  moment-succ j = trans (OnHalfLine.glue-D (pwNegExpH (suc j)) (kH j) (hx (suc j)) (dvn j) (G0 j)
      (λ m N₀ → T.tail (suc j) m N₀))
    (k-scale j)

  ----------------------------------------------------------------------------
  -- the moments

  ∫ᴹ-pw-moment : ∀ n → ∫ᴹ {WQ} lebPre (pwNegExpH n) ≈ fact n
  ∫ᴹ-pw-moment zero = trans (∫ᴹ-cong lebPre {pwNegExpH 0} {negExpH} (λ x → *-identityˡ (negExp x))) ∫-negExp
  ∫ᴹ-pw-moment (suc j) = trans (moment-succ j) (*-cong refl (∫ᴹ-pw-moment j))

  -- n = 1: `∫ x e^{−x} = 1`
  fact-1 : fact 1 ≈ 1#
  fact-1 = trans (*-identityʳ _) (+-identityˡ 1#)

  ∫-x : ∫ᴹ {WQ} lebPre xNegExpH ≈ 1#
  ∫-x = trans (∫ᴹ-cong lebPre {xNegExpH} {pwNegExpH 1} (λ x → *-cong (sym (*-identityʳ x)) refl))
    (trans (∫ᴹ-pw-moment 1) fact-1)

  -- n = 2: `∫ x² e^{−x} = 2`
  ∫-x² : ∫ᴹ {WQ} lebPre x²NegExpH ≈ 1# + 1#
  ∫-x² = trans (∫ᴹ-cong lebPre {x²NegExpH} {pwNegExpH 2} (λ x → *-cong (*-cong refl (sym (*-identityʳ x))) refl))
    (trans (∫ᴹ-pw-moment 2) (trans (*-cong refl fact-1) (trans (*-identityʳ _) (+-cong (+-identityˡ 1#) refl))))
