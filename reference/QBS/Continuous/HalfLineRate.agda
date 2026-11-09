{-# OPTIONS --safe --without-K #-}

-- The tests for the exponential with a rate λ against the Lebesgue measure `lebPre` of `Continuous/HalfLine`.
--   * `negExpRH l : WQ ⇒ WQ`, the test `x ↦ e^{−λx}` (`negExp (l * x)`), and `pwRH l i`, the test `x ↦ xⁱ e^{−λx}`;
--   * `qH l i`, the rate-1 function `x ↦ (λx)ⁱ e^{−λx}` (the scaled form used by the integration by parts);
--   * `scaleH κ f`, the test `x ↦ κ f(x)`, with `∫-scaleH : ∫ lebPre (κ f) ≈ κ ∫ lebPre f`
--     (through the unit-interval sum `∫ᴹ-leb`, `J-scale` and `∑ᶠ-scale`).
-- The rate is an element `l` of the cuts (a positive rational or integer in the instances); no condition on it is needed
-- for these definitions.
module QBS.Continuous.HalfLineRate where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)

module HalfLineRate (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgP A R using (pw)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open NegExp (lemOf lem₁) using (negExp; Meas-negExp; negExp-cong)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineMomentN lem₁ using (pw-cong; Meas-pw)
  open QBS
  open Hom

  -- `x ↦ e^{−λx}`
  negExpRH : ∣A∣ → Hom S WQ WQ
  negExpRH l = record
    { map = record { to = λ x → negExp (l * x) ; cong = λ e → negExp-cong (*-cong refl e) }
    ; map-random = λ {γ} m → Meas-negExp {λ r → l * (γ ⟨$⟩ r)} (Meas-⊗ {λ _ → l} {γ ⟨$⟩_} (Meas-const l) m) }

  -- `x ↦ xⁱ e^{−λx}`
  pwRH : ∣A∣ → ℕ → Hom S WQ WQ
  pwRH l i = record
    { map = record { to = λ x → pw i x * negExp (l * x) ; cong = λ e → *-cong (pw-cong i e) (negExp-cong (*-cong refl e)) }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (γ ⟨$⟩ r)} {λ r → negExp (l * (γ ⟨$⟩ r))}
        (Meas-pw i {γ ⟨$⟩_} m) (Meas-negExp {λ r → l * (γ ⟨$⟩ r)} (Meas-⊗ {λ _ → l} {γ ⟨$⟩_} (Meas-const l) m)) }

  -- `x ↦ (λx)ⁱ e^{−λx}`
  qH : ∣A∣ → ℕ → Hom S WQ WQ
  qH l i = record
    { map = record { to = λ x → pw i (l * x) * negExp (l * x)
                   ; cong = λ e → *-cong (pw-cong i (*-cong refl e)) (negExp-cong (*-cong refl e)) }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (l * (γ ⟨$⟩ r))} {λ r → negExp (l * (γ ⟨$⟩ r))}
        (Meas-pw i {λ r → l * (γ ⟨$⟩ r)} (Meas-⊗ {λ _ → l} {γ ⟨$⟩_} (Meas-const l) m))
        (Meas-negExp {λ r → l * (γ ⟨$⟩ r)} (Meas-⊗ {λ _ → l} {γ ⟨$⟩_} (Meas-const l) m)) }

  -- `x ↦ κ f(x)`
  scaleH : ∣A∣ → Hom S WQ WQ → Hom S WQ WQ
  scaleH κ f = record
    { map = record { to = λ x → κ * (map f ⟨$⟩ x) ; cong = λ e → *-cong refl (Func.cong (map f) e) }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → κ} {λ r → map f ⟨$⟩ (γ ⟨$⟩ r)} (Meas-const κ) (map-random f {γ} m) }

  -- ∫ κ f = κ ∫ f
  ∫-scaleH : ∀ κ f → ∫ᴹ {WQ} lebPre (scaleH κ f) ≈ κ * ∫ᴹ {WQ} lebPre f
  ∫-scaleH κ f = trans (∫ᴹ-leb (scaleH κ f)) (trans (∑ᶠ-cong term) (trans (sym (∑ᶠ-scale κ _))
    (*-cong refl (sym (∫ᴹ-leb f)))))
    where
    term : ∀ n → J fairCoin (λ r → map (scaleH κ f) ⟨$⟩ shiftPt n r) (Meas-hshift n (scaleH κ f))
      ≈ κ * J fairCoin (λ r → map f ⟨$⟩ shiftPt n r) (Meas-hshift n f)
    term n = trans (J-irrel fairCoin (Meas-hshift n (scaleH κ f))
        (Meas-⊗ {λ _ → κ} {λ r → map f ⟨$⟩ shiftPt n r} (Meas-const κ) (Meas-hshift n f)))
      (J-scale fairCoin κ {λ r → map f ⟨$⟩ shiftPt n r} (Meas-hshift n f))
