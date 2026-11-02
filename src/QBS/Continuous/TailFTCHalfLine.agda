{-# OPTIONS --safe --without-K #-}

-- The fundamental theorem of calculus in tail form on the half-line (`Continuous/TailFTC`, applied on each [n, n+1]).
--
-- Take a measurable decreasing test h : [0,∞] ⇒ [0,∞] with values ≤ 1, and G with the dyadic certificate
--     G (n + b) + (b − a) h(n + b) ≤ G (n + a) ≤ G (n + b) + (b − a) h(n + a)    on every dyadic [a, b] ⊆ [0,1], every n.
-- The unit-interval theorem gives `∫₀¹ h(n + u) du + G (n+1) = G n`; `∫ᴹ-leb` writes the Lebesgue integral as the sum of
-- these, and the sum telescopes (`AlgT.tele`):
--   * `leb-≤ : ∫ h dλ ≤ G 0` (always), and
--   * `leb-≈ : ∫ h dλ ≈ G 0` when G(n) → 0 archimedeanly (for every m some N has G N ≤ ½ᵐ).
module QBS.Continuous.TailFTCHalfLine where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)

module TailFTCHalfLine (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R; module Unit)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-fun)
  open Series A using (∑ᶠ)
  open Exp A using (natE)
  open Expansion A half hh using (expansion)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open FairCoin lem₁ using (fairCoin)
  open Integration A using (I)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open QBS
  open Hom

  module Leb (h : Hom S WQ WQ) (G : ∣A∣ → ∣A∣) (K : ℕ)
    (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y)
    (h≤1 : ∀ x → map h ⟨$⟩ x ≤ 1#) (h-anti : ∀ {x y} → x ≤ y → map h ⟨$⟩ y ≤ map h ⟨$⟩ x)
    (G-bnd : ∀ n {k a} → Dy k a → G (natE n + a) ≤ P K)
    (cert-lo : ∀ n {k a} → Dy k a →
      G (natE n + (a + hp k)) + hp k * (map h ⟨$⟩ (natE n + (a + hp k))) ≤ G (natE n + a))
    (cert-hi : ∀ n {k a} → Dy k a →
      G (natE n + a) ≤ G (natE n + (a + hp k)) + hp k * (map h ⟨$⟩ (natE n + a))) where

    hn : ℕ → ∣A∣ → ∣A∣
    hn n u = map h ⟨$⟩ (natE n + u)

    hn-cong : ∀ n {x y} → x ≈ y → hn n x ≈ hn n y
    hn-cong n e = Func.cong (map h) (+-cong refl e)

    Fn : ∀ n → _
    Fn n = Meas→Fun {λ r → hn n (expansion r)} (λ r → h≤1 _) (Meas-hshift n h)

    module U (n : ℕ) = Unit (hn n) (λ u → G (natE n + u)) K (hn-cong n) (λ e → G-cong (+-cong refl e))
      (λ x _ → h≤1 _) (λ x≤y _ → h-anti (+-mono ≤-refl x≤y)) (Fn n) (G-bnd n) (cert-lo n) (cert-hi n)

    -- the n-th unit interval: `∫₀¹ h(n + u) du + G (n+1) = G n`
    term : ℕ → ∣A∣
    term n = J fairCoin (λ r → map h ⟨$⟩ shiftPt n r) (Meas-hshift n h)

    term≈ : ∀ n → term n ≈ I fairCoin (λ r → hn n (expansion r)) (Fn n)
    term≈ n = trans (J-irrel fairCoin (Meas-hshift n h) (LS (Fn n))) (J-fun fairCoin (Fn n))

    unit-step : ∀ n → term n + G (natE (suc n)) ≈ G (natE n)
    unit-step n = trans (+-cong (term≈ n) refl) (trans (U.ftc-unit n) (G-cong (+-identityʳ _)))

    -- ∫ h dλ ≤ G 0
    leb-≤ : ∫ᴹ {WQ} lebPre h ≤ G 0#
    leb-≤ = ≤-trans (≤-reflexive (∫ᴹ-leb h)) (tail-le term (λ n → G (natE n)) unit-step)

    -- ∫ h dλ = G 0 when G(n) → 0
    leb-≈ : (∀ m → Σ ℕ (λ N → G (natE N) ≤ hp m)) → ∫ᴹ {WQ} lebPre h ≈ G 0#
    leb-≈ tl = trans (∫ᴹ-leb h) (tail-eq term (λ n → G (natE n)) unit-step tl)
