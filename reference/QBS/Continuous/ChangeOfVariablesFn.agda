{-# OPTIONS --safe --without-K #-}

-- Change of variables from functions alone.
-- A re-packaging of `ChangeOfVariables.cov`; nothing else in `src/` imports it, so it also serves as a worked example.
-- `Continuous/ChangeOfVariables` takes φ, ψ and φ′ as morphisms.  Here they are plain functions Φ, Ψ, k on the cuts with
-- the same hypotheses (`dv : ∀ N → Deriv (N+1) Φ 0 k`, the Galois connection a ≤ Ψ y ↔ Φ a ≤ y, Φ (Ψ y) ≈ y, Ψ finite on
-- finite points), and the morphisms are built by the rules: φ = `LipTest.derivH`, φ′ = `LipTest.lipkH`, and
-- ψ = `MonoTest.monoH Ψ` (Ψ is increasing and respects ≈ by the Galois connection: `Ψ-mono`, `Ψ-cong`).  Then
--   `covF : ∫ g(Φ x) k(x) dx ≈ ∫ g`   and   `covF-inv : ∫ h(Ψ y) dy ≈ ∫ h k`   for every test g, h.
module QBS.Continuous.ChangeOfVariablesFn where

open import Data.Nat.Base using (suc)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.MonoTest using (module MonoTest)
open import QBS.Continuous.LipTest using (module LipTest)
open import QBS.Continuous.ChangeOfVariables using (module ChangeOfVariables)

module ChangeOfVariablesFn (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; 0#; ≤-refl; ≤-trans; ≤-antisym) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd)
  open AlgD A R using (Deriv)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open MonoTest lem₁ using (monoH)
  open LipTest lem₁ using (derivH; lipkH)
  open ChangeOfVariables lem₁ using (cov; cov-inv)
  open QBS
  open Hom

  module _ (Φ Ψ k : ∣A∣ → ∣A∣)
           (dv : ∀ N → Deriv (natE (suc N)) Φ (λ _ → 0#) k)
           (gc-to : ∀ a y → a ≤ Ψ y → Φ a ≤ y)
           (gc-from : ∀ a y → Φ a ≤ y → a ≤ Ψ y)
           (φψ : ∀ y → Φ (Ψ y) ≈ y)
           (ψ-fin : ∀ y → Bnd y → Bnd (Ψ y)) where

    -- Ψ is increasing and respects ≈
    Ψ-mono : ∀ {x y} → x ≤ y → Ψ x ≤ Ψ y
    Ψ-mono {x} {y} x≤y = gc-from (Ψ x) y (≤-trans (gc-to (Ψ x) x ≤-refl) x≤y)

    Ψ-cong : ∀ {x y} → x ≈ y → Ψ x ≈ Ψ y
    Ψ-cong e = ≤-antisym (Ψ-mono (proj₁ e)) (Ψ-mono (proj₂ e))

    φH ψH φ′H : Hom S WQ WQ
    φH = derivH Φ (λ _ → 0#) k dv
    ψH = monoH Ψ Ψ-cong Ψ-mono
    φ′H = lipkH Φ (λ _ → 0#) k dv

    covF-inv : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h ψH) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} φ′H h)
    covF-inv = cov-inv φH ψH φ′H dv gc-to gc-from φψ ψ-fin

    covF : ∀ (g : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} φ′H (_∘H_ S g φH)) ≈ ∫ᴹ {WQ} lebPre g
    covF = cov φH ψH φ′H dv gc-to gc-from φψ ψ-fin
