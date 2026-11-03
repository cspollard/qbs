{-# OPTIONS --safe --without-K #-}

-- Additivity of the integral in the test, over any space `X` (`Inference/Domination.∫ᴹ-add` is the case `X = WQ`).
--   * `addX f g : X ⇒ WQ`, the pointwise sum of two tests;
--   * `∫ᴹ-addX p f g : ∫ᴹ p (addX f g) ≈ ∫ᴹ p f + ∫ᴹ p g`.
-- Used by `UniquenessRQ.∫-split` (every test on the real line is the sum of its two halves).
module QBS.Continuous.UniquenessRQAlg where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)

module UniquenessRQAlg (lem : LEM₀) where
  open Lebesgue lem using (A; J-cong; J-add)
  open OmegaSemiring A using (_≈_; _+_; trans; +-cong; distribˡ)
  open Meas lem using (Meas-⊕)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; ψ; mψ; module C)
  open C using (Pre)
  open C.Pre
  open QBS
  open Hom

  addX : ∀ {X : QBS S} → Hom S X WQ → Hom S X WQ → Hom S X WQ
  addX f g = record
    { map = record { to = λ x → (map f ⟨$⟩ x) + (map g ⟨$⟩ x) ; cong = λ e → +-cong (Func.cong (map f) e) (Func.cong (map g) e) }
    ; map-random = λ {γ} mγ → Meas-⊕ {λ r → map f ⟨$⟩ (γ ⟨$⟩ r)} {λ r → map g ⟨$⟩ (γ ⟨$⟩ r)}
        (map-random f {γ} mγ) (map-random g {γ} mγ) }

  ∫ᴹ-addX : ∀ {X : QBS S} (p : Pre (XW X)) (f g : Hom S X WQ) → ∫ᴹ {X} p (addX f g) ≈ ∫ᴹ {X} p f + ∫ᴹ {X} p g
  ∫ᴹ-addX {X} p f g = trans (J-cong (m p) {ψ {X} p (addX f g)} {λ r → ψ {X} p f r + ψ {X} p g r}
    (mψ {X} p (addX f g)) (Meas-⊕ {ψ {X} p f} {ψ {X} p g} (mψ {X} p f) (mψ {X} p g))
    (λ r → distribˡ _ _ _)) (J-add (m p) {ψ {X} p f} {ψ {X} p g} (mψ {X} p f) (mψ {X} p g))
