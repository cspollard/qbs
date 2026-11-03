{-# OPTIONS --safe --without-K #-}

-- Pointwise suprema, infima, lim inf and lim sup of sequences of tests on any X, and monotone convergence for `∫ᴹ`
-- (plan 03, "Dominated convergence").
--   * `supH h` and `infH h` (x ↦ ⋃ₙ h n x and x ↦ ⋂ₙ h n x) are tests: random elements go to measurable functions by
--     `Meas.Meas-⨆` and `Meas-inter`; `supH-pt`, `infH-pt` hold by `≋-refl`;
--   * `liminfH h`, `limsupH h`, with `liminfH-pt`, `limsupH-pt` against `LowerRealsInf.liminfC`/`limsupC`;
--   * `∫ᴹ-monoX`: monotonicity of `∫ᴹ` on any X; `∫ᴹ-sup`: monotone convergence for increasing sequences.
-- Route: `Meas-inter`: Lvl (⋂ hs) q = ⋃_{q′ > q} ⋂ₙ Lvl (hs n) q′, a countable union over rationals (enumerate as in
-- `Meas.Meas-⊕`) of countable intersections (`Borel.⋂`).  `∫ᴹ-monoX` and `∫ᴹ-sup` unfold `∫ᴹ p f = J (m p) (ψ p f)`
-- and use `J-mono` and `J-⨆` (`Analysis/Lebesgue`); ψ p (supH h) r is the weight times the union, so `⊗-union`.
--   Skeleton: holes first.
module QBS.Continuous.SupTest where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LowerReals using (Cut; unionC)
open import QBS.Analysis.LowerRealsInf using (interC; liminfC; limsupC)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)

module SupTest (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_)
  open Meas lem using (Meas)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; module C)
  open QBS
  open Hom

  Meas-inter : ∀ (hs : ℕ → R₁ → Cut) → (∀ n → Meas (hs n)) → Meas (λ r → interC (λ n → hs n r))
  Meas-inter = ?

  module _ {X : QBS S} where

    -- x ↦ ⋃ₙ h n x and x ↦ ⋂ₙ h n x
    supH infH : (ℕ → Hom S X WQ) → Hom S X WQ
    supH = ?
    infH = ?

    supH-pt : ∀ h x → map (supH h) ⟨$⟩ x ≈ unionC (λ n → map (h n) ⟨$⟩ x)
    supH-pt = ?

    infH-pt : ∀ h x → map (infH h) ⟨$⟩ x ≈ interC (λ n → map (h n) ⟨$⟩ x)
    infH-pt = ?

    liminfH limsupH : (ℕ → Hom S X WQ) → Hom S X WQ
    liminfH h = supH (λ n → infH (λ k → h (n +ℕ k)))
    limsupH h = infH (λ n → supH (λ k → h (n +ℕ k)))

    liminfH-pt : ∀ h x → map (liminfH h) ⟨$⟩ x ≈ liminfC (λ n → map (h n) ⟨$⟩ x)
    liminfH-pt = ?

    limsupH-pt : ∀ h x → map (limsupH h) ⟨$⟩ x ≈ limsupC (λ n → map (h n) ⟨$⟩ x)
    limsupH-pt = ?

    -- monotonicity and monotone convergence
    ∫ᴹ-monoX : ∀ (p : C.Pre (XW X)) {f g : Hom S X WQ} → (∀ x → map f ⟨$⟩ x ≤ map g ⟨$⟩ x) → ∫ᴹ {X} p f ≤ ∫ᴹ {X} p g
    ∫ᴹ-monoX = ?

    ∫ᴹ-sup : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → (∀ n x → map (h n) ⟨$⟩ x ≤ map (h (suc n)) ⟨$⟩ x) →
      ∫ᴹ {X} p (supH h) ≈ unionC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-sup = ?
