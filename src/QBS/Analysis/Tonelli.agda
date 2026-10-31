{-# OPTIONS --safe --without-K #-}

-- Tonelli for kernels with unbounded integrands: integrating a threshold-measurable φ ≥ 0 against
-- `bind m g` is integrating `r ↦ ∫ φ dg(r)` against m, and that function is again measurable.
-- By monotone convergence it reduces to the bounded truncations, where it is the definition of bind.
module QBS.Analysis.Tonelli where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Classical using (LEM₀)

module Tonelli (lem : LEM₀) where
  open Lebesgue lem
  open Meas lem
  open LevelSets lem using (LS)
  open Integration A using (Measure; KernelOk; bind; I)
  open OmegaSemiring A using (_≈_; _≤_; _*_; ⨆; ⨆-cong; Increasing; refl; sym; trans)

  -- the integral against a measurable kernel is measurable
  Meas-J : ∀ (g : R₁ → Measure) → KernelOk g → ∀ {φ} (p : Meas φ) → Meas (λ r → J (g r) φ p)
  Meas-J g kg {φ} p = Meas-⨆ {λ r → J (g r) φ p} (λ n r → Iseq (g r) φ (FunInf-Meas p) n)
    (λ n → Meas-⊗ {λ _ → pw n} {λ r → I (g r) (λ x → tr n (φ x)) (FunInf-Meas p n)}
             (Meas-const (pw n)) (LS (kg (FunInf-Meas p n))))
    (λ r → J-def (g r) p)

  J-bind : ∀ m (g : R₁ → Measure) (kg : KernelOk g) {φ} (p : Meas φ) (mk : Meas (λ r → J (g r) φ p)) →
    J (bind m g kg) φ p ≈ J m (λ r → J (g r) φ p) mk
  J-bind m g kg {φ} p mk = trans step (sym (J-⨆ m {λ r → J (g r) φ p} u ps incU mk (λ r → J-def (g r) p)))
    where
      f∞ = FunInf-Meas p

      v : ℕ → R₁ → Cut
      v n r = I (g r) (λ x → tr n (φ x)) (f∞ n)

      u : ℕ → R₁ → Cut
      u n r = Iseq (g r) φ f∞ n

      ps : ∀ n → Meas (u n)
      ps n = Meas-⊗ {λ _ → pw n} {v n} (Meas-const (pw n)) (LS (kg (f∞ n)))

      incU : ∀ r → Increasing (λ n → u n r)
      incU r n = Iseq-inc (g r) φ f∞ n

      incJ : Increasing (λ n → J m (u n) (ps n))
      incJ n = J-mono m (ps n) (ps (ℕ.suc n)) (λ x → incU x n)

      termN : ∀ n → J m (u n) (ps n) ≈ pw n * I m (v n) (kg (f∞ n))
      termN n = trans (J-def m (ps n)) (Iinf-pw m n {v n} (kg (f∞ n)) (FunInf-Meas {u n} (ps n)))

      step : J (bind m g kg) φ p ≈ ⨆ (λ n → J m (u n) (ps n)) incJ
      step = trans (J-def (bind m g kg) p) (⨆-cong (Iseq-inc (bind m g kg) φ f∞) incJ (λ n → sym (termN n)))
