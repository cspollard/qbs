{-# OPTIONS --safe --without-K #-}

-- The integral of threshold-measurable functions R → [0,∞] (lower cuts) against a measure:
-- `J m φ` is the unbounded integral `Iinf` of `Analysis/Unbounded`, with `FunInf φ` obtained from
-- `Meas φ` (`Analysis/Meas`, `Analysis/MeasFun`; in fact the two are equivalent).  It is
-- independent of the measurability proof, monotone, additive, homogeneous for every constant in
-- [0,∞], and monotone-convergent.
module QBS.Analysis.Lebesgue where

open import Level using (suc; zero; lift; lower)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch; hpC)
open import QBS.Analysis.LowerRealsMin using (lowerRealsMin; _⊓_)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.Unbounded using (module Unbounded)

module Lebesgue (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  A = LowerRealsOmega lem
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; ⨆; Increasing)
  open Integration A using (Measure; I)
  open Measurable A using (Fun)
  open Meas lem
  open MeasFun lem using (Meas→Fun)
  open LevelSets lem using (LS)
  open Unbounded A (lowerRealsArch lem) (lowerRealsMin lem) public

  ----------------------------------------------------------------------------
  -- measurability: FunInf ⟺ Meas

  FunInf-Meas : ∀ {h} → Meas h → FunInf h
  FunInf-Meas {h} mh k = Meas→Fun {λ x → tr k (h x)} (λ x → tr-≤1 k (h x))
    (Meas-⊗ {λ _ → hpC k} {λ x → h x ⊓ pw k} (Meas-const (hpC k))
      (Meas-⊓ {h} {λ _ → pw k} mh (Meas-const (pw k))))


  Meas-FunInf : ∀ {h} → FunInf h → Meas h
  Meas-FunInf {h} f = Meas-⨆ {h} (φn h)
    (λ n → Meas-⊗ {λ _ → pw n} {λ x → tr n (h x)} (Meas-const (pw n)) (LS (f n))) (eqφ h)

  closed : Closed
  closed = record
    { cl-mul = λ c {h} f → FunInf-Meas {λ x → c * h x} (Meas-⊗ {λ _ → c} {h} (Meas-const c) (Meas-FunInf f))
    ; cl-add = λ {h₁} {h₂} f₁ f₂ → FunInf-Meas {λ x → h₁ x + h₂ x} (Meas-⊕ {h₁} {h₂} (Meas-FunInf f₁) (Meas-FunInf f₂))
    }

  open Linear closed public

  ----------------------------------------------------------------------------
  -- the integral

  abstract
    J : Measure → ∀ φ → Meas φ → Cut
    J m φ mφ = Iinf m φ (FunInf-Meas mφ)

    J-irrel : ∀ m {φ} (p q : Meas φ) → J m φ p ≈ J m φ q
    J-irrel m {φ} p q = Iinf-irrel m {φ} (FunInf-Meas p) (FunInf-Meas q)

    J-cong : ∀ m {φ ψ} (p : Meas φ) (q : Meas ψ) → (∀ x → φ x ≈ ψ x) → J m φ p ≈ J m ψ q
    J-cong m {φ} {ψ} p q e = Iinf-cong m {φ} {ψ} (FunInf-Meas p) (FunInf-Meas q) e

    J-mono : ∀ m {φ ψ} (p : Meas φ) (q : Meas ψ) → (∀ x → φ x ≤ ψ x) → J m φ p ≤ J m ψ q
    J-mono m {φ} {ψ} p q le = Iinf-mono m {φ} {ψ} (FunInf-Meas p) (FunInf-Meas q) le

    -- it extends the bounded integral
    J-fun : ∀ m {h} (F : Fun h) → J m h (LS F) ≈ I m h F
    J-fun m {h} F = Iinf-bounded m {h} F (FunInf-Meas {h} (LS F))

    J-add : ∀ m {φ ψ} (p : Meas φ) (q : Meas ψ) →
      J m (λ x → φ x + ψ x) (Meas-⊕ {φ} {ψ} p q) ≈ J m φ p + J m ψ q
    J-add m {φ} {ψ} p q = Iinf-add m {λ x → φ x + ψ x} {φ} {ψ}
      (FunInf-Meas (Meas-⊕ {φ} {ψ} p q)) (FunInf-Meas p) (FunInf-Meas q) (λ x → OmegaSemiring.refl A)


    J-scale : ∀ m c {φ} (p : Meas φ) →
      J m (λ x → c * φ x) (Meas-⊗ {λ _ → c} {φ} (Meas-const c) p) ≈ c * J m φ p
    J-scale m c {φ} p = OmegaSemiring.trans A
      (Iinf-irrel m {λ x → c * φ x} (FunInf-Meas {λ x → c * φ x} (Meas-⊗ {λ _ → c} {φ} (Meas-const c) p))
                                     (Closed.cl-mul closed c {φ} (FunInf-Meas {φ} p)))
      (Iinf-scale m c {φ} (FunInf-Meas {φ} p))

    -- monotone convergence
    J-⨆ : ∀ m {φ} (φs : ℕ → R₁ → Cut) (ps : ∀ n → Meas (φs n)) (inc : ∀ x → Increasing (λ n → φs n x))
      (p : Meas φ) → (∀ x → φ x ≈ ⨆ (λ n → φs n x) (inc x)) →
      J m φ p ≈ ⨆ (λ n → J m (φs n) (ps n)) (λ n → J-mono m (ps n) (ps (ℕ.suc n)) (λ x → inc x n))
    J-⨆ m {φ} φs ps inc p e = Iinf-sup m {φ} φs (λ n → FunInf-Meas {φs n} (ps n)) inc (FunInf-Meas {φ} p) e

    -- `J` is opaque: its uses never need to unfold the supremum of truncations
    J-def : ∀ m {φ} (p : Meas φ) → J m φ p ≈ Iinf m φ (FunInf-Meas p)
    J-def m p = OmegaSemiring.refl A
