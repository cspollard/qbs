{-# OPTIONS --safe --without-K #-}

-- The unbounded integral `J` against push-forwards and against measures that agree on `Fun`, and
-- parametric measurability of `r ↦ J (g r) (s ↦ φ (merge r s))` for a kernel `g`.
module QBS.Analysis.JParam where

open import Level using (suc; zero; lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Core using (Measurable)
open import QBS.Borel.Source using (R₁) renaming (down to downR)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Param using (module Param)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Tonelli using (module Tonelli)

module JParam (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open Lebesgue lem public
  open Meas lem
  open Tonelli lem using (Meas-J)
  open OmegaSemiring A using (_≈_; refl; sym; trans; *-cong; ⨆-cong)
  open Integration A using (Measure; KernelOk; I; I-cong; push)
  open Measurable A using (Fun)
  module P₁ = Param A lem mergeC measurable-merge₁ Cyl-rect

  -- J only depends on the integral of bounded functions
  J-agree : ∀ (m n : Measure) {φ} (p : Meas φ) →
    (∀ {h} (F : Fun h) → I m h F ≈ I n h F) → J m φ p ≈ J n φ p
  J-agree m n {φ} p e = trans (J-def m p) (trans (⨆-cong (Iseq-inc m φ (FunInf-Meas p)) (Iseq-inc n φ (FunInf-Meas p))
    (λ k → *-cong refl (e (FunInf-Meas p k)))) (sym (J-def n p)))

  -- J is determined by the integrals of the truncations
  J-trunc : ∀ (m n : Measure) {φ ψ} (pφ : Meas φ) (pψ : Meas ψ) →
    (∀ k → I m (λ x → tr k (φ x)) (FunInf-Meas pφ k) ≈ I n (λ x → tr k (ψ x)) (FunInf-Meas pψ k)) →
    J m φ pφ ≈ J n ψ pψ
  J-trunc m n {φ} {ψ} pφ pψ e = trans (J-def m pφ) (trans (⨆-cong (Iseq-inc m φ (FunInf-Meas pφ)) (Iseq-inc n ψ (FunInf-Meas pψ))
    (λ k → *-cong refl (e k))) (sym (J-def n pψ)))

  -- the same, with any measurability witnesses for the truncations
  J-trunc′ : ∀ (m n : Measure) {φ ψ} (pφ : Meas φ) (pψ : Meas ψ) (Fφ : FunInf φ) (Fψ : FunInf ψ) →
    (∀ k → I m (λ x → tr k (φ x)) (Fφ k) ≈ I n (λ x → tr k (ψ x)) (Fψ k)) → J m φ pφ ≈ J n ψ pψ
  J-trunc′ m n {φ} {ψ} pφ pψ Fφ Fψ e = trans (J-irrel-FunInf m {φ} pφ Fφ)
    (trans (⨆-cong (Iseq-inc m φ Fφ) (Iseq-inc n ψ Fψ) (λ k → *-cong refl (e k)))
      (sym (J-irrel-FunInf n {ψ} pψ Fψ)))
    where
      J-irrel-FunInf : ∀ m {φ} (pφ : Meas φ) (F : FunInf φ) → J m φ pφ ≈ Iinf m φ F
      J-irrel-FunInf m {φ} pφ F = trans (J-def m pφ) (Iinf-irrel m {φ} (FunInf-Meas pφ) F)

  -- push-forward
  J-push : ∀ {f} (mf : Measurable (downR f)) (m : Measure) {φ} (p : Meas φ) (q : Meas (λ x → φ (f x))) →
    J (push {f} mf m) φ p ≈ J m (λ x → φ (f x)) q
  J-push {f} mf m {φ} p q = trans (J-def (push {f} mf m) p) (trans (⨆-cong (Iseq-inc (push {f} mf m) φ (FunInf-Meas p))
    (Iseq-inc m (λ x → φ (f x)) (FunInf-Meas q))
    (λ k → *-cong refl (I-cong m (λ x → refl) _ _))) (sym (J-def m q)))

  -- parametric measurability of the integral of a section
  Meas-Jsec : ∀ (g : R₁ → Measure) → KernelOk g → ∀ {φ} (p : Meas φ) →
    Meas (λ r → J (g r) (λ s → φ (P₁.mergeR r s)) (Meas-pre {φ} {P₁.mergeR r} p (measurable-merge₁ (lower r))))
  Meas-Jsec g kg {φ} p = Meas-ext {λ r → J (P₁.pushMerge g r) φ p}
    {λ r → J (g r) (λ s → φ (P₁.mergeR r s)) (Meas-pre {φ} {P₁.mergeR r} p (measurable-merge₁ (lower r)))}
    (λ r → J-push {P₁.mergeR r} (measurable-merge₁ (lower r)) (g r) {φ} p
             (Meas-pre {φ} {P₁.mergeR r} p (measurable-merge₁ (lower r))))
    (Meas-J (P₁.pushMerge g) (P₁.KernelOk-pushMerge {g} kg) p)

  -- the integral against a Dirac measure is evaluation
  J-dirac : ∀ r₀ {φ} (p : Meas φ) → J (Integration.dirac A r₀) φ p ≈ φ r₀
  J-dirac r₀ {φ} p = trans (J-def (Integration.dirac A r₀) p) (sym (trans (eqφ φ r₀)
    (⨆-cong (incφ φ r₀) (Iseq-inc (Integration.dirac A r₀) φ (FunInf-Meas p)) (λ n → refl))))
