{-# OPTIONS --safe --without-K #-}

-- Fubini for unbounded integrands: the iterated integrals `J μ (r ↦ J ν (s ↦ Φ (merge r s)))` and
-- `J ν (s ↦ J μ (r ↦ Φ (merge r s)))` of a threshold-measurable `Φ` agree.  Both are `J` of the two
-- product measures `tensor₁`, `tensor₂` (Tonelli), which agree on the bounded functions (`Tensor`).
module QBS.Analysis.JFubini where

open import Level using (lower)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; measurable-merge₂; Cyl-rect; Cyl-rect-flip)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Param using (module Param)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tensor using (module Tensor)

module JFubini (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Tensor A lem using (tensor₁; tensor₂; kernel₁; constK; fubini)
  open import QBS.Analysis.Omega using (module OmegaSemiring)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open import QBS.Analysis.Measure using (module Integration)
  open Integration A using (Measure; KernelOk; bind; push)
  module P₂ = Param A lem (λ a s → mergeC s a) measurable-merge₂ Cyl-rect-flip

  -- parametric measurability of the integral of a section in the second slot
  Meas-Jsec₂ : ∀ (g : R₁ → Measure) → KernelOk g → ∀ {φ} (p : Meas φ) →
    Meas (λ s → J (g s) (λ r → φ (P₂.mergeR s r)) (Meas-pre {φ} {P₂.mergeR s} p (measurable-merge₂ (lower s))))
  Meas-Jsec₂ g kg {φ} p = Meas-ext {λ s → J (P₂.pushMerge g s) φ p}
    {λ s → J (g s) (λ r → φ (P₂.mergeR s r)) (Meas-pre {φ} {P₂.mergeR s} p (measurable-merge₂ (lower s)))}
    (λ s → J-push {P₂.mergeR s} (measurable-merge₂ (lower s)) (g s) {φ} p
             (Meas-pre {φ} {P₂.mergeR s} p (measurable-merge₂ (lower s))))
    (Meas-J (P₂.pushMerge g) (P₂.KernelOk-pushMerge {g} kg) p)

  J-tensor₁ : ∀ (μ ν : Measure) {Φ} (p : Meas Φ) →
    J (tensor₁ μ ν) Φ p ≈
      J μ (λ r → J ν (λ s → Φ (P₁.mergeR r s)) (Meas-pre {Φ} {P₁.mergeR r} p (measurable-merge₁ (lower r))))
        (Meas-Jsec (λ _ → ν) (constK ν) {Φ} p)
  J-tensor₁ μ ν {Φ} p = trans
    (J-bind μ (P₁.pushMerge (λ _ → ν)) (kernel₁ ν) {Φ} p
       (Meas-J (P₁.pushMerge (λ _ → ν)) (kernel₁ ν) {Φ} p))
    (J-cong μ (Meas-J (P₁.pushMerge (λ _ → ν)) (kernel₁ ν) {Φ} p) (Meas-Jsec (λ _ → ν) (constK ν) {Φ} p)
       (λ r → J-push {P₁.mergeR r} (measurable-merge₁ (lower r)) ν {Φ} p
                (Meas-pre {Φ} {P₁.mergeR r} p (measurable-merge₁ (lower r)))))

  J-tensor₂ : ∀ (μ ν : Measure) {Φ} (p : Meas Φ) →
    J (tensor₂ μ ν) Φ p ≈
      J ν (λ s → J μ (λ r → Φ (P₂.mergeR s r)) (Meas-pre {Φ} {P₂.mergeR s} p (measurable-merge₂ (lower s))))
        (Meas-Jsec₂ (λ _ → μ) (constK μ) {Φ} p)
  J-tensor₂ μ ν {Φ} p = trans
    (J-bind ν (P₂.pushMerge (λ _ → μ)) (P₂.KernelOk-pushMerge {λ _ → μ} (constK μ)) {Φ} p
       (Meas-J (P₂.pushMerge (λ _ → μ)) (P₂.KernelOk-pushMerge {λ _ → μ} (constK μ)) {Φ} p))
    (J-cong ν (Meas-J (P₂.pushMerge (λ _ → μ)) (P₂.KernelOk-pushMerge {λ _ → μ} (constK μ)) {Φ} p)
       (Meas-Jsec₂ (λ _ → μ) (constK μ) {Φ} p)
       (λ s → J-push {P₂.mergeR s} (measurable-merge₂ (lower s)) μ {Φ} p
                (Meas-pre {Φ} {P₂.mergeR s} p (measurable-merge₂ (lower s)))))

  J-fubini : ∀ (μ ν : Measure) {Φ} (p : Meas Φ) →
    J μ (λ r → J ν (λ s → Φ (P₁.mergeR r s)) (Meas-pre {Φ} {P₁.mergeR r} p (measurable-merge₁ (lower r))))
        (Meas-Jsec (λ _ → ν) (constK ν) {Φ} p)
    ≈ J ν (λ s → J μ (λ r → Φ (P₂.mergeR s r)) (Meas-pre {Φ} {P₂.mergeR s} p (measurable-merge₂ (lower s))))
        (Meas-Jsec₂ (λ _ → μ) (constK μ) {Φ} p)
  J-fubini μ ν {Φ} p = trans (sym (J-tensor₁ μ ν {Φ} p))
    (trans (J-agree (tensor₁ μ ν) (tensor₂ μ ν) {Φ} p (λ {h} F → fubini μ ν {h} F)) (J-tensor₂ μ ν {Φ} p))
