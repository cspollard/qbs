{-# OPTIONS --safe --without-K #-}

-- The product of two measures, integrated in either order, and Fubini's theorem: the two
-- iterated integrals agree.  Both orders are Daniell functionals built by `bind`/`push`, and they
-- agree on the finite cylinders (rectangles), so uniqueness of measures finishes the proof.
module QBS.Analysis.Tensor where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Borel.PiLambda using (Cyl)
open import QBS.Borel.Merge
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators
open import QBS.Analysis.Uniqueness
open import QBS.Analysis.Param

module Tensor (A : OmegaSemiring (suc zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Indicators A lem
  open Uniqueness A lem
  open SetoidReasoning setoid
  private R = R₁

  -- parametric measurability for the first and second coordinate
  module P₁ = Param A lem mergeC measurable-merge₁ Cyl-rect
  module P₂ = Param A lem (λ a s → mergeC s a) measurable-merge₂ Cyl-rect-flip

  -- constant kernels are kernels
  constK : ∀ (n : Measure) → KernelOk (λ (_ : R) → n)
  constK n fh = Fun-const (I n _ fh) (I-≤1 n fh)

  -- the product, integrating the first coordinate outside / the second coordinate outside
  tensor₁ tensor₂ : Measure → Measure → Measure
  tensor₁ m n = bind m (P₁.pushMerge (λ _ → n)) (P₁.KernelOk-pushMerge {λ _ → n} (constK n))
  tensor₂ m n = bind n (P₂.pushMerge (λ _ → m)) (P₂.KernelOk-pushMerge {λ _ → m} (constK m))

  -- products of probability measures are probability measures
  IsProb-tensor₁ : ∀ m n → IsProb m → IsProb n → IsProb (tensor₁ m n)
  IsProb-tensor₁ m n pm pn =
    IsProb-bind {m} {P₁.pushMerge (λ _ → n)} {P₁.KernelOk-pushMerge {λ _ → n} (constK n)} pm
      (λ r → IsProb-push {P₁.mergeR r} (measurable-merge₁ (lower r)) {n} pn)

  module _ (m n : Measure) where

    -- the two factors' masses of a rectangle C₁ × C₂
    mass₁ mass₂ : ∀ {C} → Cyl C → ∣A∣
    mass₁ c = I m (χ (P₁.rC₁ (λ _ → n) (constK n) c)) (Fun-χ (Cyl-borel (P₁.rc₁ (λ _ → n) (constK n) c)))
    mass₂ c = I n (χ (P₁.rC₂ (λ _ → n) (constK n) c)) (Fun-χ (Cyl-borel (P₁.rc₂ (λ _ → n) (constK n) c)))

    lhs-cyl : ∀ {C} (c : Cyl C) → I (tensor₁ m n) (χ C) (Fun-χ (Cyl-borel c)) ≈ mass₂ c * mass₁ c
    lhs-cyl {C} c =
      trans (I-cong m e kf kf′) (I-scale m p (Fun-χ bC₁) kf′ (λ r → refl))
      where
        g = λ (_ : R) → n
        kg = constK n
        bC = Cyl-borel c
        bC₁ = Cyl-borel (P₁.rc₁ g kg c)
        bC₂ = Cyl-borel (P₁.rc₂ g kg c)
        p = mass₂ c
        kf = P₁.KernelOk-pushMerge {g} kg (Fun-χ bC)
        kf′ = Fun-scale p (I-≤1 n (Fun-χ bC₂)) (Fun-χ bC₁)
        e : ∀ r → I (P₁.pushMerge g r) (χ C) (Fun-χ bC) ≈ p * χ (P₁.rC₁ g kg c) r
        step : ∀ r → I (P₁.pushMerge g r) (χ C) (Fun-χ bC) ≈ P₁.Φ g kg bC r
        step r = I-cong n {χ C ∘ P₁.mergeR r} {χ (P₁.Sec C (lower r))} (λ s → P₁.χ-sec C (lower r) s)
                   (Fun-pre {χ C} {P₁.mergeR r} (Fun-χ bC) (measurable-merge₁ (lower r)))
                   (Fun-χ (P₁.Bsec bC (lower r)))
        e r = trans (step r) (P₁.Φ-rect g kg c r)

    rhs-cyl : ∀ {C} (c : Cyl C) → I (tensor₂ m n) (χ C) (Fun-χ (Cyl-borel c)) ≈ mass₁ c * mass₂ c
    rhs-cyl {C} c =
      trans (I-cong n e kf kf′) (I-scale n q (Fun-χ bC₂) kf′ (λ s → refl))
      where
        g = λ (_ : R) → m
        kg = constK m
        g₁ = λ (_ : R) → n
        kg₁ = constK n
        bC = Cyl-borel c
        bC₁ = Cyl-borel (P₁.rc₁ g₁ kg₁ c)
        bC₂ = Cyl-borel (P₁.rc₂ g₁ kg₁ c)
        q = mass₁ c
        kf = P₂.KernelOk-pushMerge {g} kg (Fun-χ bC)
        kf′ = Fun-scale q (I-≤1 m (Fun-χ bC₁)) (Fun-χ bC₂)
        e : ∀ s → I (P₂.pushMerge g s) (χ C) (Fun-χ bC) ≈ q * χ (P₁.rC₂ g₁ kg₁ c) s
        step : ∀ s → I (P₂.pushMerge g s) (χ C) (Fun-χ bC) ≈ P₂.Φ g kg bC s
        step s = I-cong m {χ C ∘ P₂.mergeR s} {χ (P₂.Sec C (lower s))} (λ r → P₂.χ-sec C (lower s) r)
                   (Fun-pre {χ C} {P₂.mergeR s} (Fun-χ bC) (measurable-merge₂ (lower s)))
                   (Fun-χ (P₂.Bsec bC (lower s)))
        e s = trans (step s) (P₂.Φ-rect g kg c s)

    agree-cyl : ∀ {C} (c : Cyl C) →
      I (tensor₁ m n) (χ C) (Fun-χ (Cyl-borel c)) ≈ I (tensor₂ m n) (χ C) (Fun-χ (Cyl-borel c))
    agree-cyl c = trans (lhs-cyl c) (trans (*-comm _ _) (sym (rhs-cyl c)))

    -- the mass of a product is the product of the masses
    mass-tensor₁ : mass (tensor₁ m n) ≈ mass n * mass m
    mass-tensor₁ = trans (I-cong m (λ r → I-cong n (λ s → refl) _ (Fun-const 1# ≤-refl)) _
                            (Fun-const (mass n) (I-≤1 n (Fun-const 1# ≤-refl))))
                         (I-const-mass m (mass n) (I-≤1 n (Fun-const 1# ≤-refl)))

    mass-tensor₂ : mass (tensor₂ m n) ≈ mass m * mass n
    mass-tensor₂ = trans (I-cong n (λ s → I-cong m (λ r → refl) _ (Fun-const 1# ≤-refl)) _
                            (Fun-const (mass m) (I-≤1 m (Fun-const 1# ≤-refl))))
                         (I-const-mass n (mass m) (I-≤1 m (Fun-const 1# ≤-refl)))

    -- Fubini: the two iterated integrals of any measurable function agree
    fubini : ∀ {h} (f : Fun h) → I (tensor₁ m n) h f ≈ I (tensor₂ m n) h f
    fubini = agree-fun (tensor₁ m n) (tensor₂ m n)
      (trans mass-tensor₁ (trans (*-comm _ _) (sym mass-tensor₂))) agree-cyl
