{-# OPTIONS --safe --without-K #-}

-- Two probability measures that agree on the finite cylinders agree on every measurable
-- function (uniqueness of measures, via the π–λ theorem).
module QBS.Analysis.Uniqueness where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators

module Uniqueness (A : OmegaSemiring (suc zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Indicators A lem
  open SetoidReasoning setoid
  open Dynkin lem using (dynkin)

  fsum-cong : ∀ {a b} → (∀ n → a n ≈ b n) → ∀ N → fsum a N ≈ fsum b N
  fsum-cong e ℕ.zero = refl
  fsum-cong e (ℕ.suc N) = +-cong (fsum-cong e N) (e N)

  module _ (μ ν : Measure) (masses : mass μ ≈ mass ν)
           (agree : ∀ {C} (c : Cyl C) → I μ (χ C) (Fun-χ (Cyl-borel c)) ≈ I ν (χ C) (Fun-χ (Cyl-borel c))) where

    -- the sets on which the measures agree
    Agree : Pred → Set₁
    Agree U = Σ (Borel U) (λ bU → I μ (χ U) (Fun-χ bU) ≈ I ν (χ U) (Fun-χ bU))

    Agree-resp : ∀ {U V} → U ≐ V → Agree U → Agree V
    Agree-resp {U} {V} e (bU , p) = bV ,
      trans (I-cong μ (χ-cong (≐-sym e)) (Fun-χ bV) (Fun-χ bU))
        (trans p (I-cong ν (χ-cong e) (Fun-χ bU) (Fun-χ bV)))
      where bV = resp e bU

    Agree-compl : ∀ {U} → Agree U → Agree (∁ U)
    Agree-compl {U} (bU , p) = compl bU , cancel (I-≤1 μ (Fun-χ bU))
      (trans (+-comm a x) (trans (I-χ-compl μ bU)
        (trans masses (trans (sym (I-χ-compl ν bU)) (trans (+-comm y b) (+-cong (sym p) refl))))))
      where
        a = I μ (χ U) (Fun-χ bU)
        b = I ν (χ U) (Fun-χ bU)
        x = I μ (χ (∁ U)) (Fun-χ (compl bU))
        y = I ν (χ (∁ U)) (Fun-χ (compl bU))

    Agree-disj : ∀ {U : ℕ → Pred} → (∀ n → Agree (U n)) → Disjoint U →
      Agree (λ x → Σ ℕ (λ n → U n x))
    Agree-disj {U} ag dj = ⋃ bs ,
      trans (I-⋃ μ bs dj)
        (trans (⨆-cong _ _ (fsum-cong (λ n → proj₂ (ag n))))
               (sym (I-⋃ ν bs dj)))
      where bs = λ n → proj₁ (ag n)

    agree-borel : ∀ {U} (bU : Borel U) → I μ (χ U) (Fun-χ bU) ≈ I ν (χ U) (Fun-χ bU)
    agree-borel {U} bU with dynkin Agree Agree-resp (λ c → Cyl-borel c , agree c) Agree-compl Agree-disj bU
    ... | bU′ , p = trans (I-cong μ (λ x → refl) (Fun-χ bU) (Fun-χ bU′))
                      (trans p (I-cong ν (λ x → refl) (Fun-χ bU′) (Fun-χ bU)))

    -- from sets to functions
    agree-fun : ∀ {h} (f : Fun h) → I μ h f ≈ I ν h f
    agree-fun (ind {U} {h} c c≤1 bU e₀ e₁ b) =
      trans (I-scale μ c (Fun-χ bU) f′ pw)
        (trans (*-cong refl (agree-borel bU)) (sym (I-scale ν c (Fun-χ bU) f′ pw)))
      where
        f′ = ind c c≤1 bU e₀ e₁ b
        pw : ∀ x → h x ≈ c * χ U x
        pw x = case {U (lower x)}
          (λ u → trans (e₀ x u) (sym (trans (*-cong refl (χ-in U x u)) (*-identityʳ c))))
          (λ nu → trans (e₁ x nu) (sym (trans (*-cong refl (χ-out U x nu)) (zeroʳ c))))
    agree-fun (sumF {h} {h₁} {h₂} f₁ f₂ q b) =
      trans (I-add μ (sumF f₁ f₂ q b) f₁ f₂ q)
        (trans (+-cong (agree-fun f₁) (agree-fun f₂)) (sym (I-add ν (sumF f₁ f₂ q b) f₁ f₂ q)))
    agree-fun (supF {h} hs fs inc q) =
      trans (I-sup μ hs fs inc (supF hs fs inc q) q)
        (trans (⨆-cong _ _ (λ n → agree-fun (fs n))) (sym (I-sup ν hs fs inc (supF hs fs inc q) q)))
    agree-fun (complF {h} {h′} f q) =
      cancel (I-≤1 μ f)
        (trans (+-comm (I μ h′ f) (I μ h hf))
          (trans (total μ)
            (trans masses
              (sym (trans (+-cong (agree-fun f) refl) (trans (+-comm (I ν h′ f) (I ν h hf)) (total ν)))))))
      where
        hf = complF f q
        total : ∀ (m : Measure) → I m h hf + I m h′ f ≈ mass m
        total m = sym (I-add m (Fun-const 1# ≤-refl) hf f (λ y → sym (q y)))
