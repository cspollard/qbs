{-# OPTIONS --safe --without-K #-}

-- The equal mixture ½ μ₁ + ½ μ₂ of two measures, `addM` of two `scaleM`s from `Analysis/Cone`: it is
-- again a measure (with total mass at most 1).  Needs a half in the semiring.
module QBS.Analysis.Mixture where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Cone using (module Cone)

module Mixture (A : OmegaSemiring (suc zero)) (half : OmegaSemiring.Carrier A)
               (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open SetoidReasoning setoid

  open Cone A

  -- ½ ≤ 1, since ½ + ½ = 1
  half≤1 : half ≤ 1#
  half≤1 = ≤-trans (≤-reflexive (sym (+-identityʳ half))) (≤-trans (+-mono ≤-refl 0-least) (≤-reflexive hh))

  -- ½ μ₁ + ½ μ₂ has mass at most 1 whenever the masses are
  mix-bound : ∀ m₁ m₂ → half * mass m₁ + half * mass m₂ ≤ 1#
  mix-bound m₁ m₂ = ≤-trans (+-mono (*-mono half (I-sub m₁ (Fun-const 1# ≤-refl))) (*-mono half (I-sub m₂ (Fun-const 1# ≤-refl))))
    (≤-reflexive (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh))

  mix : Measure → Measure → Measure
  mix m₁ m₂ = addM (scaleM half half≤1 m₁) (scaleM half half≤1 m₂) (mix-bound m₁ m₂)

  -- the value on a set whose two halves have measures m₁ (first bit true) and m₂ (false)
  mixcomb : ∀ {m m₁ m₂ n₁ n₂ : ∣A∣} → m ≈ half * (m₂ + m₁) → m₁ ≈ n₁ → m₂ ≈ n₂ →
    m ≈ half * n₁ + half * n₂
  mixcomb {m} {m₁} {m₂} {n₁} {n₂} e e₁ e₂ = begin
    m                           ≈⟨ e ⟩
    half * (m₂ + m₁)            ≈⟨ distribˡ half m₂ m₁ ⟩
    half * m₂ + half * m₁       ≈⟨ +-comm _ _ ⟩
    half * m₁ + half * m₂       ≈⟨ +-cong (*-cong refl e₁) (*-cong refl e₂) ⟩
    half * n₁ + half * n₂       ∎

  -- the mixture of two probability masses has mass one
  mix-one : ∀ {a b : ∣A∣} → a ≈ 1# → b ≈ 1# → half * a + half * b ≈ 1#
  mix-one {a} {b} ea eb = begin
    half * a + half * b   ≈⟨ +-cong (*-cong refl ea) (*-cong refl eb) ⟩
    half * 1# + half * 1# ≈⟨ +-cong (*-identityʳ half) (*-identityʳ half) ⟩
    half + half           ≈⟨ hh ⟩
    1#                    ∎
