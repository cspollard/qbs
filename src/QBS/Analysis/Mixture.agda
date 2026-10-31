{-# OPTIONS --safe --without-K #-}

-- The equal mixture ½ μ₁ + ½ μ₂ of two measures, as a functional: it is again a measure (with
-- total mass at most 1).  Needs a half in the semiring.
module QBS.Analysis.Mixture where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Series using (module Series)

module Mixture (A : OmegaSemiring (suc zero)) (half : OmegaSemiring.Carrier A)
               (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Series A
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  mix-mono : ∀ (m₁ m₂ : Measure) {h h′} (f : Fun h) (f′ : Fun h′) → (∀ x → h x ≤ h′ x) →
    half * I m₁ h f + half * I m₂ h f ≤ half * I m₁ h′ f′ + half * I m₂ h′ f′
  mix-mono m₁ m₂ f f′ le = +-mono (*-mono half (I-mono m₁ f f′ le)) (*-mono half (I-mono m₂ f f′ le))

  mix-sup : ∀ (m₁ m₂ : Measure) {h} (hs : ℕ → _ → ∣A∣) (fs : ∀ n → Fun (hs n))
    (inc : ∀ x → Increasing (λ n → hs n x)) (f : Fun h) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
    half * I m₁ h f + half * I m₂ h f ≈
      ⨆ (λ n → half * I m₁ (hs n) (fs n) + half * I m₂ (hs n) (fs n))
        (λ n → mix-mono m₁ m₂ (fs n) (fs (ℕ.suc n)) (λ x → inc x n))
  mix-sup m₁ m₂ {h} hs fs inc f e = begin
    half * I m₁ h f + half * I m₂ h f
      ≈⟨ +-cong (*-cong refl (I-sup m₁ hs fs inc f e)) (*-cong refl (I-sup m₂ hs fs inc f e)) ⟩
    half * ⨆ a ia + half * ⨆ b ib
      ≈⟨ +-cong (*-⨆ half a ia (λ n → *-mono half (ia n))) (*-⨆ half b ib (λ n → *-mono half (ib n))) ⟩
    ⨆ (λ n → half * a n) (λ n → *-mono half (ia n)) + ⨆ (λ n → half * b n) (λ n → *-mono half (ib n))
      ≈⟨ ⨆-+-diag (λ n → *-mono half (ia n)) (λ n → *-mono half (ib n)) _ ⟩
    ⨆ (λ n → half * a n + half * b n) _ ∎
    where
      a = λ n → I m₁ (hs n) (fs n)
      b = λ n → I m₂ (hs n) (fs n)
      ia = λ n → I-mono m₁ (fs n) (fs (ℕ.suc n)) (λ x → inc x n)
      ib = λ n → I-mono m₂ (fs n) (fs (ℕ.suc n)) (λ x → inc x n)

  mix-add : ∀ (m₁ m₂ : Measure) {h h₁ h₂} (f : Fun h) (f₁ : Fun h₁) (f₂ : Fun h₂) → (∀ x → h x ≈ h₁ x + h₂ x) →
    half * I m₁ h f + half * I m₂ h f
      ≈ (half * I m₁ h₁ f₁ + half * I m₂ h₁ f₁) + (half * I m₁ h₂ f₂ + half * I m₂ h₂ f₂)
  mix-add m₁ m₂ f f₁ f₂ e = trans
    (+-cong (*-cong refl (I-add m₁ f f₁ f₂ e)) (*-cong refl (I-add m₂ f f₁ f₂ e)))
    (solve 5 (λ h a₁ a₂ b₁ b₂ → h :* (a₁ :+ a₂) :+ h :* (b₁ :+ b₂) := (h :* a₁ :+ h :* b₁) :+ (h :* a₂ :+ h :* b₂))
             refl half _ _ _ _)

  mix-scale : ∀ (m₁ m₂ : Measure) {h h′} c (f : Fun h) (f′ : Fun h′) → (∀ x → h′ x ≈ c * h x) →
    half * I m₁ h′ f′ + half * I m₂ h′ f′ ≈ c * (half * I m₁ h f + half * I m₂ h f)
  mix-scale m₁ m₂ c f f′ e = trans
    (+-cong (*-cong refl (I-scale m₁ c f f′ e)) (*-cong refl (I-scale m₂ c f f′ e)))
    (solve 4 (λ h c a b → h :* (c :* a) :+ h :* (c :* b) := c :* (h :* a :+ h :* b)) refl half c _ _)

  mix : Measure → Measure → Measure
  mix m₁ m₂ = record
    { I = λ h f → half * I m₁ h f + half * I m₂ h f
    ; I-mono = mix-mono m₁ m₂
    ; I-add = mix-add m₁ m₂
    ; I-scale = mix-scale m₁ m₂
    ; I-sup = λ {h} hs fs inc f e → mix-sup m₁ m₂ {h} hs fs inc f e
    ; I-sub = λ f → ≤-trans (+-mono (*-mono half (I-sub m₁ f)) (*-mono half (I-sub m₂ f)))
        (≤-reflexive (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh))
    }

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
