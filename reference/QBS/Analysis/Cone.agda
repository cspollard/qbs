{-# OPTIONS --safe --without-K #-}

-- Measures form a cone: a module over [0,∞] (valuations; Jones–Plotkin 1989, Keimel–Plotkin).
-- The generic constructions, each with the side condition that keeps total mass at most 1:
-- the zero measure, scaling `c μ` by a weight `c ≤ 1`, and the sum `μ₁ + μ₂` of two measures
-- whose masses add up to at most 1; and the equal mixture `mix` ½ μ₁ + ½ μ₂ (module `Mixture`).
-- (`Analysis/MixtureN` is the countable sum.)
module QBS.Analysis.Cone where

open import Level using (suc; zero)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Series using (module Series)

module Cone (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Series A
  open SetoidReasoning setoid
  open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup using () renaming (x∙yz≈y∙xz to swap)
  open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using () renaming (interchange to +-interchange)

  -- the zero measure
  zeroM : Measure
  zeroM = record
    { I = λ _ _ → 0#
    ; I-mono = λ _ _ _ → ≤-refl
    ; I-add = λ _ _ _ _ → sym (+-identityˡ 0#)
    ; I-scale = λ c _ _ _ → sym (zeroʳ c)
    ; I-sup = λ hs fs inc f e → sym (⨆-const 0# _)
    ; I-sub = λ _ → 0-least
    }

  -- scaling a measure by a weight ≤ 1
  scaleM : ∀ c → c ≤ 1# → Measure → Measure
  scaleM c c≤1 μ = record
    { I = λ h f → c * I μ h f
    ; I-mono = λ f f′ le → *-mono c (I-mono μ f f′ le)
    ; I-add = λ f f₁ f₂ e → trans (*-cong refl (I-add μ f f₁ f₂ e)) (distribˡ c _ _)
    ; I-scale = λ d f f′ e → trans (*-cong refl (I-scale μ d f f′ e)) (swap c d _)
    ; I-sup = λ hs fs inc f e →
        let incI = λ n → I-mono μ (fs n) (fs (ℕ.suc n)) (λ x → inc x n)
        in trans (*-cong refl (I-sup μ hs fs inc f e))
             (*-⨆ c (λ n → I μ (hs n) (fs n)) incI (λ n → *-mono c (incI n)))
    ; I-sub = λ f → ≤-trans (≤-trans (*-mono c (I-sub μ f)) (≤-reflexive (*-identityʳ c))) c≤1
    }

  -- the sum of two measures, when their masses add up to at most 1
  addM : ∀ (μ₁ μ₂ : Measure) → mass μ₁ + mass μ₂ ≤ 1# → Measure
  addM μ₁ μ₂ bd = record
    { I = λ h f → I μ₁ h f + I μ₂ h f
    ; I-mono = λ f f′ le → +-mono (I-mono μ₁ f f′ le) (I-mono μ₂ f f′ le)
    ; I-add = λ f f₁ f₂ e → trans (+-cong (I-add μ₁ f f₁ f₂ e) (I-add μ₂ f f₁ f₂ e)) (+-interchange _ _ _ _)
    ; I-scale = λ c f f′ e →
        trans (+-cong (I-scale μ₁ c f f′ e) (I-scale μ₂ c f f′ e)) (sym (distribˡ c _ _))
    ; I-sup = λ hs fs inc f e →
        let incI₁ = λ n → I-mono μ₁ (fs n) (fs (ℕ.suc n)) (λ x → inc x n)
            incI₂ = λ n → I-mono μ₂ (fs n) (fs (ℕ.suc n)) (λ x → inc x n)
        in trans (+-cong (I-sup μ₁ hs fs inc f e) (I-sup μ₂ hs fs inc f e))
             (⨆-+-diag incI₁ incI₂ _)
    ; I-sub = λ f → ≤-trans
        (+-mono (≤-reflexive (I-cong μ₁ (λ _ → refl) f (Fun-const 1# ≤-refl)))
                (≤-reflexive (I-cong μ₂ (λ _ → refl) f (Fun-const 1# ≤-refl))))
        bd
    }

-- The equal mixture ½ μ₁ + ½ μ₂ of two measures, `addM` of two `scaleM`s: it is again a measure
-- (with total mass at most 1).  Needs a half in the semiring.
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
