{-# OPTIONS --safe --without-K #-}

-- Countable mixtures `∑ₙ cₙ μₙ` of measures with coefficients of sum at most 1, as functionals:
-- `I h = ∑ᶠ (n ↦ cₙ · I μₙ h)`.  Monotone convergence is `∑ᶠ-⨆`.  (`Analysis/Mixture` is the
-- binary case with half coefficients.)
module QBS.Analysis.MixtureN where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.SeriesSup using (module SeriesSup)

module MixtureN (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Series A
  open SeriesSup A
  open SetoidReasoning setoid

  private
    swap : ∀ x y z → x * (y * z) ≈ y * (x * z)
    swap x y z = trans (sym (*-assoc x y z)) (trans (*-cong (*-comm x y) refl) (*-assoc y x z))

  -- the mixture functional `h ↦ ∑ₙ cₙ · I μₙ h`
  mixI : (ℕ → ∣A∣) → (ℕ → Measure) → ∀ {h} → Fun h → ∣A∣
  mixI c μ {h} f = ∑ᶠ (λ n → c n * I (μ n) h f)

  mixN-mono : ∀ c μ {h h′} (f : Fun h) (f′ : Fun h′) → (∀ x → h x ≤ h′ x) → mixI c μ f ≤ mixI c μ f′
  mixN-mono c μ f f′ le = ∑ᶠ-mono (λ n → *-mono (c n) (I-mono (μ n) f f′ le))

  mixN-add : ∀ c μ {h h₁ h₂} (f : Fun h) (f₁ : Fun h₁) (f₂ : Fun h₂) → (∀ x → h x ≈ h₁ x + h₂ x) →
    mixI c μ f ≈ mixI c μ f₁ + mixI c μ f₂
  mixN-add c μ f f₁ f₂ e = begin
    ∑ᶠ (λ n → c n * I (μ n) _ f)
      ≈⟨ ∑ᶠ-cong (λ n → trans (*-cong refl (I-add (μ n) f f₁ f₂ e)) (distribˡ _ _ _)) ⟩
    ∑ᶠ (λ n → c n * I (μ n) _ f₁ + c n * I (μ n) _ f₂)
      ≈⟨ ∑ᶠ-+ _ _ ⟩
    mixI c μ f₁ + mixI c μ f₂ ∎

  mixN-scale : ∀ c μ {h h′} d (f : Fun h) (f′ : Fun h′) → (∀ x → h′ x ≈ d * h x) →
    mixI c μ f′ ≈ d * mixI c μ f
  mixN-scale c μ d f f′ e = begin
    ∑ᶠ (λ n → c n * I (μ n) _ f′)
      ≈⟨ ∑ᶠ-cong (λ n → trans (*-cong refl (I-scale (μ n) d f f′ e)) (swap (c n) d _)) ⟩
    ∑ᶠ (λ n → d * (c n * I (μ n) _ f))
      ≈⟨ sym (∑ᶠ-scale d _) ⟩
    d * mixI c μ f ∎

  mixN-sup : ∀ c μ {h} (hs : ℕ → _ → ∣A∣) (fs : ∀ n → Fun (hs n))
    (inc : ∀ x → Increasing (λ n → hs n x)) (f : Fun h) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
    mixI c μ f ≈ ⨆ (λ k → mixI c μ (fs k)) (λ k → mixN-mono c μ (fs k) (fs (ℕ.suc k)) (λ x → inc x k))
  mixN-sup c μ {h} hs fs inc f e = begin
    ∑ᶠ (λ n → c n * I (μ n) h f)
      ≈⟨ ∑ᶠ-cong (λ n → trans (*-cong refl (I-sup (μ n) hs fs inc f e))
           (*-⨆ (c n) (a n) (ia n) (λ k → *-mono (c n) (ia n k)))) ⟩
    ∑ᶠ (λ n → ⨆ (λ k → c n * a n k) (λ k → *-mono (c n) (ia n k)))
      ≈⟨ ∑ᶠ-⨆ (λ n k → c n * a n k) (λ n k → *-mono (c n) (ia n k)) ⟩
    ⨆ (λ k → ∑ᶠ (λ n → c n * a n k)) _ ∎
    where
      a = λ n k → I (μ n) (hs k) (fs k)
      ia = λ n k → I-mono (μ n) (fs k) (fs (ℕ.suc k)) (λ x → inc x k)

  mixN : ∀ (c : ℕ → ∣A∣) → ∑ᶠ c ≤ 1# → (ℕ → Measure) → Measure
  mixN c sub μ = record
    { I = λ h f → mixI c μ f
    ; I-mono = mixN-mono c μ
    ; I-add = mixN-add c μ
    ; I-scale = mixN-scale c μ
    ; I-sup = mixN-sup c μ
    ; I-sub = λ f → ≤-trans (∑ᶠ-mono (λ n → ≤-trans (*-mono (c n) (I-sub (μ n) f)) (≤-reflexive (*-identityʳ (c n))))) sub
    }

  -- probability measures mix to a probability measure when the coefficients sum to 1
  mixN-prob : ∀ c (sub : ∑ᶠ c ≤ 1#) (μ : ℕ → Measure) → ∑ᶠ c ≈ 1# → (∀ n → IsProb (μ n)) → IsProb (mixN c sub μ)
  mixN-prob c sub μ s p = trans (∑ᶠ-cong (λ n → *-cong refl (p n)))
    (trans (∑ᶠ-cong (λ n → *-identityʳ (c n))) s)
