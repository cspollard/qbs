{-# OPTIONS --safe --without-K #-}

-- The dyadic premeasure on clopen sets (finite trees), with values in an `OmegaSemiring` that
-- has a half: μ0 (leaf true) = 1, μ0 (leaf false) = 0, μ0 (split a b) = ½ (μ0 a + μ0 b).
module QBS.Analysis.ClopenMeasure where

open import Level using (suc; zero)
open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core using (Cantor)
open import QBS.Analysis.Omega
open import QBS.Analysis.Clopen
open import QBS.Analysis.Archimedean

module Premeasure {A : OmegaSemiring (suc zero)} (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  module _ where

    μ0 : Cl → ∣A∣
    μ0 (leaf true) = 1#
    μ0 (leaf false) = 0#
    μ0 (split a b) = half * (μ0 a + μ0 b)

    swap4 : ∀ a b c d → (a + b) + (c + d) ≈ (a + c) + (b + d)
    swap4 = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl

    μ0-mod : ∀ a b → μ0 (a ∪ b) + μ0 (a ∩ b) ≈ μ0 a + μ0 b
    μ0-mod (leaf true) t = refl
    μ0-mod (leaf false) t = +-comm _ _
    μ0-mod (split a b) (leaf true) = +-comm _ _
    μ0-mod (split a b) (leaf false) = refl
    μ0-mod (split a b) (split c d) = begin
      half * (μ0 (a ∪ c) + μ0 (b ∪ d)) + half * (μ0 (a ∩ c) + μ0 (b ∩ d))
        ≈⟨ sym (distribˡ half _ _) ⟩
      half * ((μ0 (a ∪ c) + μ0 (b ∪ d)) + (μ0 (a ∩ c) + μ0 (b ∩ d)))
        ≈⟨ *-cong refl (swap4 _ _ _ _) ⟩
      half * ((μ0 (a ∪ c) + μ0 (a ∩ c)) + (μ0 (b ∪ d) + μ0 (b ∩ d)))
        ≈⟨ *-cong refl (+-cong (μ0-mod a c) (μ0-mod b d)) ⟩
      half * ((μ0 a + μ0 c) + (μ0 b + μ0 d))
        ≈⟨ *-cong refl (swap4 _ _ _ _) ⟩
      half * ((μ0 a + μ0 b) + (μ0 c + μ0 d))
        ≈⟨ distribˡ half _ _ ⟩
      half * (μ0 a + μ0 b) + half * (μ0 c + μ0 d) ∎

    μ0-∁ : ∀ a → μ0 (∁ᶜ a) + μ0 a ≈ 1#
    μ0-∁ (leaf true) = +-identityˡ _
    μ0-∁ (leaf false) = +-identityʳ _
    μ0-∁ (split a b) = begin
      half * (μ0 (∁ᶜ a) + μ0 (∁ᶜ b)) + half * (μ0 a + μ0 b)
        ≈⟨ sym (distribˡ half _ _) ⟩
      half * ((μ0 (∁ᶜ a) + μ0 (∁ᶜ b)) + (μ0 a + μ0 b))
        ≈⟨ *-cong refl (swap4 _ _ _ _) ⟩
      half * ((μ0 (∁ᶜ a) + μ0 a) + (μ0 (∁ᶜ b) + μ0 b))
        ≈⟨ *-cong refl (+-cong (μ0-∁ a) (μ0-∁ b)) ⟩
      half * (1# + 1#)
        ≈⟨ distribˡ half 1# 1# ⟩
      half * 1# + half * 1#
        ≈⟨ +-cong (*-identityʳ half) (*-identityʳ half) ⟩
      half + half
        ≈⟨ hh ⟩
      1# ∎

    μ0-≤1 : ∀ a → μ0 a ≤ 1#
    μ0-≤1 a = ≤-trans ≤-+ʳ (≤-reflexive (trans (+-comm _ _) (μ0-∁ a)))

    -- a function that is true everywhere has mass 1; one that is false everywhere has mass 0
    μ0-full : ∀ b → (∀ x → eval b x ≡ true) → 1# ≤ μ0 b
    μ0-full (leaf true) h = ≤-refl
    μ0-full (leaf false) h with h (λ _ → false)
    ... | ()
    μ0-full (split c d) h = ≤-trans (≤-reflexive (sym two))
      (*-mono half (+-mono (μ0-full c (λ y → h (cons false y))) (μ0-full d (λ y → h (cons true y)))))
      where
        two : half * (1# + 1#) ≈ 1#
        two = trans (distribˡ half 1# 1#) (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh)

    μ0-empty : ∀ a → (∀ x → eval a x ≡ false) → μ0 a ≤ 0#
    μ0-empty (leaf true) h with h (λ _ → false)
    ... | ()
    μ0-empty (leaf false) h = ≤-refl
    μ0-empty (split c d) h = ≤-trans
      (*-mono half (+-mono (μ0-empty c (λ y → h (cons false y))) (μ0-empty d (λ y → h (cons true y)))))
      (≤-reflexive (trans (*-cong refl (+-identityˡ 0#)) (zeroʳ half)))

    μ0-mono : ∀ a b → (∀ x → eval a x ≡ true → eval b x ≡ true) → μ0 a ≤ μ0 b
    μ0-mono (leaf false) b h = 0-least
    μ0-mono (leaf true) b h = μ0-full b (λ x → h x ≡.refl)
    μ0-mono (split a₀ a₁) (leaf true) h = μ0-≤1 (split a₀ a₁)
    μ0-mono (split a₀ a₁) (leaf false) h = μ0-empty (split a₀ a₁)
      (λ x → ¬true⇒false (eval (split a₀ a₁) x) (λ e → true≢false (≡.sym (h x e))))
    μ0-mono (split a₀ a₁) (split b₀ b₁) h =
      *-mono half (+-mono (μ0-mono a₀ b₀ (λ y → h (cons false y))) (μ0-mono a₁ b₁ (λ y → h (cons true y))))

    μ0-ext : ∀ a b → (∀ x → eval a x ≡ eval b x) → μ0 a ≈ μ0 b
    μ0-ext a b e = ≤-antisym
      (μ0-mono a b (λ x h → ≡.trans (≡.sym (e x)) h))
      (μ0-mono b a (λ x h → ≡.trans (e x) h))

    μ0-∪≤ : ∀ a b → μ0 (a ∪ b) ≤ μ0 a + μ0 b
    μ0-∪≤ a b = ≤-trans ≤-+ʳ (≤-reflexive (μ0-mod a b))
