{-# OPTIONS --safe --without-K #-}

-- Derived facts about sums in a complete semiring: additivity, Tonelli-style
-- swapping of iterated sums, pushforward of weights along a function, and
-- Dirac masses.
module QBS.Model.Sums where

open import Level using (Level; suc; _⊔_; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Inverse; _↔_; mk↔ₛ′)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Model.Semiring

module Sums {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A
  open SetoidReasoning setoid

  private
    variable
      I J : Set ℓ

  ∑-zero : (f : I → Carrier) → (∀ i → f i ≈ 0#) → ∑ f ≈ 0#
  ∑-zero {I} f z = begin
    ∑ f                          ≈⟨ ∑-cong z ⟩
    ∑ (λ _ → 0#)                 ≈⟨ ∑-cong (λ _ → sym (zeroˡ 1#)) ⟩
    ∑ (λ _ → 0# * 1#)            ≈⟨ sym (∑-distribˡ 0# (λ _ → 1#)) ⟩
    0# * ∑ (λ (_ : I) → 1#)      ≈⟨ zeroˡ _ ⟩
    0#                           ∎

  ∑-swap : ∀ (h : I → J → Carrier) → ∑ (λ i → ∑ (λ j → h i j)) ≈ ∑ (λ j → ∑ (λ i → h i j))
  ∑-swap {I} {J} h = begin
    ∑ (λ i → ∑ (λ j → h i j))                          ≈⟨ sym (∑-Σ {J = λ _ → J} (λ p → h (proj₁ p) (proj₂ p))) ⟩
    ∑ {Σ I (λ _ → J)} (λ p → h (proj₁ p) (proj₂ p))    ≈⟨ ∑-reindex {J = Σ J (λ _ → I)} swap (λ q → h (proj₂ q) (proj₁ q)) ⟩
    ∑ {Σ J (λ _ → I)} (λ q → h (proj₂ q) (proj₁ q))    ≈⟨ ∑-Σ {J = λ _ → I} (λ q → h (proj₂ q) (proj₁ q)) ⟩
    ∑ (λ j → ∑ (λ i → h i j))                          ∎
    where
      swap : Σ I (λ _ → J) ↔ Σ J (λ _ → I)
      swap = mk↔ₛ′ (λ p → proj₂ p , proj₁ p) (λ q → proj₂ q , proj₁ q) (λ _ → ≡.refl) (λ _ → ≡.refl)

  ∑-+ : ∀ (f g : I → Carrier) → ∑ (λ i → f i + g i) ≈ ∑ f + ∑ g
  ∑-+ {I} f g = begin
    ∑ (λ i → f i + g i)                  ≈⟨ ∑-cong (λ i → sym (two i)) ⟩
    ∑ (λ i → ∑ (hh i))                   ≈⟨ ∑-swap hh ⟩
    ∑ (λ b → ∑ (λ i → hh i b))           ≈⟨ ∑-⊎ (λ b → ∑ (λ i → hh i b)) ⟩
    ∑ (λ _ → ∑ f) + ∑ (λ _ → ∑ g)       ≈⟨ +-cong (∑-unit (λ _ → ∑ f)) (∑-unit (λ _ → ∑ g)) ⟩
    ∑ f + ∑ g                            ∎
    where
      hh : I → (⊤ {ℓ} ⊎ ⊤ {ℓ}) → Carrier
      hh i (inj₁ _) = f i
      hh i (inj₂ _) = g i
      two : ∀ i → ∑ (hh i) ≈ f i + g i
      two i = trans (∑-⊎ (hh i)) (+-cong (∑-unit (λ _ → f i)) (∑-unit (λ _ → g i)))

  ∑-distribʳ : ∀ (f : I → Carrier) x → ∑ f * x ≈ ∑ (λ i → f i * x)
  ∑-distribʳ f x = begin
    ∑ f * x             ≈⟨ *-comm _ _ ⟩
    x * ∑ f             ≈⟨ ∑-distribˡ x f ⟩
    ∑ (λ i → x * f i)   ≈⟨ ∑-cong (λ i → *-comm x (f i)) ⟩
    ∑ (λ i → f i * x)   ∎

  ∑-scale : ∀ x (f : I → Carrier) → ∑ (λ i → x * f i) ≈ x * ∑ f
  ∑-scale x f = sym (∑-distribˡ x f)

  ∑-prod : ∀ (f : I → Carrier) (g : J → Carrier) →
    ∑ (λ i → ∑ (λ j → f i * g j)) ≈ ∑ f * ∑ g
  ∑-prod f g = begin
    ∑ (λ i → ∑ (λ j → f i * g j))   ≈⟨ ∑-cong (λ i → sym (∑-distribˡ (f i) g)) ⟩
    ∑ (λ i → f i * ∑ g)             ≈⟨ sym (∑-distribʳ f (∑ g)) ⟩
    ∑ f * ∑ g                       ∎

  -- Pushforward of weights along a function: sum over the fibre.
  Fibre : (I → J) → J → Set ℓ
  Fibre {I} f j = Σ I (λ i → f i ≡ j)

  push : (I → J) → (I → Carrier) → J → Carrier
  push f μ j = ∑ (λ (m : Fibre f j) → μ (proj₁ m))

  private
    fibres : (f : I → J) → Σ J (Fibre f) ↔ I
    fibres f = mk↔ₛ′ (λ p → proj₁ (proj₂ p)) (λ i → f i , i , ≡.refl)
      (λ _ → ≡.refl) (λ { (_ , _ , ≡.refl) → ≡.refl })

  -- ∫ h d(f_* μ) = ∫ h∘f dμ
  push-∑ : ∀ (f : I → J) (μ : I → Carrier) (h : J → Carrier) →
    ∑ (λ j → push f μ j * h j) ≈ ∑ (λ i → μ i * h (f i))
  push-∑ f μ h = begin
    ∑ (λ j → push f μ j * h j)
      ≈⟨ ∑-cong (λ j → ∑-distribʳ (λ (m : Fibre f j) → μ (proj₁ m)) (h j)) ⟩
    ∑ (λ j → ∑ (λ (m : Fibre f j) → μ (proj₁ m) * h j))
      ≈⟨ sym (∑-Σ (λ (p : Σ _ (Fibre f)) → μ (proj₁ (proj₂ p)) * h (proj₁ p))) ⟩
    ∑ (λ (p : Σ _ (Fibre f)) → μ (proj₁ (proj₂ p)) * h (proj₁ p))
      ≈⟨ ∑-cong (λ { (_ , _ , ≡.refl) → refl }) ⟩
    ∑ (λ (p : Σ _ (Fibre f)) → μ (proj₁ (proj₂ p)) * h (f (proj₁ (proj₂ p))))
      ≈⟨ ∑-reindex (fibres f) (λ i → μ i * h (f i)) ⟩
    ∑ (λ i → μ i * h (f i))
      ∎

  -- The Dirac weights at j₀: the pushforward of the unit weight on a point.
  dirac : J → J → Carrier
  dirac j₀ = push (λ (_ : ⊤ {ℓ}) → j₀) (λ _ → 1#)

  dirac-∑ : ∀ (j₀ : J) (h : J → Carrier) → ∑ (λ j → dirac j₀ j * h j) ≈ h j₀
  dirac-∑ j₀ h = begin
    ∑ (λ j → dirac j₀ j * h j)   ≈⟨ push-∑ (λ _ → j₀) (λ _ → 1#) h ⟩
    ∑ (λ (_ : ⊤ {ℓ}) → 1# * h j₀) ≈⟨ ∑-unit (λ _ → 1# * h j₀) ⟩
    1# * h j₀                     ≈⟨ *-identityˡ _ ⟩
    h j₀                          ∎
