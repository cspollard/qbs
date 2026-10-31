{-# OPTIONS --safe --without-K #-}

-- Hard conditioning in the discrete model: restrict a sub-probability measure to the points where
-- a Boolean observation holds (disintegration along a Boolean-valued function).  The unnormalised
-- result has the evidence as its mass; the rejected mass becomes the defect of the sub-probability
-- measure.  `Example/Conditioning.agda` does this for programs written with `guard`; here it is a
-- measure transformer with its laws.
module QBS.Example.HardConditioning where

open import Level using (Lift)
open import Data.Nat.Base using (ℕ)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡c
import Relation.Binary.PropositionalEquality.Properties as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.SubProb using (subClass)

module _ {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open SetoidReasoning Aˢ
  module MS = Measures A (subClass A)
  open MS using (Pre; mk; α; ∫)
  open Pre

  private
    Obs : QBS (discreteSource ℓ) → Set ℓ
    Obs X = Func (QBS.Carrier X) (≡.setoid Bool)

    ite : Bool → ∣A∣ → ∣A∣
    ite b x = if b then x else 0#

    ite-cong : ∀ {b b′ x y} → b ≡c.≡ b′ → x ≈ y → ite b x ≈ ite b′ y
    ite-cong {true} ≡c.refl e = e
    ite-cong {false} ≡c.refl e = refl

    -- the two branches of an observation partition a quantity
    ite-split : ∀ b x → ite b x + ite (not b) x ≈ x
    ite-split true x = +-identityʳ x
    ite-split false x = +-identityˡ x

    ite-mul : ∀ b m x → ite b m * x ≈ m * ite b x
    ite-mul true m x = refl
    ite-mul false m x = trans (zeroˡ x) (sym (zeroʳ m))

  negate : ∀ {X : QBS (discreteSource ℓ)} → Obs X → Obs X
  negate c = record { to = λ x → not (c ⟨$⟩ x) ; cong = λ e → ≡c.cong not (Func.cong c e) }

  -- the weights that survive the observation
  private
    kept : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Obs X → Lift ℓ ℕ → ∣A∣
    kept p c r = ite (c ⟨$⟩ α p r) (μ p r)

    mass-split : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (c : Obs X) →
      ∑ (kept p c) + ∑ (kept p (negate {X} c)) ≈ ∑ (μ p)
    mass-split {X} p c = begin
      ∑ (kept p c) + ∑ (kept p (negate {X} c))   ≈⟨ sym (∑-+ _ _) ⟩
      ∑ (λ r → kept p c r + kept p (negate {X} c) r) ≈⟨ ∑-cong (λ r → ite-split (c ⟨$⟩ α p r) (μ p r)) ⟩
      ∑ (μ p)                                ∎

  -- the conditioned (unnormalised) measure: keep the runs where the observation c is true
  condition : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Obs X → Pre X
  condition {X} p c = mk (αₛ p) (α-random p) (kept p c)
    ( proj₁ (μ-ok p) + ∑ (kept p (negate {X} c))
    , (begin
        ∑ (kept p c) + (proj₁ (μ-ok p) + ∑ (kept p (negate {X} c))) ≈⟨ +-cong refl (+-comm _ _) ⟩
        ∑ (kept p c) + (∑ (kept p (negate {X} c)) + proj₁ (μ-ok p)) ≈⟨ sym (+-assoc _ _ _) ⟩
        (∑ (kept p c) + ∑ (kept p (negate {X} c))) + proj₁ (μ-ok p) ≈⟨ +-cong (mass-split p c) refl ⟩
        ∑ (μ p) + proj₁ (μ-ok p)                                ≈⟨ proj₂ (μ-ok p) ⟩
        1#                                                       ∎))

  ∫-condition : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (c : Obs X) (f : Func (QBS.Carrier X) Aˢ) →
    ∫ (condition p c) f ≈ ∫ p (record { to = λ x → ite (c ⟨$⟩ x) (f ⟨$⟩ x)
                                      ; cong = λ e → ite-cong (Func.cong c e) (Func.cong f e) })
  ∫-condition {X} p c f = ∑-cong (λ r → ite-mul (c ⟨$⟩ α p r) (μ p r) (f ⟨$⟩ α p r))

  -- law of total expectation: observing c or not c splits any measure
  condition-split : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (c : Obs X) (f : Func (QBS.Carrier X) Aˢ) →
    ∫ p f ≈ ∫ (condition p c) f + ∫ (condition p (negate {X} c)) f
  condition-split {X} p c f = begin
    ∫ p f ≈⟨ ∑-cong pt ⟩
    ∑ (λ r → kept p c r * (f ⟨$⟩ α p r) + kept p (negate {X} c) r * (f ⟨$⟩ α p r)) ≈⟨ ∑-+ _ _ ⟩
    ∫ (condition p c) f + ∫ (condition p (negate {X} c)) f ∎
    where
      pt : ∀ r → μ p r * (f ⟨$⟩ α p r) ≈ kept p c r * (f ⟨$⟩ α p r) + kept p (negate {X} c) r * (f ⟨$⟩ α p r)
      pt r = let b = c ⟨$⟩ α p r ; fx = f ⟨$⟩ α p r in
        trans (*-cong refl (sym (ite-split b fx)))
          (trans (distribˡ _ _ _) (+-cong (sym (ite-mul b (μ p r) fx)) (sym (ite-mul (not b) (μ p r) fx))))
