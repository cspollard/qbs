{-# OPTIONS --safe --without-K #-}

-- Measures on the Borel σ-algebra of Cantor space, valued in a complete semiring
-- (Billingsley §2; Affeldt–Cohen–Saito, *Measure Construction by Extension in Dependent
-- Type Theory with Application to Integration*, for the architecture): a σ-additive map on
-- Borel sets.  Since `Borel` is proof-relevant (a set can be derived in many ways), a measure is
-- also required to be independent of the derivation.
module QBS.Borel.Measure where

import Level as L
open import Level using (Level; suc; _⊔_; Lift; lift; lower)
open import Data.Unit.Base using (tt)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Borel.Core

-- the members of a family of sets are pairwise disjoint
Disjoint : (ℕ → Pred) → Set
Disjoint U = ∀ x m n → U m x → U n x → m ≡ n

module BorelMeasure {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣)
  open Sums A

  record Measure : Set (suc L.zero ⊔ ℓ) where
    field
      μ : ∀ {U} → Borel U → ∣A∣
      μ-cong : ∀ {U V} (e : U ≐ V) (bu : Borel U) (bv : Borel V) → μ bu ≈ μ bv
      μ-empty : μ ⊥-borel ≈ 0#
      μ-additive : ∀ {U : ℕ → Pred} (bs : ∀ n → Borel (U n)) → Disjoint U →
        μ (⋃ bs) ≈ ∑ (λ (n : Lift ℓ ℕ) → μ (bs (lower n)))

  open Measure public

  IsProbability : Measure → Set ℓ
  IsProbability m = μ m ⊤-borel ≈ 1#

  -- push-forward along a measurable map
  pushforward : ∀ {f} → Measurable f → Measure → Measure
  pushforward {f} mf m = record
    { μ = λ bu → μ m (preimage mf bu)
    ; μ-cong = λ e bu bv → μ-cong m (λ x → e (f x)) (preimage mf bu) (preimage mf bv)
    ; μ-empty = trans (μ-cong m (λ x → (λ b → b) , (λ b → b)) (preimage mf ⊥-borel) ⊥-borel) (μ-empty m)
    ; μ-additive = λ bs dj → μ-additive m (λ n → preimage mf (bs n)) (λ x p q → dj (f x) p q)
    }

  pushforward-prob : ∀ {f} (mf : Measurable f) (m : Measure) → IsProbability m →
    IsProbability (pushforward mf m)
  pushforward-prob mf m p = trans (μ-cong m (λ x → (λ _ → tt) , (λ _ → tt)) (preimage mf ⊤-borel) ⊤-borel) p

  -- push-forward is functorial (up to the derivation independence of measures)
  pushforward-id : ∀ (m : Measure) {U} (bu : Borel U) → μ (pushforward measurable-id m) bu ≈ μ m bu
  pushforward-id m bu = μ-cong m (λ x → (λ b → b) , (λ b → b)) (preimage measurable-id bu) bu

  pushforward-∘ : ∀ {f g} (mf : Measurable f) (mg : Measurable g) (m : Measure) {U} (bu : Borel U) →
    μ (pushforward (measurable-∘ mf mg) m) bu ≈ μ (pushforward mg (pushforward mf m)) bu
  pushforward-∘ mf mg m bu =
    μ-cong m (λ x → (λ b → b) , (λ b → b)) (preimage (measurable-∘ mf mg) bu) (preimage mf (preimage mg bu))
