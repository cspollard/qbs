{-# OPTIONS --safe --without-K #-}

-- Bayes' rule for the discrete model, generic in the normalisable semiring.  posterior = prior reweighted by a likelihood, normalised by the evidence.
module QBS.Example.Bayes where

open import Level using (Level; Lift; lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.WeightClasses using (allClass; probClass)

module _ {ℓ} (N : NormalizableSemiring ℓ) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  module MA = Measures A (allClass A)
  module MP = Measures A (probClass A)
  open MA using (Pre; mk; ∫)
  open Pre

  -- pointwise product of test functions
  infixl 7 _·_
  _·_ : ∀ {X : QBS (discreteSource ℓ)} → Func (QBS.Carrier X) Aˢ → Func (QBS.Carrier X) Aˢ → Func (QBS.Carrier X) Aˢ
  _·_ {X} f g = record
    { to = λ x → (f ⟨$⟩ x) * (g ⟨$⟩ x)
    ; cong = λ e → *-cong (Func.cong f e) (Func.cong g e) }

  -- the unnormalised posterior: weight each point of the prior by the likelihood of the data there
  posteriorU : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Func (QBS.Carrier X) Aˢ → Pre X
  posteriorU p w = mk (α p) (α-random p) (λ r → μ p r * (w ⟨$⟩ α p r)) _

  -- the evidence Z = ∫ prior · likelihood
  evidence : ∀ {X : QBS (discreteSource ℓ)} → Pre X → Func (QBS.Carrier X) Aˢ → ∣A∣
  evidence p w = ∫ p w

  -- Bayes' numerator: ∫ posteriorU f = ∫ prior (_·_ {X} w f)
  bayes-numerator : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (w f : Func (QBS.Carrier X) Aˢ) →
    ∫ (posteriorU p w) f ≈ ∫ p (_·_ {X} w f)
  bayes-numerator p w f = ∑-cong (λ r → trans (*-assoc _ _ _) refl)

  -- the normalised posterior, given an inverse n of the evidence, is a probability measure with
  -- ∫ posterior f = n · ∫ prior (_·_ {X} w f)
  posterior : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (w : Func (QBS.Carrier X) Aˢ) (n : ∣A∣) →
    evidence p w * n ≈ 1# → MP.Pre X
  posterior p w n h = MP.mk (α p) (α-random p) (λ r → n * (μ p r * (w ⟨$⟩ α p r)))
    (trans (∑-scale n _) (trans (*-comm n _) h))

  bayes : ∀ {X : QBS (discreteSource ℓ)} (p : Pre X) (w f : Func (QBS.Carrier X) Aˢ) (n : ∣A∣)
    (h : evidence p w * n ≈ 1#) → MP.∫ (posterior p w n h) f ≈ n * ∫ p (_·_ {X} w f)
  bayes p w f n h = trans (∑-cong (λ r → *-assoc n (μ p r * (w ⟨$⟩ α p r)) (f ⟨$⟩ α p r)))
    (trans (∑-scale n _) (*-cong refl (bayes-numerator p w f)))
