{-# OPTIONS --safe --without-K #-}

-- Bayesian inference over the discrete model (see `plans/03-bayesian-frequentist.md`, stage 3b).  Probabilities are over the
-- parameter given fixed data.  A prior is a measure on the parameter space; an observation `x` enters through its
-- likelihood `w θ = P(x | θ)`; the posterior is the prior reweighted by the likelihood and normalised by the evidence
-- (`Example/Bayes`).  This module adds what a statistician uses on top of the bare rule:
--   * sequential updating: observing x₁ then x₂ is observing both, with the product likelihood;
--   * the chain rule for the evidence, and the posterior predictive;
--   * the Bernoulli model with a discrete set of parameters, where the likelihood of a sequence of observations depends
--     only on the numbers of successes and failures (the sufficiency that makes Beta–Bernoulli conjugacy work).
-- Everything is stated without division: normalisation appears only through an inverse `n` of the evidence, as in
-- `Example/Bayes`.
module QBS.Inference.Bayesian where

open import Level using (Level)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.WeightClasses using (allClass; probClass)
open import QBS.Model.Monad
open import QBS.Example.Bayes using (posteriorU; evidence; _·_; posterior; bayes; bayes-numerator)

module Bayesian {ℓ} (N : NormalizableSemiring ℓ) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  module MA = Measures A (allClass A)
  open MA using (Pre; mk; ∫; _≈ᵖ_)

  -- powers
  pow : ∣A∣ → ℕ → ∣A∣
  pow x zero = 1#
  pow x (suc n) = x * pow x n

  ----------------------------------------------------------------------------
  -- sequential updating and the posterior predictive

  module _ {X : QBS (discreteSource ℓ)} (prior : Pre X) (w₁ w₂ : Func (QBS.Carrier X) Aˢ) where

    -- observing w₁ and then w₂ is observing the product likelihood
    sequential : posteriorU N (posteriorU N prior w₁) w₂ ≈ᵖ posteriorU N prior (_·_ N {X} w₁ w₂)
    sequential f = trans (bayes-numerator N (posteriorU N prior w₁) w₂ f)
      (trans (bayes-numerator N prior w₁ (_·_ N {X} w₂ f))
        (trans (∑-cong (λ r → *-cong refl (sym (*-assoc _ _ _))))
          (sym (bayes-numerator N prior (_·_ N {X} w₁ w₂) f))))

    -- the evidence is multiplicative: Z(x₁, x₂) = Z(x₁) · P(x₂ | x₁), with the unnormalised predictive Z(x₂ | x₁)
    evidence-sequential : evidence N (posteriorU N prior w₁) w₂ ≈ evidence N prior (_·_ N {X} w₁ w₂)
    evidence-sequential = bayes-numerator N prior w₁ w₂

    -- the posterior predictive of the next observation, given an inverse n of the evidence of the first
    -- (`Example/Bayes.posterior`): P(x₂ | x₁) = n · Z(x₁, x₂)
    predictive-chain : ∀ (n : ∣A∣) (h : evidence N prior w₁ * n ≈ 1#) →
      evidence N prior w₁ * (n * evidence N prior (_·_ N {X} w₁ w₂)) ≈ evidence N prior (_·_ N {X} w₁ w₂)
    predictive-chain n h = trans (sym (*-assoc _ _ _)) (trans (*-cong h refl) (*-identityˡ _))

  ----------------------------------------------------------------------------
  -- the Bernoulli model over a discrete set of parameters

  -- parameters θ with success probability `p θ` and failure probability `q θ`, `p θ + q θ = 1`
  module Bernoulli {Θ : QBS (discreteSource ℓ)} (p q : Func (QBS.Carrier Θ) Aˢ)
      (pq : ∀ θ → (p ⟨$⟩ θ) + (q ⟨$⟩ θ) ≈ 1#) where

    -- the likelihood of one observation, and of a sequence of independent observations
    lik : Bool → Func (QBS.Carrier Θ) Aˢ
    lik true = p
    lik false = q

    one : Func (QBS.Carrier Θ) Aˢ
    one = record { to = λ _ → 1# ; cong = λ _ → refl }

    likSeq : List Bool → Func (QBS.Carrier Θ) Aˢ
    likSeq [] = one
    likSeq (b ∷ bs) = _·_ N {Θ} (lik b) (likSeq bs)

    -- the numbers of successes and failures
    successes failures : List Bool → ℕ
    successes [] = 0
    successes (true ∷ xs) = suc (successes xs)
    successes (false ∷ xs) = successes xs
    failures [] = 0
    failures (true ∷ xs) = failures xs
    failures (false ∷ xs) = suc (failures xs)

    -- the likelihood of a sequence is `p^s q^f`: it depends on the data only through the counts
    likSeq-counts : ∀ xs θ → (likSeq xs ⟨$⟩ θ) ≈ pow (p ⟨$⟩ θ) (successes xs) * pow (q ⟨$⟩ θ) (failures xs)
    likSeq-counts [] θ = sym (*-identityˡ 1#)
    likSeq-counts (true ∷ xs) θ = trans (*-cong refl (likSeq-counts xs θ)) (sym (*-assoc _ _ _))
    likSeq-counts (false ∷ xs) θ = trans (*-cong refl (likSeq-counts xs θ))
      (trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _)))

    -- updating one observation at a time is updating with the sequence
    update : Pre Θ → List Bool → Pre Θ
    update prior [] = prior
    update prior (b ∷ bs) = update (posteriorU N prior (lik b)) bs

    posterior-seq : ∀ (prior : Pre Θ) xs →
      update prior xs ≈ᵖ posteriorU N prior (likSeq xs)
    posterior-seq prior [] f = trans (∑-cong (λ r → refl))
      (trans (∑-cong (λ r → *-cong refl (sym (*-identityˡ _)))) (sym (bayes-numerator N prior one f)))
    posterior-seq prior (b ∷ bs) f = trans (posterior-seq (posteriorU N prior (lik b)) bs f)
      (sequential prior (lik b) (likSeq bs) f)

    -- sequences with equal counts give equal posteriors
    posterior-exchangeable : ∀ (prior : Pre Θ) xs ys → successes xs ≡ successes ys → failures xs ≡ failures ys →
      posteriorU N prior (likSeq xs) ≈ᵖ posteriorU N prior (likSeq ys)
    posterior-exchangeable prior xs ys hs hf f = trans (bayes-numerator N prior (likSeq xs) f)
      (trans (∑-cong (λ r → *-cong refl (*-cong (same (MA.Pre.α prior r)) refl)))
        (sym (bayes-numerator N prior (likSeq ys) f)))
      where
        same : ∀ θ → (likSeq xs ⟨$⟩ θ) ≈ (likSeq ys ⟨$⟩ θ)
        same θ = trans (likSeq-counts xs θ) (trans (counts θ) (sym (likSeq-counts ys θ)))
          where
            counts : ∀ θ → pow (p ⟨$⟩ θ) (successes xs) * pow (q ⟨$⟩ θ) (failures xs)
                           ≈ pow (p ⟨$⟩ θ) (successes ys) * pow (q ⟨$⟩ θ) (failures ys)
            counts θ rewrite hs | hf = refl

    -- the evidence is a distribution on the data: Z(heads) + Z(tails) is the total mass of the prior, which is 1 for a
    -- probability prior (this is where `p θ + q θ = 1` is used)
    evidence-total : ∀ (prior : Pre Θ) → evidence N prior p + evidence N prior q ≈ ∫ prior one
    evidence-total prior = trans (sym (∑-+ _ _))
      (∑-cong (λ r → trans (sym (distribˡ _ _ _)) (*-cong refl (pq (MA.Pre.α prior r)))))

    evidence-total-prob : ∀ (prior : Pre Θ) → ∫ prior one ≈ 1# → evidence N prior p + evidence N prior q ≈ 1#
    evidence-total-prob prior h = trans (evidence-total prior) h
