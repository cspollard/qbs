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
--
-- SKELETON: the declarations are in place; the proofs marked by holes are the plan's next steps.
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
open import QBS.Model.WeightClasses using (allClass; probClass)
open import QBS.Model.Monad
open import QBS.Example.Bayes using (posteriorU; evidence; _·_; posterior; bayes; bayes-numerator)

module Bayesian {ℓ} (N : NormalizableSemiring ℓ) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
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
    sequential f = {!!}

    -- the evidence is multiplicative: Z(x₁, x₂) = Z(x₁) · P(x₂ | x₁), with the unnormalised predictive Z(x₂ | x₁)
    evidence-sequential : evidence N (posteriorU N prior w₁) w₂ ≈ evidence N prior (_·_ N {X} w₁ w₂)
    evidence-sequential = {!!}

    -- the posterior predictive of the next observation, given an inverse n of the evidence of the first
    -- (`Example/Bayes.posterior`): P(x₂ | x₁) = n · Z(x₁, x₂)
    predictive-chain : ∀ (n : ∣A∣) (h : evidence N prior w₁ * n ≈ 1#) →
      evidence N prior w₁ * (n * evidence N prior (_·_ N {X} w₁ w₂)) ≈ evidence N prior (_·_ N {X} w₁ w₂)
    predictive-chain n h = {!!}

  ----------------------------------------------------------------------------
  -- the Bernoulli model over a discrete set of parameters

  -- parameters θ with success probability `p θ` and failure probability `q θ`, `p θ + q θ = 1`
  module Bernoulli {Θ : QBS (discreteSource ℓ)} (p q : Func (QBS.Carrier Θ) Aˢ)
      (pq : ∀ θ → (p ⟨$⟩ θ) + (q ⟨$⟩ θ) ≈ 1#) where

    -- the likelihood of one observation, and of a sequence of independent observations
    lik : Bool → Func (QBS.Carrier Θ) Aˢ
    lik b = {!!}   -- p if b, q otherwise

    likSeq : List Bool → Func (QBS.Carrier Θ) Aˢ
    likSeq xs = {!!}   -- the pointwise product of the likelihoods

    -- the numbers of successes and failures
    successes failures : List Bool → ℕ
    successes xs = {!!}
    failures xs = {!!}

    -- the likelihood of a sequence is `p^s q^f`: it depends on the data only through the counts
    likSeq-counts : ∀ xs θ → (likSeq xs ⟨$⟩ θ) ≈ pow (p ⟨$⟩ θ) (successes xs) * pow (q ⟨$⟩ θ) (failures xs)
    likSeq-counts xs θ = {!!}

    -- updating one observation at a time is updating with the sequence
    update : Pre Θ → List Bool → Pre Θ
    update prior [] = prior
    update prior (b ∷ bs) = update (posteriorU N prior (lik b)) bs

    posterior-seq : ∀ (prior : Pre Θ) xs →
      update prior xs ≈ᵖ posteriorU N prior (likSeq xs)
    posterior-seq prior xs = {!!}

    -- sequences with equal counts give equal posteriors
    posterior-exchangeable : ∀ (prior : Pre Θ) xs ys → successes xs ≡ successes ys → failures xs ≡ failures ys →
      posteriorU N prior (likSeq xs) ≈ᵖ posteriorU N prior (likSeq ys)
    posterior-exchangeable prior xs ys hs hf = {!!}
