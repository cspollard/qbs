{-# OPTIONS --safe --without-K #-}

-- Frequentist inference, layer 1 (see `plans/03-bayesian-frequentist.md`): experiments, statistics, bias, variance, mean
-- squared error and unbiasedness, built on the signed expectation of Plan 2.  Probabilities are over the data for a fixed
-- parameter.
--
-- An `Experiment Θ` gives, for every parameter, a probability space and a sequence of observations: bounded signed random
-- variables (`Analysis/BoundedRing`).  A statistic is a ring term in the observations (`Term`), so the sample mean and the
-- sample variance are statistics; `E`, `bias`, `variance` and `mse` are computed in the ring of random variables.  The
-- estimator theorem (`Analysis/Estimator`) then gives the unbiasedness results for every experiment whose observations have
-- the right moments, and `Inference/UniformExperiment` instantiates this for draws uniform on an interval.
--
-- SKELETON: the declarations are in place; the proofs marked by holes are the plan's next steps.
module QBS.Inference.Frequentist where

open import Algebra using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)

open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Estimator using (module Estimator)

----------------------------------------------------------------------------
-- statistics: ring terms in the observations

-- a polynomial with natural coefficients and negation, in the variables X₀, X₁, …
infixl 6 _+ₜ_
infixl 7 _*ₜ_
data Term : Set where
  var : ℕ → Term
  nat : ℕ → Term
  _+ₜ_ _*ₜ_ : Term → Term → Term
  -ₜ_ : Term → Term

-- a term in any commutative ring, given the values of the variables
module Eval {c ℓ} (R : CommutativeRing c ℓ) where
  private module R = CommutativeRing R

  natR : ℕ → R.Carrier
  natR zero = R.0#
  natR (suc n) = natR n R.+ R.1#

  eval : Term → (ℕ → R.Carrier) → R.Carrier
  eval (var i) X = X i
  eval (nat k) X = natR k
  eval (s +ₜ t) X = eval s X R.+ eval t X
  eval (s *ₜ t) X = eval s X R.* eval t X
  eval (-ₜ t) X = R.- eval t X

-- the sum of the first n observations, the sum of their squares, and n Q − S² (n² − n times the sample variance)
sumT sqT ssT : ℕ → Term
sumT zero = nat 0
sumT (suc n) = sumT n +ₜ var n
sqT zero = nat 0
sqT (suc n) = sqT n +ₜ var n *ₜ var n
ssT n = nat n *ₜ sqT n +ₜ -ₜ (sumT n *ₜ sumT n)

----------------------------------------------------------------------------
-- experiments and their inference quantities

module Frequentist (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  open import QBS.Analysis.CoinIntegral using (lemOf)
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (Measure; IsProb)
  open BoundedRing (lemOf lem₁) using (BSF; boundedRing; E-B; κB)
  open Bounded A using (Sg; _≃_; _+S_; -S_; _*S_; 0S)

  -- for each parameter a probability space with a sequence of observations
  record Experiment (Θ : Set) : Set₁ where
    field
      space : Θ → Measure
      prob : ∀ θ → IsProb (space θ)
      obs : ∀ θ → ℕ → BSF (space θ) (prob θ)

  module _ {Θ : Set} (ex : Experiment Θ) (θ : Θ) where
    open Experiment ex

    -- the ring of random variables at θ
    RV : CommutativeRing _ _
    RV = boundedRing (space θ) (prob θ)

    -- the statistic t, as a random variable
    value : Term → CommutativeRing.Carrier RV
    value t = Eval.eval RV t (obs θ)

    -- its expectation, bias for an estimand τ, variance and mean squared error
    expect : Term → Sg
    expect t = E-B (space θ) (prob θ) (value t)

    bias : (τ : Θ → Sg) → Term → Sg
    bias τ t = {!!}   -- expect t − τ θ

    variance : Term → Sg
    variance t = {!!}   -- E[(t − E t)²], with κB for the constant E t

    mse : (τ : Θ → Sg) → Term → Sg
    mse τ t = {!!}      -- E[(t − τ θ)²]

  -- unbiased for τ: the bias vanishes at every parameter value
  Unbiased : ∀ {Θ} → Experiment Θ → (Θ → Sg) → Term → Set₁
  Unbiased ex τ t = ∀ θ → bias ex θ τ t ≃ 0S

  -- the moment hypotheses on the observations at every parameter (cf. `Estimator.Moments`): identically distributed
  -- up to second moments, with mean μ θ and variance σ² θ, and pairwise uncorrelated
  record Moments {Θ : Set} (ex : Experiment Θ) (μ σ² : Θ → Sg) : Set₁ where
    open Experiment ex
    field
      mean : ∀ θ i → E-B (space θ) (prob θ) (obs θ i) ≃ μ θ
      second : ∀ θ i → E-B (space θ) (prob θ) (CommutativeRing._*_ (RV ex θ) (obs θ i) (obs θ i)) ≃ σ² θ +S (μ θ *S μ θ)
      uncorr : ∀ θ i j → i < j →
        E-B (space θ) (prob θ) (CommutativeRing._*_ (RV ex θ) (obs θ i) (obs θ j)) ≃ μ θ *S μ θ

  -- the theorems of the estimator layer, for every experiment with moments.  (The scaling by n stays division-free:
  -- the natural number n appears as a signed constant, `natS n`.)
  module _ {Θ : Set} {ex : Experiment Θ} {μ σ² : Θ → Sg} (mo : Moments ex μ σ²) where
    natS : ℕ → Sg
    natS n = {!!}   -- the signed constant n, as `Estimator.natS`

    -- E Sₙ = n μ  (so the sample mean Sₙ/n is unbiased for μ)
    expect-sum : ∀ θ n → expect ex θ (sumT n) ≃ natS n *S μ θ
    expect-sum θ n = {!!}   -- `Estimator.E-sum` at θ; `eval (sumT n)` is `sumR` by induction

    -- E (n Qₙ − Sₙ²) = (n² − n) σ²
    expect-ss : ∀ θ n → expect ex θ (ssT n) ≃ (natS n *S natS n +S -S natS n) *S σ² θ
    expect-ss θ n = {!!}   -- `Estimator.E-SS`
