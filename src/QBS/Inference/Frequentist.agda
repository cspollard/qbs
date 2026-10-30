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
module QBS.Inference.Frequentist where

open import Algebra using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; cong; cong₂; subst)

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
  open BoundedRing (lemOf lem₁) using (BSF; boundedRing; E-B; E-B-cong; E-B-+; κB)
  open Bounded A using (Sg; signedRing; _≃_; _+S_; -S_; _*S_; 0S; 1S)

  -- for each parameter a probability space with a sequence of observations
  record Experiment (Θ : Set₁) : Set₂ where
    field
      space : Θ → Measure
      prob : ∀ θ → IsProb (space θ)
      obs : ∀ θ → ℕ → BSF (space θ) (prob θ)

  module _ {Θ : Set₁} (ex : Experiment Θ) (θ : Θ) where
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

    private module RVm = CommutativeRing RV

    bias : (τ : Θ → Sg) → Term → Sg
    bias τ t = expect t +S (-S τ θ)

    -- E[(t − c)²] for a constant c: the variance at c = E t, the mean squared error at c = τ θ
    meanSq : Sg → Term → Sg
    meanSq c t = E-B (space θ) (prob θ) (d RVm.* d)
      where d = value t RVm.+ RVm.- κB (space θ) (prob θ) c

    variance : Term → Sg
    variance t = meanSq (expect t) t

    mse : (τ : Θ → Sg) → Term → Sg
    mse τ t = meanSq (τ θ) t

  -- unbiased for τ: the bias vanishes at every parameter value
  Unbiased : ∀ {Θ} → Experiment Θ → (Θ → Sg) → Term → Set₁
  Unbiased ex τ t = ∀ θ → bias ex θ τ t ≃ 0S

  -- t / k is unbiased for τ, without division (the signed ring has no inverses of naturals): E t = k τ at every parameter
  ScaledUnbiased : ∀ {Θ} → Experiment Θ → (Θ → Sg) → (Θ → Sg) → Term → Set₁
  ScaledUnbiased ex k τ t = ∀ θ → expect ex θ t ≃ k θ *S τ θ

  -- the moment hypotheses on the observations at every parameter (cf. `Estimator.Moments`): identically distributed
  -- up to second moments, with mean μ θ and variance σ² θ, and pairwise uncorrelated
  record Moments {Θ : Set₁} (ex : Experiment Θ) (μ σ² : Θ → Sg) : Set₂ where
    open Experiment ex
    field
      mean : ∀ θ i → E-B (space θ) (prob θ) (obs θ i) ≃ μ θ
      second : ∀ θ i → E-B (space θ) (prob θ) (CommutativeRing._*_ (RV ex θ) (obs θ i) (obs θ i)) ≃ σ² θ +S (μ θ *S μ θ)
      uncorr : ∀ θ i j → i < j →
        E-B (space θ) (prob θ) (CommutativeRing._*_ (RV ex θ) (obs θ i) (obs θ j)) ≃ μ θ *S μ θ

  -- the theorems of the estimator layer, for every experiment with moments.  (The scaling by n stays division-free:
  -- the natural number n appears as a signed constant, `natS n`.)
  module _ {Θ : Set₁} {ex : Experiment Θ} {μ σ² : Θ → Sg} (mo : Moments ex μ σ²) where
    natS : ℕ → Sg
    natS zero = 0S
    natS (suc n) = natS n +S 1S

    -- the estimator layer at the parameter θ, and the evaluation of the statistics against it
    module At (θ : Θ) where
      open Experiment ex
      module Est = Estimator signedRing (RV ex θ) (E-B (space θ) (prob θ))
        (E-B-cong (space θ) (prob θ)) (E-B-+ (space θ) (prob θ))

      est : Est.Moments (obs θ) (μ θ) (σ² θ)
      est = record { mean = Moments.mean mo θ ; second = Moments.second mo θ ; uncorr = Moments.uncorr mo θ }

      natS-eq : ∀ n → Est.natS n ≡ natS n
      natS-eq zero = refl
      natS-eq (suc n) = cong (λ x → x +S 1S) (natS-eq n)

      natR-eq : ∀ n → Eval.natR (RV ex θ) n ≡ Est.natR n
      natR-eq zero = refl
      natR-eq (suc n) = cong (λ x → x RVm.+ RVm.1#) (natR-eq n)
        where module RVm = CommutativeRing (RV ex θ)

      sum-eq : ∀ n → Eval.eval (RV ex θ) (sumT n) (obs θ) ≡ Est.sumR (obs θ) n
      sum-eq zero = refl
      sum-eq (suc n) = cong (λ x → x RVm.+ obs θ n) (sum-eq n)
        where module RVm = CommutativeRing (RV ex θ)

      sq-eq : ∀ n → Eval.eval (RV ex θ) (sqT n) (obs θ) ≡ Est.sumR (Est.sq (obs θ)) n
      sq-eq zero = refl
      sq-eq (suc n) = cong (λ x → x RVm.+ obs θ n RVm.* obs θ n) (sq-eq n)
        where module RVm = CommutativeRing (RV ex θ)

      ss-eq : ∀ n → Eval.eval (RV ex θ) (ssT n) (obs θ) ≡ Est.SS (obs θ) n
      ss-eq n = cong₂ (λ a b → a RVm.+ RVm.- b)
        (cong₂ RVm._*_ (natR-eq n) (sq-eq n))
        (cong₂ RVm._*_ (sum-eq n) (sum-eq n))
        where module RVm = CommutativeRing (RV ex θ)

    -- E Sₙ = n μ  (so the sample mean Sₙ/n is unbiased for μ)
    expect-sum : ∀ θ n → expect ex θ (sumT n) ≃ natS n *S μ θ
    expect-sum θ n =
      subst (λ v → E-B (Experiment.space ex θ) (Experiment.prob ex θ) v ≃ natS n *S μ θ) (sym (At.sum-eq θ n))
        (subst (λ k → E-B (Experiment.space ex θ) (Experiment.prob ex θ) (At.Est.sumR θ (Experiment.obs ex θ) n) ≃ k *S μ θ)
          (At.natS-eq θ n) (At.Est.E-sum θ (At.est θ) n))

    -- E (n Qₙ − Sₙ²) = (n² − n) σ²
    expect-ss : ∀ θ n → expect ex θ (ssT n) ≃ (natS n *S natS n +S -S natS n) *S σ² θ
    expect-ss θ n =
      subst (λ v → E-B (Experiment.space ex θ) (Experiment.prob ex θ) v ≃ (natS n *S natS n +S -S natS n) *S σ² θ)
        (sym (At.ss-eq θ n))
        (subst (λ k → E-B (Experiment.space ex θ) (Experiment.prob ex θ) (At.Est.SS θ (Experiment.obs ex θ) n)
                        ≃ (k *S k +S -S k) *S σ² θ)
          (At.natS-eq θ n) (At.Est.E-SS θ (At.est θ) n))

    -- Sₙ / n is unbiased for μ, and (n Qₙ − Sₙ²) / (n² − n) is unbiased for σ²
    sample-mean-unbiased : ∀ n → ScaledUnbiased ex (λ _ → natS n) μ (sumT n)
    sample-mean-unbiased n θ = expect-sum θ n

    sample-variance-unbiased : ∀ n → ScaledUnbiased ex (λ _ → natS n *S natS n +S -S natS n) σ² (ssT n)
    sample-variance-unbiased n θ = expect-ss θ n
