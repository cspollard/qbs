{-# OPTIONS --safe --without-K #-}

-- The first instance of `Inference/Frequentist`: independent draws uniform on an interval.  The parameter is the pair
-- `(a , c)` of signed values (the interval [a, a + c]), the probability space is the fair coin for every parameter, and
-- the observations are `Yᵢ = a + c · Xᵢ` (`Continuous/UniformInterval`).  The unbiasedness theorems of the generic layer
-- apply: `Sₙ / n` is unbiased for the mean `a + c · ½`, and `(n Qₙ − Sₙ²) / (n² − n)` for the variance `c² σ²` (σ² = 1/12).
module QBS.Inference.UniformExperiment where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_)
import Level as L

open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.UniformVariance using (module UniformVariance)
open import QBS.Continuous.UniformInterval using (module UniformInterval)
open import QBS.Inference.Frequentist

module UniformExperiment (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _+S_; _*S_; -S_)
  open SignedIntegral (lemOf lem₁) using (E)
  open UniformVariance lem₁ using (u; pm)
  module UI = UniformInterval lem₁
  module F = Frequentist lem₁
  open FairCoin lem₁ using (fairCoin)

  -- the parameters (a , c)
  Par : Set₁
  Par = Sg × Sg

  uniformExp : F.Experiment Par
  uniformExp = record
    { space = λ _ → fairCoin
    ; prob = λ _ → pm
    ; obs = λ { (a , c) → UI.Y a c } }

  mean : Par → Sg
  mean (a , c) = a +S c *S E u

  variance : Par → Sg
  variance (a , c) = UI.σc a c

  moments : F.Moments uniformExp mean variance
  moments = record
    { mean = λ { (a , c) i → UI.US.Est.Moments.mean (UI.momentsY a c) i }
    ; second = λ { (a , c) i → UI.US.Est.Moments.second (UI.momentsY a c) i }
    ; uncorr = λ { (a , c) i j h → UI.US.Est.Moments.uncorr (UI.momentsY a c) i j h } }

  -- the sample mean is unbiased for a + c/2
  sample-mean-unbiased : ∀ n → F.ScaledUnbiased uniformExp (λ _ → F.natS moments n) mean (sumT n)
  sample-mean-unbiased = F.sample-mean-unbiased moments

  -- the sample variance is unbiased for c² σ²
  sample-variance-unbiased : ∀ n → F.ScaledUnbiased uniformExp
    (λ _ → F.natS moments n *S F.natS moments n +S -S F.natS moments n) variance (ssT n)
  sample-variance-unbiased = F.sample-variance-unbiased moments
