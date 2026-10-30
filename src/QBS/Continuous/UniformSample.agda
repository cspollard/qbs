{-# OPTIONS --safe --without-K #-}

-- Estimation from independent uniform draws.  `Xᵢ = u ∘ coordᵢ` (`CoinCoords`) are identically distributed
-- pairwise independent copies of the uniform variable `u` on the fair coin, with mean ½ and variance 1/12
-- (`UniformVariance`).  The generic estimator theorem (`Analysis/Estimator`, over the ring of bounded signed
-- functions of `Analysis/BoundedRing`) gives, for `Sₙ = X₀ + … + X_{n−1}`, without division:
--   E Sₙ = n · ½                                (the sample mean is unbiased)
--   12 · Var Sₙ = n                             (Var x̄ = σ²/n with σ² = 1/12)
--   12 · E (n Qₙ − Sₙ²) = n² − n                (the sample variance is unbiased)
--
module QBS.Continuous.UniformSample where

open import Algebra using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product.Base using (_,_; proj₁)
import Level as L
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Sum.Base using (_⊎_)

open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Estimator using (module Estimator)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Variance using (module Variance; module Arith)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.CoinCoords using (module CoinCoords)
open import QBS.Continuous.UniformVariance using (module UniformVariance)

module UniformSample (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open UniformVariance lem₁ using (u; u-bdd; uu; varU; pm; vf; variance; mean-u; moment-u)
  open Lebesgue (lemOf lem₁) using (A)
  open CoinCoords lem₁ funext using (coordSF; coordSF-bdd; E-coord; E-indep)
  open BoundedRing (lemOf lem₁) using (boundedRing; E-B; E-B-cong; E-B-+)
  open Bounded A using (Sg; finite; signedRing; _≃_; ≃-trans; ≃-sym; ≃-refl; _+S_; _*S_; -S_; 0S; 1S; +S-cong; +S-assoc; +S-comm; +S-identityˡ; +S-inverseˡ; *S-congʳ; *S-identityʳ; *S-distribˡ)
  open SignedIntegral (lemOf lem₁) using (E; E-cong)
  open Variance (lemOf lem₁) using (_*SF_[_])
  open Arith (OmegaSemiring.commutativeSemiring A) finite using (x12; x12-cong; x12-*)
  open FairCoin lem₁ using (fairCoin)

  private BR = boundedRing fairCoin pm
  module BRm = CommutativeRing BR

  -- the i-th draw
  X : ℕ → CommutativeRing.Carrier BR
  X i = coordSF i u , coordSF-bdd i u u-bdd

  module Est = Estimator signedRing BR (E-B fairCoin pm) (E-B-cong fairCoin pm) (E-B-+ fairCoin pm)

  -- a ≃ b − c gives b ≃ a + c
  shift-sub : ∀ {a b c : Sg} → a ≃ b +S (-S c) → b ≃ a +S c
  shift-sub {a} {b} {c} h = ≃-sym {a +S c} {b} (≃-trans {a +S c} {(b +S (-S c)) +S c} {b}
    (+S-cong {a} {b +S (-S c)} {c} {c} h (≃-refl {c}))
    (≃-trans {(b +S (-S c)) +S c} {b +S ((-S c) +S c)} {b} (+S-assoc b (-S c) c)
      (≃-trans {b +S ((-S c) +S c)} {b +S 0S} {b} (+S-cong {b} {b} {(-S c) +S c} {0S} (≃-refl {b}) (+S-inverseˡ c))
        (≃-trans {b +S 0S} {0S +S b} {b} (+S-comm b 0S) (+S-identityˡ b)))))

  -- E (Xᵢ²) = Var u + (E u)²
  second-moment : ∀ i → E-B fairCoin pm (X i BRm.* X i) ≃ varU +S (E u *S E u)
  second-moment i = ≃-trans {E-B fairCoin pm (X i BRm.* X i)} {E (coordSF i uu)} {varU +S (E u *S E u)}
    (E-cong {fairCoin} {proj₁ (X i BRm.* X i)} {coordSF i uu} (λ x → OmegaSemiring.refl A))
    (≃-trans {E (coordSF i uu)} {E uu} {varU +S (E u *S E u)} (E-coord i uu) (shift-sub {varU} {E uu} {E u *S E u} vf))

  -- mean μ = E u, variance σ² = Var u
  moments : Est.Moments X (E u) varU
  moments = record
    { mean = λ i → E-coord i u
    ; second = second-moment
    ; uncorr = λ i j h → E-indep i j h u u u-bdd }

  -- the sample mean is unbiased: E Sₙ = n · (E u) with E u = ½ (so 2 E Sₙ = n)
  sample-mean : ∀ n → E-B fairCoin pm (Est.sumR X n) ≃ Est.natS n *S E u
  sample-mean = Est.E-sum moments

  -- twelve copies of q·σ² are q when twelve copies of σ² are one
  x12-scaled : ∀ (V q σ : Sg) → V ≃ q *S σ → x12 σ ≃ 1S → x12 V ≃ q
  x12-scaled V q σ h hσ = ≃-trans {x12 V} {x12 (q *S σ)} {q} (x12-cong {V} {q *S σ} h)
    (≃-trans {x12 (q *S σ)} {q *S x12 σ} {q} (x12-* q σ)
      (≃-trans {q *S x12 σ} {q *S 1S} {q} (*S-congʳ q {x12 σ} {1S} hσ) (*S-identityʳ q)))

  -- E Sₙ = n · (E u), and E u + E u = 1: 2 E Sₙ = n
  ES : ℕ → Sg
  ES n = E-B fairCoin pm (Est.sumR X n)

  sample-mean-unbiased : ∀ n → ES n +S ES n ≃ Est.natS n
  sample-mean-unbiased n = ≃-trans {ES n +S ES n} {(Est.natS n *S E u) +S (Est.natS n *S E u)} {Est.natS n}
    (+S-cong {ES n} {Est.natS n *S E u} {ES n} {Est.natS n *S E u} (sample-mean n) (sample-mean n))
    (≃-trans {(Est.natS n *S E u) +S (Est.natS n *S E u)} {Est.natS n *S (E u +S E u)} {Est.natS n}
      (≃-sym {Est.natS n *S (E u +S E u)} {(Est.natS n *S E u) +S (Est.natS n *S E u)} (*S-distribˡ (Est.natS n) (E u) (E u)))
      (≃-trans {Est.natS n *S (E u +S E u)} {Est.natS n *S 1S} {Est.natS n}
        (*S-congʳ (Est.natS n) {E u +S E u} {1S} mean-u) (*S-identityʳ (Est.natS n))))

  -- Var Sₙ = E Sₙ² − (E Sₙ)²
  VarS : ℕ → Sg
  VarS n = E-B fairCoin pm (Est.sumR X n BRm.* Est.sumR X n) +S (-S (E-B fairCoin pm (Est.sumR X n) *S E-B fairCoin pm (Est.sumR X n)))

  VarS-eq : ∀ n → VarS n ≃ Est.natS n *S varU
  VarS-eq n = Est.var-sum moments n

  -- 12 Var Sₙ = n (Var x̄ = σ²/n with σ² = 1/12)
  sample-mean-variance : ∀ n → x12 (VarS n) ≃ Est.natS n
  sample-mean-variance n = x12-scaled (VarS n) (Est.natS n) varU (VarS-eq n) variance

  -- E (n Qₙ − Sₙ²) = (n² − n) σ²
  ESS : ℕ → Sg
  ESS n = E-B fairCoin pm (Est.SS X n)

  ESS-eq : ∀ n → ESS n ≃ (Est.natS n *S Est.natS n +S (-S (Est.natS n))) *S varU
  ESS-eq n = Est.E-SS moments n

  -- 12 · E (n Qₙ − Sₙ²) = n² − n: the sample variance is unbiased
  sample-variance : ∀ n → x12 (ESS n) ≃ Est.natS n *S Est.natS n +S (-S (Est.natS n))
  sample-variance n = x12-scaled (ESS n) (Est.natS n *S Est.natS n +S (-S (Est.natS n))) varU (ESS-eq n) variance
