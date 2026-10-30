{-# OPTIONS --safe --without-K #-}

-- Estimation from independent draws uniform on an interval: `Yᵢ = a + c · Xᵢ` with `Xᵢ` the uniform draws of
-- `UniformSample` (`c = b − a` for the interval [a, b]; `a` and `c` are any signed values).  The affine part of
-- `Analysis/Estimator` gives the moments `μ′ = a + c/2`, `σ′² = c²/12`, and then, for `Tₙ = Y₀ + … + Y_{n−1}`
-- and `Qₙ = ΣYᵢ²`, without division:
--   E Tₙ + E Tₙ = n (a + a + c)          (the sample mean is unbiased for a + c/2)
--   12 · Var Tₙ = n c²                   (Var ȳ = c²/(12 n))
--   12 · E (n Qₙ − Tₙ²) = (n² − n) c²    (the sample variance is unbiased for c²/12)
module QBS.Continuous.UniformInterval where

open import Algebra using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_)
import Level as L
open import Axiom.Extensionality.Propositional using (Extensionality)
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver

open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Variance using (module Arith)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.UniformVariance using (module UniformVariance)
open import QBS.Continuous.UniformSample using (module UniformSample)

module UniformInterval (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open Lebesgue (lemOf lem₁) using (A)
  open UniformVariance lem₁ using (u; varU; pm; variance; mean-u)
  module US = UniformSample lem₁ funext
  open BoundedRing (lemOf lem₁) using (boundedRing; E-B; κB; E-κB; E-κB*)
  open Bounded A using (Sg; finite; signedRing; _≃_; ≃-trans; ≃-sym; ≃-refl; _+S_; _*S_; -S_; 1S; +S-cong; *S-congʳ; *S-identityʳ; *S-assoc; *S-distribˡ)
  open SignedIntegral (lemOf lem₁) using (E)
  open Arith (OmegaSemiring.commutativeSemiring A) finite using (x12)
  open FairCoin lem₁ using (fairCoin)
  module SolveSg = Solver (CommutativeRing.commutativeSemiring signedRing)

  module BRm = CommutativeRing (boundedRing fairCoin pm)
  module Aff = US.Est.Affine (κB fairCoin pm) (E-κB fairCoin pm) (E-κB* fairCoin pm)

  module _ (a c : Sg) where
    -- the draws Yᵢ = a + c Xᵢ and their moments
    -- the variance c² σ², kept opaque
    abstract
      σc : Sg
      σc = c *S c *S varU

      σc-eq : σc ≃ c *S c *S varU
      σc-eq = ≃-refl {c *S c *S varU}

    abstract
      Y : ℕ → BRm.Carrier
      Y = Aff.affine US.X a c

      momentsY : US.Est.Moments Y (a +S c *S E u) σc
      momentsY = Aff.affine-moments US.moments a c

    TT : ℕ → Sg
    TT n = E-B fairCoin pm (US.Est.sumR Y n)

    -- E Tₙ = n (a + c/2)
    interval-mean : ∀ n → TT n ≃ US.Est.natS n *S (a +S c *S E u)
    interval-mean = US.Est.E-sum momentsY

    -- Var Tₙ = E Tₙ² − (E Tₙ)²
    VarT : ℕ → Sg
    VarT n = E-B fairCoin pm (US.Est.sumR Y n BRm.* US.Est.sumR Y n) +S (-S (TT n *S TT n))

    VarT-eq : ∀ n → VarT n ≃ (US.Est.natS n *S (c *S c)) *S varU
    VarT-eq n = ≃-trans {VarT n} {US.Est.natS n *S σc} {(US.Est.natS n *S (c *S c)) *S varU}
      (US.Est.var-sum momentsY n) (≃-trans {US.Est.natS n *S σc} {US.Est.natS n *S (c *S c *S varU)} {(US.Est.natS n *S (c *S c)) *S varU}
        (*S-congʳ (US.Est.natS n) {σc} {c *S c *S varU} σc-eq)
        (≃-sym {(US.Est.natS n *S (c *S c)) *S varU} {US.Est.natS n *S (c *S c *S varU)} (*S-assoc (US.Est.natS n) (c *S c) varU)))

    -- 12 Var Tₙ = n c²
    interval-variance : ∀ n → x12 (VarT n) ≃ US.Est.natS n *S (c *S c)
    interval-variance n = US.x12-scaled (VarT n) (US.Est.natS n *S (c *S c)) varU (VarT-eq n) variance

    -- n² − n, and E (n Qₙ − Tₙ²) = (n² − n) c² σ²
    ESS′ : ℕ → Sg
    ESS′ n = E-B fairCoin pm (US.Est.SS Y n)

    ESS′-raw : ∀ n → ESS′ n ≃ US.nn n *S σc
    ESS′-raw n = US.ESS-gen {Y} {a +S c *S E u} {σc} momentsY n

    ESS′-eq : ∀ n → ESS′ n ≃ (US.nn n *S (c *S c)) *S varU
    ESS′-eq n = ≃-trans {ESS′ n} {US.nn n *S σc} {(US.nn n *S (c *S c)) *S varU}
      (ESS′-raw n) (≃-trans {US.nn n *S σc} {US.nn n *S (c *S c *S varU)} {(US.nn n *S (c *S c)) *S varU}
        (*S-congʳ (US.nn n) {σc} {c *S c *S varU} σc-eq)
        (≃-sym {(US.nn n *S (c *S c)) *S varU} {US.nn n *S (c *S c *S varU)} (*S-assoc (US.nn n) (c *S c) varU)))

    -- 12 E (n Qₙ − Tₙ²) = (n² − n) c²
    interval-sample-variance : ∀ n → x12 (ESS′ n) ≃ US.nn n *S (c *S c)
    interval-sample-variance n = US.x12-scaled (ESS′ n) (US.nn n *S (c *S c)) varU (ESS′-eq n) variance

    -- (a + c μ) + (a + c μ) = (a + a) + c when μ + μ = 1
    twice-mean : (a +S c *S E u) +S (a +S c *S E u) ≃ (a +S a) +S c
    twice-mean = ≃-trans {(a +S c *S E u) +S (a +S c *S E u)} {(a +S a) +S c *S (E u +S E u)} {(a +S a) +S c}
      (SolveSg.solve 3 (λ a c μ → (a SolveSg.:+ c SolveSg.:* μ) SolveSg.:+ (a SolveSg.:+ c SolveSg.:* μ) SolveSg.:=
                                  (a SolveSg.:+ a) SolveSg.:+ c SolveSg.:* (μ SolveSg.:+ μ)) ≃-refl a c (E u))
      (+S-cong {a +S a} {a +S a} {c *S (E u +S E u)} {c} (≃-refl {a +S a})
        (≃-trans {c *S (E u +S E u)} {c *S 1S} {c} (*S-congʳ c {E u +S E u} {1S} mean-u) (*S-identityʳ c)))

    -- 2 E Tₙ = n (2a + c): the sample mean is unbiased for a + c/2
    interval-mean-unbiased : ∀ n → TT n +S TT n ≃ US.Est.natS n *S ((a +S a) +S c)
    interval-mean-unbiased n = ≃-trans {TT n +S TT n} {US.Est.natS n *S M +S US.Est.natS n *S M} {US.Est.natS n *S ((a +S a) +S c)}
      (+S-cong {TT n} {US.Est.natS n *S M} {TT n} {US.Est.natS n *S M} (interval-mean n) (interval-mean n))
      (≃-trans {US.Est.natS n *S M +S US.Est.natS n *S M} {US.Est.natS n *S (M +S M)} {US.Est.natS n *S ((a +S a) +S c)}
        (≃-sym {US.Est.natS n *S (M +S M)} {US.Est.natS n *S M +S US.Est.natS n *S M} (*S-distribˡ (US.Est.natS n) M M))
        (*S-congʳ (US.Est.natS n) {M +S M} {(a +S a) +S c} twice-mean))
      where M = a +S c *S E u
