{-# OPTIONS --safe --without-K #-}

-- The Gaussian N(μ, σ²) from the standard one by the affine statistic `x ↦ μ + σx` (item B of `plans/03`), with no new integral.
-- `RQ = WQ +Q WQ` has no addition, so the affine map is not a `Hom` into `RQ`; by the pushforward principle
-- (`Inference/PushforwardExpectation`, `E_{f∗p}[g] = E_p[g ∘ f]`) the expectation under N(μ, σ²) of a test `g` is the expectation under
-- N(0,1) of the signed statistic `g(μ + σX)`.  For the identity and the square this statistic is built by the linearity of
-- `Inference/ExpectationInt` from the constant test `constI`, `xI` (`X`) and `sqI` (`X²`) of `Inference/GaussReal`, for signed `μ`, `σ : Sg`
-- (a cut `a` is the signed value `ι a`):
--   * `affI m s = m + s·X : ITest gaussR` with `E-atᴵ-affI : E[μ + σX] ≃ μ` (from `E[X] ≃ 0`);
--   * `aff2I m s = (μ² + 2μσ·X) + σ²·X²` is `(μ + σX)²` as a signed function, and `E-atᴵ-aff2I′ : E[Y²] ≃ (μ² + 2μσ·E[X]) + σ²·E[X²]`;
--   * `var-affI : E[Y²] − (E Y)² ≃ σ²` for `Y = μ + σX` (`Analysis/AffineAlg.var-aff`).
module QBS.Inference.GaussAffine where

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.AffineAlg using (module AlgAff)
open import QBS.Inference.GaussReal using (module GaussReal)
open import QBS.Inference.PushforwardExpectation using (module PushforwardExpectation)
import QBS.Inference.ExpectationInt as EI

module GaussAffine (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Sg; _≃_; ≃-trans; _+S_; _*S_; -S_; +S-cong; 0S; 1S; _−_[_,_])
  open AlgAff A using (mean-aff; var-aff)
  open GaussReal lem₁ using (gaussR; xI; sqI; E-atᴵ-X; E-atᴵ-X²)
  open PushforwardExpectation lem₁ using (constI; E-atᴵ-const)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ; _+I_; scaleI; E-atᴵ-+; E-atᴵ-scale)

  -- E[X] ≃ 0 and E[X²] ≃ 1 as signed values
  EX : E-atᴵ gaussR xI ≃ 0S
  EX = E-atᴵ-X

  EX² : E-atᴵ gaussR sqI ≃ 1S
  EX² = E-atᴵ-X²

  ----------------------------------------------------------------------------
  -- the statistic μ + σX

  affI : Sg → Sg → ITest gaussR
  affI m s = constI gaussR m +I scaleI s xI

  E-atᴵ-affI′ : ∀ m s → E-atᴵ gaussR (affI m s) ≃ (m +S (s *S E-atᴵ gaussR xI))
  E-atᴵ-affI′ m s = ≃-trans (E-atᴵ-+ gaussR (constI gaussR m) (scaleI s xI))
    (+S-cong (E-atᴵ-const gaussR m) (E-atᴵ-scale gaussR s xI))

  -- E[μ + σX] ≃ μ
  E-atᴵ-affI : ∀ m s → E-atᴵ gaussR (affI m s) ≃ m
  E-atᴵ-affI m s = mean-aff m s (E-atᴵ gaussR xI) (E-atᴵ gaussR (affI m s)) EX (E-atᴵ-affI′ m s)

  ----------------------------------------------------------------------------
  -- the square (μ + σX)²

  aff2I : Sg → Sg → ITest gaussR
  aff2I m s = (constI gaussR (m *S m) +I scaleI ((m +S m) *S s) xI) +I scaleI (s *S s) sqI

  E-atᴵ-aff2I′ : ∀ m s → E-atᴵ gaussR (aff2I m s)
    ≃ (((m *S m) +S (((m +S m) *S s) *S E-atᴵ gaussR xI)) +S ((s *S s) *S E-atᴵ gaussR sqI))
  E-atᴵ-aff2I′ m s = ≃-trans (E-atᴵ-+ gaussR (constI gaussR (m *S m) +I scaleI ((m +S m) *S s) xI) (scaleI (s *S s) sqI))
    (+S-cong (≃-trans (E-atᴵ-+ gaussR (constI gaussR (m *S m)) (scaleI ((m +S m) *S s) xI))
                (+S-cong (E-atᴵ-const gaussR (m *S m)) (E-atᴵ-scale gaussR ((m +S m) *S s) xI)))
             (E-atᴵ-scale gaussR (s *S s) sqI))

  -- the variance: E[Y²] − (E Y)² ≃ σ²
  var-affI : ∀ m s → (E-atᴵ gaussR (aff2I m s) +S (-S (E-atᴵ gaussR (affI m s) *S E-atᴵ gaussR (affI m s)))) ≃ (s *S s)
  var-affI m s = var-aff m s (E-atᴵ gaussR xI) (E-atᴵ gaussR sqI) (E-atᴵ gaussR (affI m s)) (E-atᴵ gaussR (aff2I m s))
    EX EX² (E-atᴵ-affI′ m s) (E-atᴵ-aff2I′ m s)
