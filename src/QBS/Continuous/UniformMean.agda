{-# OPTIONS --safe --without-K #-}

-- The mean of the uniform distribution on [0,1] is ½: ∫ expansion dμ = ½, by self-similarity (split
-- off the first bit, as `UniformMoment` and `SelfSimilar` do) and cancellation.
-- Consequently the soft-conditioned uniform draw (weight u) has total mass ½.
module QBS.Continuous.UniformMean where

open import Data.Bool.Base using (true; false)
open import Algebra using (CommutativeSemiring)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Classical using (LEM₁)

-- the semiring algebra behind the mean, over an abstract commutative semiring (the solver is slow on
-- the concrete cut semiring)
module Alg {c ℓ} (S : CommutativeSemiring c ℓ) (half : CommutativeSemiring.Carrier S)
    (hh : CommutativeSemiring._≈_ S (CommutativeSemiring._+_ S half half) (CommutativeSemiring.1# S)) where
  open CommutativeSemiring S
  open import Algebra.Solver.Ring.NaturalCoefficients.Default S
  open SetoidReasoning setoid

  -- (½ + ½) ½ = ½ and ½m + ½m = m
  k : (half + half) * half ≈ half
  k = trans (*-cong hh refl) (*-identityˡ half)

  hm : ∀ m → half * m + half * m ≈ m
  hm m = trans (sym (distribʳ m half half)) (trans (*-cong hh refl) (*-identityˡ m))

  -- m = ½(½ + ½m) + ½(½m) gives m + m = ½ + m
  double : ∀ m → m ≈ half * (half + half * m) + half * (half * m) → m + m ≈ half + m
  double m E = begin
    m + m                                                                       ≈⟨ +-cong E E ⟩
    X + X                                                                       ≈⟨ polyEq ⟩
    (half + half) * half + ((half + half) * half * m + (half + half) * half * m)
      ≈⟨ +-cong k (+-cong (*-cong k refl) (*-cong k refl)) ⟩
    half + (half * m + half * m)                                                ≈⟨ +-cong refl (hm m) ⟩
    half + m ∎
    where
      X = half * (half + half * m) + half * (half * m)
      polyEq : X + X ≈ (half + half) * half + ((half + half) * half * m + (half + half) * half * m)
      polyEq = solve 2 (λ h x → let X′ = h :* (h :+ h :* x) :+ h :* (h :* x)
                                in X′ :+ X′ := (h :+ h) :* h :+ ((h :+ h) :* h :* x :+ (h :+ h) :* h :* x)) refl half m

module UniformMean (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open Integration A
  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre; Fun-≤1)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Expansion A half hh
  open ExpansionCons A half hh using (expansion-cons)
  open HalfOrder A R using (half≤1)
  open Indicators A (lemOf lem₁) using (I-const)
  open SetoidReasoning setoid

  ----------------------------------------------------------------------------
  -- the expectation of the binary expansion, by self-similarity (as for the CDF and the second
  -- moment): splitting off the first bit, with e(true :: s) = ½ + ½ e(s) and e(false :: s) = ½ e(s),
  --   M = ½(½ + ½M) + ½(½M),   so   M + M = M + ½   and M = ½ by cancellation (M ≤ 1)

  M : ∣A∣
  M = I fairCoin expansion Fun-expansion

  M≤1 : M ≤ 1#
  M≤1 = ≤-trans (I-mono fairCoin Fun-expansion (Fun-const 1# ≤-refl) (Fun-≤1 Fun-expansion))
                (≤-reflexive (I-const fairCoin L-one 1# ≤-refl))

  private
    Fhe : Fun (λ x → half * expansion x)
    Fhe = Fun-scale half half≤1 Fun-expansion
    ET : Fun (λ x → expansion (consR true x))
    ET = Fun-pre {f = consR true} Fun-expansion (measurable-cons true)
    EF : Fun (λ x → expansion (consR false x))
    EF = Fun-pre {f = consR false} Fun-expansion (measurable-cons false)

  I-true : I fairCoin (λ x → expansion (consR true x)) ET ≈ half + half * M
  I-true = trans (I-add fairCoin ET (Fun-const half half≤1) Fhe (expansion-cons true))
    (+-cong (I-const fairCoin L-one half half≤1) (I-scale fairCoin half Fun-expansion Fhe (λ _ → refl)))

  I-false : I fairCoin (λ x → expansion (consR false x)) EF ≈ half * M
  I-false = I-scale fairCoin half Fun-expansion EF (λ r → trans (expansion-cons false r) (+-identityˡ _))

  E : M ≈ half * (half + half * M) + half * (half * M)
  E = trans (firstBit-fun Fun-expansion) (+-cong (*-cong refl I-true) (*-cong refl I-false))

  -- E[U] = ½
  mean : I fairCoin expansion Fun-expansion ≈ half
  mean = cancel M≤1 (trans (Alg.double commutativeSemiring half hh M E) (+-comm half M))
