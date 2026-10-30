{-# OPTIONS --safe --without-K #-}

-- The second moment of the uniform distribution: with e the binary expansion and m = E[e²],
--   e(true :: s) = ½ + ½ e(s),  e(false :: s) = ½ e(s)
-- and the first-bit decomposition give 4m = 1 + m, hence 3m = 1 (no division needed: the
-- statement is `m + m + m ≈ 1`).
module QBS.Continuous.UniformMoment where

open import Level using (lift; lower)
open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra using (CommutativeSemiring)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Mixture using (module Mixture)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.UniformMean using (module UniformMean)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.HalfOrder using (module HalfOrder)

-- the semiring algebra behind the second moment, over an abstract commutative semiring (the solver
-- is slow on the concrete cut semiring)
module Alg {c ℓ} (S : CommutativeSemiring c ℓ) (half : CommutativeSemiring.Carrier S)
    (hh : CommutativeSemiring._≈_ S (CommutativeSemiring._+_ S half half) (CommutativeSemiring.1# S)) where
  open CommutativeSemiring S
  open import Algebra.Solver.Ring.NaturalCoefficients.Default S
  open SetoidReasoning setoid

  sq-true : ∀ x → (half + half * x) * (half + half * x) ≈ half * half + ((half * half * x + half * half * x) + half * half * (x * x))
  sq-true x = solve 2 (λ h x → (h :+ h :* x) :* (h :+ h :* x) := h :* h :+ ((h :* h :* x :+ h :* h :* x) :+ h :* h :* (x :* x))) refl half x

  sq-false : ∀ x → (half * x) * (half * x) ≈ half * half * (x * x)
  sq-false x = solve 2 (λ h x → (h :* x) :* (h :* x) := h :* h :* (x :* x)) refl half x

  three-pre : ∀ m → m + ((m + m) + m) ≈ (m + m) + (m + m)
  three-pre m = solve 1 (λ x → x :+ ((x :+ x) :+ x) := (x :+ x) :+ (x :+ x)) refl m

  module Eq (m : Carrier)
    (E : m ≈ half * (half * half + ((half * half * half + half * half * half) + half * half * m)) + half * (half * half * m)) where
    o2 : (half + half) * (half + half) ≈ 1#
    o2 = trans (*-cong hh hh) (*-identityˡ 1#)
    o3 : (half + half) * (half + half) * (half + half) ≈ 1#
    o3 = trans (*-cong o2 hh) (*-identityˡ 1#)
    o2h : half * ((half + half) * (half + half)) ≈ half
    o2h = trans (*-cong refl o2) (*-identityʳ half)

    four : (m + m) + (m + m) ≈ 1# + m
    four = begin
      (m + m) + (m + m) ≈⟨ +-cong (+-cong E E) (+-cong E E) ⟩
      (X + X) + (X + X) ≈⟨ polyEq ⟩
      half * ((half + half) * (half + half)) + (half * ((half + half) * (half + half) * (half + half)) + (half + half) * (half + half) * (half + half) * m)
        ≈⟨ +-cong o2h (+-cong (trans (*-cong refl o3) (*-identityʳ half)) (trans (*-cong o3 refl) (*-identityˡ m))) ⟩
      half + (half + m) ≈⟨ sym (+-assoc half half m) ⟩
      (half + half) + m ≈⟨ +-cong hh refl ⟩
      1# + m ∎
      where
        X = half * (half * half + ((half * half * half + half * half * half) + half * half * m)) + half * (half * half * m)
        polyEq : (X + X) + (X + X)
          ≈ half * ((half + half) * (half + half))
            + (half * ((half + half) * (half + half) * (half + half)) + (half + half) * (half + half) * (half + half) * m)
        polyEq = solve 2 (λ h x → let X′ = h :* (h :* h :+ ((h :* h :* h :+ h :* h :* h) :+ h :* h :* x)) :+ h :* (h :* h :* x)
                                  in (X′ :+ X′) :+ (X′ :+ X′)
                                     := h :* ((h :+ h) :* (h :+ h))
                                        :+ (h :* ((h :+ h) :* (h :+ h) :* (h :+ h)) :+ (h :+ h) :* (h :+ h) :* (h :+ h) :* x))
                                refl half m


module UniformMoment (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  open JParam (lemOf lem₁)
  open Meas (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open Integration A
  open Expansion A half hh
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open SetoidReasoning setoid

  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre; sumF; Fun-≤1)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open ExpansionCons A half hh using (expansion-cons)
  open UniformMean lem₁ using (mean)
  open Daniell lem₁ using (L-one)
  open HalfOrder A R using (half≤1)
  open Indicators A (lemOf lem₁) using (I-const)

  e² : R₁ → ∣A∣
  e² r = expansion r * expansion r

  q : ∣A∣
  q = half * half

  Meas-e² : Meas e²
  Meas-e² = Meas-⊗ {expansion} {expansion} (LS Fun-expansion) (LS Fun-expansion)

  Fun-e² : Fun e²
  Fun-e² = Meas→Fun (λ r → ≤-trans (*-mono (expansion r) (expansion≤1 r)) (≤-trans (≤-reflexive (*-identityʳ _)) (expansion≤1 r))) Meas-e²

  q≤1 : q ≤ 1#
  q≤1 = ≤-trans (*-mono half half≤1) (≤-trans (≤-reflexive (*-identityʳ half)) half≤1)

  m : ∣A∣
  m = I fairCoin e² Fun-e²

  m≤1 : m ≤ 1#
  m≤1 = ≤-trans (I-mono fairCoin Fun-e² (Fun-const 1# ≤-refl) (Fun-≤1 Fun-e²))
                (≤-reflexive (I-const fairCoin L-one 1# ≤-refl))

  -- the two branches of e²
  e²-true : ∀ r → e² (consR true r) ≈ q + ((q * expansion r + q * expansion r) + q * e² r)
  e²-true r = trans (*-cong (expansion-cons true r) (expansion-cons true r)) (Alg.sq-true commutativeSemiring half hh (expansion r))

  e²-false : ∀ r → e² (consR false r) ≈ q * e² r
  e²-false r = trans (*-cong (trans (expansion-cons false r) (+-identityˡ _)) (trans (expansion-cons false r) (+-identityˡ _)))
    (Alg.sq-false commutativeSemiring half hh (expansion r))

  private
    Fqe : Fun (λ x → q * expansion x)
    Fqe = Fun-scale q q≤1 Fun-expansion
    Fqe² : Fun (λ x → q * e² x)
    Fqe² = Fun-scale q q≤1 Fun-e²
    FT1 : Fun (λ x → q * expansion x + q * expansion x)
    FT1 = sumF Fqe Fqe (λ _ → refl) (λ x → ≤-trans (+-mono (*-mono q (expansion≤1 x)) (*-mono q (expansion≤1 x)))
      (≤-trans (≤-reflexive (+-cong (*-identityʳ q) (*-identityʳ q)))
        (≤-trans (≤-reflexive (sym (distribʳ half half half))) (≤-trans (≤-reflexive (trans (*-cong hh refl) (*-identityˡ half))) half≤1))))
    ET : Fun (λ x → e² (consR true x))
    ET = Fun-pre {f = consR true} Fun-e² (measurable-cons true)
    bT : ∀ x → ((q * expansion x + q * expansion x) + q * e² x) ≤ 1#
    bT x = ≤-trans {T x} {q + T x} {1#}
      (≤-trans {T x} {T x + q} {q + T x} (≤-+ʳ {T x} {q}) (≤-reflexive (+-comm (T x) q)))
      (≤-trans {q + T x} {e² (consR true x)} {1#} (≤-reflexive (sym (e²-true x))) (Fun-≤1 ET x))
      where T = λ x → (q * expansion x + q * expansion x) + q * e² x
    FT : Fun (λ x → (q * expansion x + q * expansion x) + q * e² x)
    FT = sumF FT1 Fqe² (λ _ → refl) bT

  I-true : I fairCoin (λ x → e² (consR true x)) (Fun-pre {f = consR true} Fun-e² (measurable-cons true))
    ≈ q + ((q * half + q * half) + q * m)
  I-true = trans (I-add fairCoin ET (Fun-const q q≤1) FT e²-true)
    (+-cong (I-const fairCoin L-one q q≤1)
      (trans (I-add fairCoin FT FT1 Fqe² (λ _ → refl))
        (+-cong (trans (I-add fairCoin FT1 Fqe Fqe (λ _ → refl))
                  (+-cong qe qe))
                (I-scale fairCoin q Fun-e² Fqe² (λ _ → refl)))))
    where qe = trans (I-scale fairCoin q Fun-expansion Fqe (λ _ → refl)) (*-cong refl mean)

  I-false : I fairCoin (λ x → e² (consR false x)) (Fun-pre {f = consR false} Fun-e² (measurable-cons false))
    ≈ q * m
  I-false = I-scale fairCoin q Fun-e² (Fun-pre {f = consR false} Fun-e² (measurable-cons false)) e²-false

  E : m ≈ half * (q + ((q * half + q * half) + q * m)) + half * (q * m)
  E = trans (firstBit-fun Fun-e²) (+-cong (*-cong {half} {half} refl I-true) (*-cong {half} {half} refl I-false))

  -- 4m = 1 + m
  moment-eq : (m + m) + (m + m) ≈ 1# + m
  moment-eq = Alg.Eq.four commutativeSemiring half hh m E

  -- E[e²] is a third: 3m = 1 (no division: the statement is m + m + m ≈ 1)
  second-moment : (m + m) + m ≈ 1#
  second-moment = cancel m≤1 (trans (Alg.three-pre commutativeSemiring half hh m) (trans moment-eq (+-comm 1# m)))
