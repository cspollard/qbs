{-# OPTIONS --safe --without-K #-}

-- Polynomial domination of every degree under the half-normal (extends `Inference/PolyDomination`, which has even degree only).
-- By the split `x ≤ 1` or `1 ≤ x` (`Analysis/CutSplit.split1`), `xᵏ ≤ 1 + x^{2k}` pointwise (`pw≤1+sq`), hence
-- `1 + xᵏ ≤ 2 (1 + x^{2k})` and a growth bound `g ≤ c (1 + xᵏ)` becomes `g ≤ 2c (1 + x^{ev k})`.
--   * `hnIk g⁺ g⁻ k c cB dom⁺ dom⁻ : ITest halfNormal` for `g± x ≤ c · (1 + xᵏ)` with `k` arbitrary and `c` finite;
--   * validation: `xI : ITest halfNormal` for the first moment `x ↦ x` (degree 1, odd).
-- The value `E[X] = n` (that is, `∫₀^∞ x e^{−x²/2} = 1`) is in `Inference/HalfNormalMean`.
module QBS.Inference.PolyDominationOdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Level as L

open import QBS.Core
open import QBS.Continuous.Sample using (S)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.CutSplit using (split1)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.GaussInverse using (module GaussInverse)
open import QBS.Inference.PolyDomination using (module PolyDomination)
open import QBS.Inference.HalfNormal using (module HalfNormal)
open import QBS.Inference.ExpectationInt using (module ExpectationInt)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import Function.Bundles using (_⟨$⟩_)

-- the algebra, over an abstract ω-semiring with a splitting at 1
module AlgO (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgP A R using (pw; *-mono₂)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  sq-step : ∀ x p → x * (x * (p * p)) ≈ (x * p) * (x * p)
  sq-step x p = solve 2 (λ x′ p′ → x′ :* (x′ :* (p′ :* p′)) := (x′ :* p′) :* (x′ :* p′)) refl x p

  pw≤1 : ∀ {x} → x ≤ 1# → ∀ i → pw i x ≤ 1#
  pw≤1 x1 zero = ≤-refl
  pw≤1 x1 (suc i) = ≤-trans (*-mono₂ x1 (pw≤1 x1 i)) (≤-reflexive (*-identityˡ _))

  pw≥1 : ∀ {x} → 1# ≤ x → ∀ i → 1# ≤ pw i x
  pw≥1 x1 zero = ≤-refl
  pw≥1 x1 (suc i) = ≤-trans (≤-reflexive (sym (*-identityˡ _))) (*-mono₂ x1 (pw≥1 x1 i))

  -- `p ≤ 1 + p²` when `p ≤ 1` or `1 ≤ p`
  cases : ∀ {p} → p ≤ 1# ⊎ 1# ≤ p → p ≤ 1# + p * p
  cases (inj₁ lo) = ≤-trans lo ≤-+ʳ
  cases {p} (inj₂ hi) = ≤-trans (≤-reflexive (sym (*-identityˡ p))) (≤-trans (*-mono₂ hi ≤-refl)
    (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ 1#))))

  -- `p ≤ 1 + s` and `g ≤ c (1 + p)` give `g ≤ (c · 2)(1 + s)`
  dom-alg : ∀ {g c p s} → p ≤ 1# + s → g ≤ c * (1# + p) → g ≤ (c * (1# + 1#)) * (1# + s)
  dom-alg {g} {c} {p} {s} ps gd = ≤-trans gd (≤-trans (*-mono c (≤-trans (+-mono ≤-refl ps) (step s)))
    (≤-reflexive (sym (*-assoc c (1# + 1#) (1# + s)))))
    where
    alg : ∀ s → (1# + 1#) * (1# + s) ≈ (1# + (1# + s)) + s
    alg = solve 1 (λ s′ → (con 1 :+ con 1) :* (con 1 :+ s′) := (con 1 :+ (con 1 :+ s′)) :+ s′) refl
    step : ∀ s → 1# + (1# + s) ≤ (1# + 1#) * (1# + s)
    step s = ≤-trans ≤-+ʳ (≤-reflexive (sym (alg s)))

module PolyDominationOdd (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≤_; _≈_; 0#; 1#; _+_; _*_; refl; sym; trans; *-cong; *-identityˡ; ≤-reflexive; 0-least; *-identityʳ)
  open AlgP A R using (pw)
  open AlgO A R using (sq-step; pw≤1; pw≥1; cases; dom-alg)
  open Bounded A using (Bnd; finite)
  open SubSemiring using (Is-1; Is-+; Is-*)
  open Weights (lemOf lem₁) using (WQ; constW)
  open ExpDist lem₁ using (idW)
  open GaussMoment lem₁ using (ev)
  open GaussInverse lem₁ using (Z-inv)
  open PolyDomination lem₁ using (module HNZ; ≤-1+)
  open HalfNormal lem₁ using (module WithInverse)
  open WithInverse (proj₁ Z-inv) (proj₂ Z-inv) using (halfNormal)
  open ExpectationInt lem₁ using (ITest)
  open Hom

  -- `x^{2k} = xᵏ · xᵏ`
  ev-sq : ∀ k x → pw (ev k) x ≈ pw k x * pw k x
  ev-sq zero x = sym (*-identityˡ _)
  ev-sq (suc k) x = trans (*-cong refl (*-cong refl (ev-sq k x))) (sq-step x (pw k x))

  -- `xᵏ ≤ 1 + x^{2k}` on `WQ`
  pw≤1+ev : ∀ k x → pw k x ≤ 1# + pw (ev k) x
  pw≤1+ev k x = OmegaSemiring.≤-trans A (cases (cs (split1 (lemOf lem₁) x)))
    (OmegaSemiring.+-mono A (OmegaSemiring.≤-refl A) (≤-reflexive (OmegaSemiring.sym A (ev-sq k x))))
    where
    cs : x ≤ 1# ⊎ 1# ≤ x → pw k x ≤ 1# ⊎ 1# ≤ pw k x
    cs (inj₁ lo) = inj₁ (pw≤1 lo k)
    cs (inj₂ hi) = inj₂ (pw≥1 hi k)

  hnIk : ∀ (g⁺ g⁻ : Hom S WQ WQ) k c → Bnd c →
    (∀ x → map g⁺ ⟨$⟩ x ≤ c * (1# + pw k x)) → (∀ x → map g⁻ ⟨$⟩ x ≤ c * (1# + pw k x)) → ITest halfNormal
  hnIk g⁺ g⁻ k c cB dom⁺ dom⁻ = HNZ.hnI g⁺ g⁻ k (c * (1# + 1#)) (Is-* finite cB (Is-+ finite (Is-1 finite) (Is-1 finite)))
    (λ x → dom-alg (pw≤1+ev k x) (dom⁺ x)) (λ x → dom-alg (pw≤1+ev k x) (dom⁻ x))

  -- validation: the first moment `x ↦ x`
  xI : ITest halfNormal
  xI = hnIk idW (constW 0#) 1 1# (Is-1 finite)
    (λ x → ≤-1+ (≤-reflexive (OmegaSemiring.sym A (*-identityʳ x)))) (λ x → 0-least)
