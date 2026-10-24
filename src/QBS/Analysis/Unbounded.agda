{-# OPTIONS --safe --without-K #-}

-- SKELETON (unsolved holes). Integration of unbounded measurable functions `R → [0,∞]`, the crux
-- of the s-finite measure monad: well-definedness of `join` on `M (M X)` and normalisation of
-- sub-probability measures both integrate functions that are not bounded by 1.  The plan: extend a
-- Daniell functional by truncation, `Iinf m h = ⨆ₙ I m (min (h, n)) / n`-style, and prove monotone
-- convergence, additivity and that it agrees with `I` on `Fun`.
module QBS.Analysis.Unbounded where

open import Level using (zero; suc)
open import Function.Base using (const)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure

module Unbounded (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  private R = R₁

  -- measurable functions into [0,∞]: suprema of increasing sequences of bounded ones
  data FunInf : (R → ∣A∣) → Set₁ where
    bounded : ∀ {h} → Fun h → FunInf h
    -- (to be settled: scaling by naturals / sums of bounded pieces, so that FunInf is closed under +)

  -- the extended integral
  Iinf : Measure → ∀ h → FunInf h → ∣A∣
  Iinf m h f = ?

  -- it extends the bounded integral
  Iinf-bounded : ∀ (m : Measure) {h} (f : Fun h) → Iinf m h (bounded f) ≈ I m h f
  Iinf-bounded m f = ?

  Iinf-mono : ∀ (m : Measure) {h h′} (f : FunInf h) (f′ : FunInf h′) → (∀ x → h x ≤ h′ x) →
    Iinf m h f ≤ Iinf m h′ f′
  Iinf-mono m f f′ le = ?

  Iinf-add : ∀ (m : Measure) {h h₁ h₂} (f : FunInf h) (f₁ : FunInf h₁) (f₂ : FunInf h₂) →
    (∀ x → h x ≈ h₁ x + h₂ x) → Iinf m h f ≈ Iinf m h₁ f₁ + Iinf m h₂ f₂
  Iinf-add m f f₁ f₂ e = ?

  -- monotone convergence
  Iinf-sup : ∀ (m : Measure) {h} (hs : ℕ → R → ∣A∣) (fs : ∀ n → FunInf (hs n))
    (inc : ∀ x → Increasing (λ n → hs n x)) (f : FunInf h) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
    Iinf m h f ≈ ⨆ (λ n → Iinf m (hs n) (fs n)) (λ n → Iinf-mono m (fs n) (fs (ℕ.suc n)) (λ x → inc x n))
  Iinf-sup m hs fs inc f e = ?
