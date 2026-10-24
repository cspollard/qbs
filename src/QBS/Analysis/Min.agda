{-# OPTIONS --safe --without-K #-}

-- A binary minimum on the values of an `OmegaSemiring`, with exactly the properties that the
-- dyadic truncations `min (a, 2ᵏ) / 2ᵏ` of `Analysis/Unbounded` need: greatest lower bound,
-- continuity along increasing suprema, subadditivity `min (a + b, c) ≤ min (a, c) + min (b, c)`, and
-- `a = ⨆ₖ min (a, 2ᵏ)`.
-- The intended instance is intersection of lower cuts (`Analysis/LowerRealsMin`).
module QBS.Analysis.Min where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ

open import QBS.Analysis.Omega

-- the powers of two 1, 2, 4, …
module Pow (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)

  pw : ℕ → ∣A∣
  pw ℕ.zero = 1#
  pw (ℕ.suc k) = pw k + pw k

record Min (A : OmegaSemiring (suc zero)) : Set₁ where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Pow A
  field
    mn : ∣A∣ → ∣A∣ → ∣A∣
    mn-≤l : ∀ {a b} → mn a b ≤ a
    mn-≤r : ∀ {a b} → mn a b ≤ b
    mn-glb : ∀ {a b c} → c ≤ a → c ≤ b → c ≤ mn a b
    mn-⨆ : ∀ c (inc : Increasing c) b (inc′ : Increasing (λ n → mn (c n) b)) →
      mn (⨆ c inc) b ≤ ⨆ (λ n → mn (c n) b) inc′
    mn-add : ∀ {a b c} → mn (a + b) c ≤ mn a c + mn b c
    mn-sup : ∀ a (inc : Increasing (λ k → mn a (pw k))) → a ≤ ⨆ (λ k → mn a (pw k)) inc
