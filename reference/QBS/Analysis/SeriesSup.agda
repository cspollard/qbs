{-# OPTIONS --safe --without-K #-}

-- Countable sums commute with suprema of increasing sequences (monotone convergence for series).
module QBS.Analysis.SeriesSup where

import Level as L
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Series

module SeriesSup {ℓ} (A : OmegaSemiring ℓ) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Series A
  open SetoidReasoning setoid

  -- the supremum of a doubly increasing array in either order
  ⨆⨆-swap′ : ∀ (d : ℕ → ℕ → ∣A∣) (iN : ∀ n → Increasing (λ N → d N n)) (iM : ∀ N → Increasing (d N)) →
    ⨆ (λ N → ⨆ (d N) (iM N)) (λ N → ⨆-mono (iM N) (iM (ℕ.suc N)) (λ n → iN n N))
      ≈ ⨆ (λ n → ⨆ (λ N → d N n) (iN n)) (λ n → ⨆-mono (iN n) (iN (ℕ.suc n)) (λ N → iM N n))
  ⨆⨆-swap′ d iN iM = ≤-antisym
    (⨆-lub _ _ (λ N → ⨆-lub _ (iM N) (λ n →
       ≤-trans (⨆-ub _ (iN n) N) (⨆-ub _ (λ m → ⨆-mono (iN m) (iN (ℕ.suc m)) (λ N′ → iM N′ m)) n))))
    (⨆-lub _ _ (λ n → ⨆-lub _ (iN n) (λ N →
       ≤-trans (⨆-ub _ (iM N) n) (⨆-ub _ (λ N′ → ⨆-mono (iM N′) (iM (ℕ.suc N′)) (λ m → iN m N′)) N))))

  -- finite sums commute with suprema
  psum-⨆′ : ∀ (c : ℕ → ℕ → ∣A∣) (inc : ∀ a → Increasing (c a)) N →
    psum (λ a → ⨆ (c a) (inc a)) N ≈ ⨆ (λ n → psum (λ a → c a n) N) (λ n → psum-mono (λ a → inc a n) N)
  psum-⨆′ c inc ℕ.zero = sym (⨆-const 0# (λ n → ≤-refl))
  psum-⨆′ c inc (ℕ.suc N) = begin
    psum (λ a → ⨆ (c a) (inc a)) N + ⨆ (c N) (inc N)
      ≈⟨ +-cong (psum-⨆′ c inc N) refl ⟩
    ⨆ (λ n → psum (λ a → c a n) N) (λ n → psum-mono (λ a → inc a n) N) + ⨆ (c N) (inc N)
      ≈⟨ ⨆-+-diag (λ n → psum-mono (λ a → inc a n) N) (inc N) incS ⟩
    ⨆ (λ n → psum (λ a → c a n) N + c N n) incS
      ≈⟨ ⨆-cong incS (λ n → psum-mono (λ a → inc a n) (ℕ.suc N)) (λ n → refl) ⟩
    ⨆ (λ n → psum (λ a → c a n) (ℕ.suc N)) (λ n → psum-mono (λ a → inc a n) (ℕ.suc N)) ∎
    where
      incS : Increasing (λ n → psum (λ a → c a n) N + c N n)
      incS n = +-mono (psum-mono (λ a → inc a n) N) (inc N n)

  ∑ᶠ-⨆ : ∀ (c : ℕ → ℕ → ∣A∣) (inc : ∀ a → Increasing (c a)) →
    ∑ᶠ (λ a → ⨆ (c a) (inc a)) ≈ ⨆ (λ n → ∑ᶠ (λ a → c a n)) (λ n → ∑ᶠ-mono (λ a → inc a n))
  ∑ᶠ-⨆ c inc = begin
    ∑ᶠ (λ a → ⨆ (c a) (inc a))
      ≈⟨ ⨆-cong (psum-inc _) (λ N → ⨆-mono (iM N) (iM (ℕ.suc N)) (λ n → iN n N)) (psum-⨆′ c inc) ⟩
    ⨆ (λ N → ⨆ (d N) (iM N)) _
      ≈⟨ ⨆⨆-swap′ d iN iM ⟩
    ⨆ (λ n → ⨆ (λ N → d N n) (iN n)) _
      ≈⟨ ⨆-cong _ (λ n → ∑ᶠ-mono (λ a → inc a n)) (λ n → refl) ⟩
    ⨆ (λ n → ∑ᶠ (λ a → c a n)) (λ n → ∑ᶠ-mono (λ a → inc a n)) ∎
    where
      d : ℕ → ℕ → ∣A∣
      d N n = psum (λ a → c a n) N
      iM : ∀ N → Increasing (d N)
      iM N n = psum-mono (λ a → inc a n) N
      iN : ∀ n → Increasing (λ N → d N n)
      iN n N = psum-inc (λ a → c a n) N
