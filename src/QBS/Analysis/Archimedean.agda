{-# OPTIONS --safe --without-K #-}

-- The extra structure of the extended non-negative reals that the construction of Lebesgue-type
-- measures needs, beyond `OmegaSemiring`: a half, Archimedean closure, cancellation for the
-- order, and tails of convergent series.
module QBS.Analysis.Archimedean where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Series

record Arch (A : OmegaSemiring (suc zero)) : Set₁ where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  field
    half : ∣A∣
    half+half : half + half ≈ 1#
    -- a sequence of tolerances 1, ½, ¼, … (any sequence with these properties will do)
    hp : ℕ → ∣A∣
    hp-zero : hp 0 ≈ 1#
    hp-double : ∀ n → hp (ℕ.suc n) + hp (ℕ.suc n) ≈ hp n
    arch : ∀ {x y} → (∀ n → x ≤ y + hp n) → x ≤ y
    cancel≤ : ∀ {a x y} → a ≤ 1# → a + x ≤ a + y → x ≤ y
    -- the tail of a bounded increasing sequence is small
    way-below : ∀ c (inc : Increasing c) → ⨆ c inc ≤ 1# →
      ∀ n → Σ ℕ (λ N → ⨆ c inc ≤ c N + hp n)

module ArchLemmas {A : OmegaSemiring (suc zero)} (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R
  open Series A
  open SetoidReasoning setoid

  hp-≤ : ∀ n → hp (ℕ.suc n) ≤ hp n
  hp-≤ n = ≤-trans ≤-+ʳ (≤-reflexive (hp-double n))

  -- the geometric partial sums: hp (1+k) + … + hp (N+k) + hp (N+k) = hp k
  geo : ∀ k N → psum (λ i → hp (ℕ.suc i ℕ.+ k)) N + hp (N ℕ.+ k) ≈ hp k
  geo k ℕ.zero = +-identityˡ _
  geo k (ℕ.suc N) = begin
    (psum (λ i → hp (ℕ.suc i ℕ.+ k)) N + hp (ℕ.suc N ℕ.+ k)) + hp (ℕ.suc N ℕ.+ k)
      ≈⟨ +-assoc _ _ _ ⟩
    psum (λ i → hp (ℕ.suc i ℕ.+ k)) N + (hp (ℕ.suc N ℕ.+ k) + hp (ℕ.suc N ℕ.+ k))
      ≈⟨ +-cong refl (hp-double (N ℕ.+ k)) ⟩
    psum (λ i → hp (ℕ.suc i ℕ.+ k)) N + hp (N ℕ.+ k)
      ≈⟨ geo k N ⟩
    hp k ∎

  geo-sum : ∀ k → ∑ᶠ (λ i → hp (ℕ.suc i ℕ.+ k)) ≤ hp k
  geo-sum k = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (geo k N)))
