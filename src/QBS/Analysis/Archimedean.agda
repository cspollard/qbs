{-# OPTIONS --safe --without-K #-}

-- The extra structure of the extended non-negative reals that the construction of Lebesgue-type
-- measures needs, beyond `OmegaSemiring`: a half, Archimedean closure, cancellation for the
-- order, and tails of convergent series.
module QBS.Analysis.Archimedean where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)

open import QBS.Analysis.Omega
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.Series using (module Series)

record Arch (A : OmegaSemiring (suc zero)) : Set₁ where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  field
    half : ∣A∣
    half+half : half + half ≈ 1#
  -- the tolerances 1, ½, ¼, … (see `Analysis/Half`)
  open Half A half half+half public
  field
    arch : ∀ {x y} → (∀ n → x ≤ y + hp n) → x ≤ y
    cancel≤ : ∀ {a x y} → a ≤ 1# → a + x ≤ a + y → x ≤ y
    -- the tail of a bounded increasing sequence is small
    way-below : ∀ c (inc : Increasing c) → ⨆ c inc ≤ 1# →
      ∀ n → Σ ℕ (λ N → ⨆ c inc ≤ c N + hp n)

  -- the geometric series ∑ ½ⁿ⁺¹ = 1 (the partial sums are bounded by `geom`, and `arch` closes the gap)
  open Series A using (psum; ∑ᶠ; ∑ᶠ-lub; psum≤∑ᶠ)

  ∑hp≤1 : ∑ᶠ (λ n → hp (ℕ.suc n)) ≤ 1#
  ∑hp≤1 = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (geom N)))

  ∑hp≈1 : ∑ᶠ (λ n → hp (ℕ.suc n)) ≈ 1#
  ∑hp≈1 = ≤-antisym ∑hp≤1 (arch (λ n →
    ≤-trans (≤-reflexive (sym (geom n))) (+-mono (psum≤∑ᶠ (λ i → hp (ℕ.suc i)) n) ≤-refl)))
