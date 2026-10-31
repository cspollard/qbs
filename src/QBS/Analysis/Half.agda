{-# OPTIONS --safe --without-K #-}

-- Powers of ½ in an `OmegaSemiring` with a half (`half + half ≈ 1`): `hp n = ½ⁿ` is the stdlib power
-- `half ^ n` (so `hp (suc n) = half * hp n` holds by definition), with `½ (x + x) = x`, the doubling
-- law `½ⁿ⁺¹ + ½ⁿ⁺¹ = ½ⁿ`, the geometric partial sums `½ + ¼ + … + ½ᴺ + ½ᴺ = 1`, and uniqueness of any
-- sequence with the same recurrence.  Every other use of ½ⁿ in the library goes through this module.
module QBS.Analysis.Half where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Algebra.Bundles using (CommutativeSemiring)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)

module Half (A : OmegaSemiring (suc zero)) (half : OmegaSemiring.Carrier A)
    (half+half : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Series A
  open SetoidReasoning setoid
  open import Algebra.Properties.Semiring.Exp (CommutativeSemiring.semiring commutativeSemiring) using (_^_)

  -- 1, ½, ¼, …
  hp : ℕ → ∣A∣
  hp n = half ^ n

  hp-zero : hp 0 ≈ 1#
  hp-zero = refl

  -- ½ (x + x) = x
  half-twice : ∀ x → half * (x + x) ≈ x
  half-twice x = begin
    half * (x + x)       ≈⟨ distribˡ half x x ⟩
    half * x + half * x  ≈⟨ sym (distribʳ x half half) ⟩
    (half + half) * x    ≈⟨ *-cong half+half refl ⟩
    1# * x               ≈⟨ *-identityˡ x ⟩
    x ∎

  -- ½ⁿ⁺¹ + ½ⁿ⁺¹ = ½ⁿ
  hp-double : ∀ n → hp (ℕ.suc n) + hp (ℕ.suc n) ≈ hp n
  hp-double n = begin
    half * hp n + half * hp n  ≈⟨ sym (distribʳ (hp n) half half) ⟩
    (half + half) * hp n       ≈⟨ *-cong half+half refl ⟩
    1# * hp n                  ≈⟨ *-identityˡ _ ⟩
    hp n ∎

  -- ½ · ½ⁿ = ½ⁿ⁺¹ is `refl`, and ½ · (½ⁿ⁺¹ + ½ⁿ⁺¹) = ½ⁿ⁺¹ is `half-twice`; hence any sequence
  -- with `h 0 = 1` and `h (n+1) + h (n+1) = h n` is `hp`
  hp-unique : ∀ (h : ℕ → ∣A∣) → h 0 ≈ 1# → (∀ n → h (ℕ.suc n) + h (ℕ.suc n) ≈ h n) → ∀ n → h n ≈ hp n
  hp-unique h h0 hd ℕ.zero = h0
  hp-unique h h0 hd (ℕ.suc n) = begin
    h (ℕ.suc n)                                   ≈⟨ sym (half-twice _) ⟩
    half * (h (ℕ.suc n) + h (ℕ.suc n))            ≈⟨ *-cong refl (hd n) ⟩
    half * h n                                    ≈⟨ *-cong refl (hp-unique h h0 hd n) ⟩
    hp (ℕ.suc n) ∎

  hp-≤ : ∀ n → hp (ℕ.suc n) ≤ hp n
  hp-≤ n = ≤-trans ≤-+ʳ (≤-reflexive (hp-double n))

  -- the geometric partial sums of any halving sequence: h 1 + … + h N + h N = h 0
  geoF : ∀ (h : ℕ → ∣A∣) → (∀ n → h (ℕ.suc n) + h (ℕ.suc n) ≈ h n) →
    ∀ N → psum (λ i → h (ℕ.suc i)) N + h N ≈ h 0
  geoF h hd ℕ.zero = +-identityˡ _
  geoF h hd (ℕ.suc N) = begin
    (psum (λ i → h (ℕ.suc i)) N + h (ℕ.suc N)) + h (ℕ.suc N)
      ≈⟨ +-assoc _ _ _ ⟩
    psum (λ i → h (ℕ.suc i)) N + (h (ℕ.suc N) + h (ℕ.suc N))
      ≈⟨ +-cong refl (hd N) ⟩
    psum (λ i → h (ℕ.suc i)) N + h N
      ≈⟨ geoF h hd N ⟩
    h 0 ∎

  -- ½ + ¼ + … + ½ᴺ + ½ᴺ = 1
  geom : ∀ N → psum (λ i → hp (ℕ.suc i)) N + hp N ≈ 1#
  geom = geoF hp hp-double

  -- the same, started at ½ᵏ
  geo : ∀ k N → psum (λ i → hp (ℕ.suc i ℕ.+ k)) N + hp (N ℕ.+ k) ≈ hp k
  geo k = geoF (λ i → hp (i ℕ.+ k)) (λ n → hp-double (n ℕ.+ k))

  geo-sum : ∀ k → ∑ᶠ (λ i → hp (ℕ.suc i ℕ.+ k)) ≤ hp k
  geo-sum k = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (geo k N)))
