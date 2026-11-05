{-# OPTIONS --safe --without-K #-}

-- Ring identities on parts of signed values for random vectors (plan 05, item 52; helper for `RandomVectorAlg`).
--   * `comm-cross`, `comm-sums`: the product of signed values commutes, on the parts;
--   * `sc-cross`: (c f)(d g) = (c d)(f g) on the parts;
--   * `sh-cross`: (f + c)(g + d) = (f g + d f) + (c g + c d) on the parts.
-- Route: one `solve` of the natural-coefficient ring solver each, over an abstract commutative semiring.
module QBS.Continuous.RandomVectorRing where

open import Algebra using (CommutativeSemiring)
open import Data.Product.Base using (_,_)
open import QBS.Continuous.SignedVarRing using (module Ring)

module RVRing {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (refl)
  open Ring R using (Pr; _⊕_; _⊗_; cross; sums; Pa; _⊕ᵃ_; _⊗ᵃ_; crossᵃ; sumsᵃ)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R

  comm-cross : ∀ a b c d → crossᵃ ((a , b) ⊗ᵃ (c , d)) ((c , d) ⊗ᵃ (a , b))
  comm-cross a b c d = solve 4 (λ a b c d → cross ((a , b) ⊗ (c , d)) ((c , d) ⊗ (a , b))) refl a b c d

  comm-sums : ∀ a b c d → sumsᵃ ((a , b) ⊗ᵃ (c , d)) ((c , d) ⊗ᵃ (a , b))
  comm-sums a b c d = solve 4 (λ a b c d → sums ((a , b) ⊗ (c , d)) ((c , d) ⊗ (a , b))) refl a b c d

  -- (c f)(d g) and (c d)(f g)
  SC SC′ : ∀ {n} → Pr n → Pr n → Pr n → Pr n → Pr n
  SC c f d g = (c ⊗ f) ⊗ (d ⊗ g)
  SC′ c f d g = (c ⊗ d) ⊗ (f ⊗ g)

  SCᵃ SC′ᵃ : Pa → Pa → Pa → Pa → Pa
  SCᵃ c f d g = (c ⊗ᵃ f) ⊗ᵃ (d ⊗ᵃ g)
  SC′ᵃ c f d g = (c ⊗ᵃ d) ⊗ᵃ (f ⊗ᵃ g)

  sc-cross : ∀ p q a b r s u v → crossᵃ (SCᵃ (p , q) (a , b) (r , s) (u , v)) (SC′ᵃ (p , q) (a , b) (r , s) (u , v))
  sc-cross p q a b r s u v = solve 8
    (λ p q a b r s u v → cross (SC (p , q) (a , b) (r , s) (u , v)) (SC′ (p , q) (a , b) (r , s) (u , v)))
    refl p q a b r s u v

  -- (f + c)(g + d) and (f g + d f) + (c g + c d)
  SH SH′ : ∀ {n} → Pr n → Pr n → Pr n → Pr n → Pr n
  SH f c g d = (f ⊕ c) ⊗ (g ⊕ d)
  SH′ f c g d = ((f ⊗ g) ⊕ (d ⊗ f)) ⊕ ((c ⊗ g) ⊕ (c ⊗ d))

  SHᵃ SH′ᵃ : Pa → Pa → Pa → Pa → Pa
  SHᵃ f c g d = (f ⊕ᵃ c) ⊗ᵃ (g ⊕ᵃ d)
  SH′ᵃ f c g d = ((f ⊗ᵃ g) ⊕ᵃ (d ⊗ᵃ f)) ⊕ᵃ ((c ⊗ᵃ g) ⊕ᵃ (c ⊗ᵃ d))

  sh-cross : ∀ a b p q u v r s → crossᵃ (SHᵃ (a , b) (p , q) (u , v) (r , s)) (SH′ᵃ (a , b) (p , q) (u , v) (r , s))
  sh-cross a b p q u v r s = solve 8
    (λ a b p q u v r s → cross (SH (a , b) (p , q) (u , v) (r , s)) (SH′ (a , b) (p , q) (u , v) (r , s)))
    refl a b p q u v r s
