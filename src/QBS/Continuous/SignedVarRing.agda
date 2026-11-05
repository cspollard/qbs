{-# OPTIONS --safe --without-K #-}

-- Ring identities on parts of signed values over an abstract commutative semiring (plan 03, "Information quantities";
-- helper for `SignedVarAlg`).
--   * pairs `Pa` of elements (x⁺, x⁻) with the operations `_⊕ᵃ_`, `_⊗ᵃ_`, `ngᵃ` of signed sums, products and negation,
--     and the cross-added / part-summed equations `crossᵃ`, `sumsᵃ`;
--   * the identities behind `(f − c)² ≐ f² − 2c f + c²`, `(c f)² ≐ c² f²` and the variance laws (`cen-alg`, `cen-sums`,
--     `scl-alg`, `scl-sums`, `R1-alg`, `RS-alg`, `SQ-alg`) and the sign rules `neg-mul-alg`, `mul-neg-alg`.
-- Route: each identity is one `solve` of the natural-coefficient ring solver; stated over an abstract semiring, so that
-- the solver normalises small terms (instantiating at the concrete semiring afterwards is cheap).
module QBS.Continuous.SignedVarRing where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Algebra using (CommutativeSemiring)

module Ring {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (_≈_; _+_; _*_; 0#; 1#; refl) renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R

  -- parts as pairs of polynomials
  Pr : ℕ → Set
  Pr n = Polynomial n × Polynomial n

  infixl 6 _⊕_
  infixl 7 _⊗_
  _⊕_ _⊗_ : ∀ {n} → Pr n → Pr n → Pr n
  (x , y) ⊕ (z , w) = x :+ z , y :+ w
  (x , y) ⊗ (z , w) = x :* z :+ y :* w , x :* w :+ y :* z

  ng : ∀ {n} → Pr n → Pr n
  ng (x , y) = y , x

  -- cross-added and part-summed equations
  cross sums : ∀ {n} → Pr n → Pr n → Pr n
  cross (x , y) (z , w) = (x :+ w) := (z :+ y)
  sums (x , y) (z , w) = (x :+ y) := (z :+ w)

  -- the same operations on pairs of elements
  Pa : Set c
  Pa = ∣A∣ × ∣A∣

  infixl 6 _⊕ᵃ_
  infixl 7 _⊗ᵃ_
  _⊕ᵃ_ _⊗ᵃ_ : Pa → Pa → Pa
  (x , y) ⊕ᵃ (z , w) = x + z , y + w
  (x , y) ⊗ᵃ (z , w) = x * z + y * w , x * w + y * z

  ngᵃ : Pa → Pa
  ngᵃ (x , y) = y , x

  crossᵃ sumsᵃ : Pa → Pa → Set ℓ
  crossᵃ (x , y) (z , w) = x + w ≈ z + y
  sumsᵃ (x , y) (z , w) = x + y ≈ z + w

  -- the pairs of `(f − c)²`, of `Sq f c`, of `(c f)²` and of `c² f²`
  cenA sqA sclA sclA′ : Pa → Pa → Pa
  cenA f c = (f ⊕ᵃ ngᵃ c) ⊗ᵃ (f ⊕ᵃ ngᵃ c)
  sqA f c = ((f ⊗ᵃ f) ⊕ᵃ (ngᵃ (c ⊕ᵃ c) ⊗ᵃ f)) ⊕ᵃ (c ⊗ᵃ c)
  sclA f c = (c ⊗ᵃ f) ⊗ᵃ (c ⊗ᵃ f)
  sclA′ f c = (c ⊗ᵃ c) ⊗ᵃ (f ⊗ᵃ f)

  -- the polynomials of `(f − c)²`, of `Sq f c`, of `(c f)²` and of `c² f²`
  cenP sqP sclP sclP′ : ∀ {n} → Pr n → Pr n → Pr n
  cenP f c = (f ⊕ ng c) ⊗ (f ⊕ ng c)
  sqP f c = ((f ⊗ f) ⊕ (ng (c ⊕ c) ⊗ f)) ⊕ (c ⊗ c)
  sclP f c = (c ⊗ f) ⊗ (c ⊗ f)
  sclP′ f c = (c ⊗ c) ⊗ (f ⊗ f)

  cen-alg : ∀ a b p n → crossᵃ (cenA (a , b) (p , n)) (sqA (a , b) (p , n))
  cen-alg a b p n = solve 4 (λ a b p n → cross (cenP (a , b) (p , n)) (sqP (a , b) (p , n))) refl a b p n

  cen-sums : ∀ a b p n → sumsᵃ (cenA (a , b) (p , n)) (sqA (a , b) (p , n))
  cen-sums a b p n = solve 4 (λ a b p n → sums (cenP (a , b) (p , n)) (sqP (a , b) (p , n))) refl a b p n

  scl-alg : ∀ a b p n → crossᵃ (sclA (a , b) (p , n)) (sclA′ (a , b) (p , n))
  scl-alg a b p n = solve 4 (λ a b p n → cross (sclP (a , b) (p , n)) (sclP′ (a , b) (p , n))) refl a b p n

  scl-sums : ∀ a b p n → sumsᵃ (sclA (a , b) (p , n)) (sclA′ (a , b) (p , n))
  scl-sums a b p n = solve 4 (λ a b p n → sums (sclP (a , b) (p , n)) (sclP′ (a , b) (p , n))) refl a b p n

  -- ring identities for `Var-cen` (c = E f), `Var-shift`, `Var-scale`
  L1 LS : ∀ {n} → Pr n → Pr n → Pr n
  L1 m1 m2 = ((m2 ⊕ ng ((m1 ⊕ m1) ⊗ m1)) ⊕ (m1 ⊗ m1))
  LS m c = ((ng ((ng c ⊕ ng c) ⊗ m) ⊕ (ng c ⊗ ng c)) ⊕ ng ((m ⊕ c) ⊗ (m ⊕ c)))
  RV SQ SQ′ : ∀ {n} → Pr n → Pr n → Pr n
  RV m1 m2 = (m2 ⊕ ng (m1 ⊗ m1))
  SQ m c = ((c ⊗ m) ⊗ (c ⊗ m))
  SQ′ m c = ((c ⊗ c) ⊗ (m ⊗ m))

  L1ᵃ LSᵃ RVᵃ SQᵃ SQ′ᵃ : Pa → Pa → Pa
  L1ᵃ m1 m2 = ((m2 ⊕ᵃ ngᵃ ((m1 ⊕ᵃ m1) ⊗ᵃ m1)) ⊕ᵃ (m1 ⊗ᵃ m1))
  LSᵃ m c = (ngᵃ ((ngᵃ c ⊕ᵃ ngᵃ c) ⊗ᵃ m) ⊕ᵃ (ngᵃ c ⊗ᵃ ngᵃ c)) ⊕ᵃ ngᵃ ((m ⊕ᵃ c) ⊗ᵃ (m ⊕ᵃ c))
  RVᵃ m1 m2 = (m2 ⊕ᵃ ngᵃ (m1 ⊗ᵃ m1))
  SQᵃ m c = ((c ⊗ᵃ m) ⊗ᵃ (c ⊗ᵃ m))
  SQ′ᵃ m c = ((c ⊗ᵃ c) ⊗ᵃ (m ⊗ᵃ m))

  R1-alg : ∀ a b c d → crossᵃ (L1ᵃ (a , b) (c , d)) (RVᵃ (a , b) (c , d))
  R1-alg a b c d = solve 4 (λ a b c d → cross (L1 (a , b) (c , d)) (RV (a , b) (c , d))) refl a b c d

  RS-alg : ∀ a b p n → crossᵃ (LSᵃ (a , b) (p , n)) (ngᵃ ((a , b) ⊗ᵃ (a , b)))
  RS-alg a b p n = solve 4 (λ a b p n → cross (LS (a , b) (p , n)) (ng ((a , b) ⊗ (a , b)))) refl a b p n

  SQ-alg : ∀ a b p n → crossᵃ (SQᵃ (a , b) (p , n)) (SQ′ᵃ (a , b) (p , n))
  SQ-alg a b p n = solve 4 (λ a b p n → cross (SQ (a , b) (p , n)) (SQ′ (a , b) (p , n))) refl a b p n

  neg-mul-alg : ∀ a b c d → crossᵃ (ngᵃ (a , b) ⊗ᵃ (c , d)) (ngᵃ ((a , b) ⊗ᵃ (c , d)))
  neg-mul-alg a b c d = solve 4 (λ a b c d → cross (ng (a , b) ⊗ (c , d)) (ng ((a , b) ⊗ (c , d)))) refl a b c d

  mul-neg-alg : ∀ a b c d → crossᵃ ((a , b) ⊗ᵃ ngᵃ (c , d)) (ngᵃ ((a , b) ⊗ᵃ (c , d)))
  mul-neg-alg a b c d = solve 4 (λ a b c d → cross ((a , b) ⊗ ng (c , d)) (ng ((a , b) ⊗ (c , d)))) refl a b c d
