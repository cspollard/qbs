{-# OPTIONS --safe --without-K #-}

-- Pointwise and ring identities for the variance of signed tests (plan 03, "Information quantities"; helper for
-- `SignedVar`).
--   * the expansion `Sq f c = f² − 2c f + c²` of `(f − c)²` as a signed test, with `cen-eq` ((f − c)² ≐ Sq f c) and
--     `cen-bnd` (the sums of the two parts agree pointwise), likewise `scl-eq`, `scl-bnd` for (c f)² and c² f²;
--   * `Int-via`: integrability of F from that of S when F⁺ + F⁻ ≈ S⁺ + S⁻ pointwise (by `Int-dom`);
--   * the three identities in the signed ring `R-cen`, `R-shift`, `R-scale` behind `Var-cen`, `Var-shift`, `Var-scale`.
-- Route: parts of signed sums and products are polynomials in the parts (`_⊕_`, `_⊗_`, `ng` mirror `_+S_`, `_*S_`, `-S_`),
-- so every identity is one `solve` of the natural-coefficient ring solver (cross-added form, witness 0).
module QBS.Continuous.SignedVarAlg where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedVarAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; 1#; +-identityʳ; refl; trans; sym; ≤-reflexive; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; _*S_; -S_; 1S; mk≃; finite; ≃-refl; ≃-sym; ≃-trans;
    +S-cong; -S-cong; *S-congˡ; +S-assoc;
    *S-distribˡ; *S-distribʳ; *S-identityˡ)
  open Sg
  open SubSemiring finite using (Is-+; Is-0)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SFinite (lemOf lem₁) using (XW; module C)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Int-dom; bnd≈; ∫+)
  open QBS
  open Hom
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- (f − c)² expanded: f² − 2c f + c²
  cen : ∀ {X : QBS S} → SgT X → Sg → SgT X
  cen f c = f +T constT (-S c)

  Sq : ∀ {X : QBS S} → SgT X → Sg → SgT X
  Sq f c = (f *T f +T scaleT (-S (c +S c)) f) +T constT (c *S c)

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

  one two : ∀ {n} → Pr n
  one = con 1 , con 0
  two = one ⊕ one

  -- cross-added and part-summed equations
  cross sums : ∀ {n} → Pr n → Pr n → Pr n
  cross (x , y) (z , w) = (x :+ w) := (z :+ y)
  sums (x , y) (z , w) = (x :+ y) := (z :+ w)

  crossS : ∀ {n} → Pr n → Pr n → Pr n
  crossS (x , y) (z , w) = ((x :+ w) :+ con 0) := ((z :+ y) :+ con 0)

  -- the polynomials of `(f − c)²`, of `Sq f c`, of `(c f)²` and of `c² f²`
  cenP sqP sclP sclP′ : ∀ {n} → Pr n → Pr n → Pr n
  cenP f c = (f ⊕ ng c) ⊗ (f ⊕ ng c)
  sqP f c = ((f ⊗ f) ⊕ (ng (c ⊕ c) ⊗ f)) ⊕ (c ⊗ c)
  sclP f c = (c ⊗ f) ⊗ (c ⊗ f)
  sclP′ f c = (c ⊗ c) ⊗ (f ⊗ f)

  -- the same operations on pairs of elements, so that the lemmas are stated (and checked) before unfolding the tests
  Pa : Set₁
  Pa = ∣A∣ × ∣A∣

  infixl 6 _⊕ᵃ_
  infixl 7 _⊗ᵃ_
  _⊕ᵃ_ _⊗ᵃ_ : Pa → Pa → Pa
  (x , y) ⊕ᵃ (z , w) = x + z , y + w
  (x , y) ⊗ᵃ (z , w) = x * z + y * w , x * w + y * z

  ngᵃ : Pa → Pa
  ngᵃ (x , y) = y , x

  twoᵃ : Pa
  twoᵃ = (1# , 0#) ⊕ᵃ (1# , 0#)

  crossᵃ sumsᵃ crossSᵃ : Pa → Pa → Set₁
  crossᵃ (x , y) (z , w) = x + w ≈ z + y
  sumsᵃ (x , y) (z , w) = x + y ≈ z + w
  crossSᵃ (x , y) (z , w) = (x + w) + 0# ≈ (z + y) + 0#

  cenA sqA sclA sclA′ : Pa → Pa → Pa
  cenA f c = (f ⊕ᵃ ngᵃ c) ⊗ᵃ (f ⊕ᵃ ngᵃ c)
  sqA f c = ((f ⊗ᵃ f) ⊕ᵃ (ngᵃ (c ⊕ᵃ c) ⊗ᵃ f)) ⊕ᵃ (c ⊗ᵃ c)
  sclA f c = (c ⊗ᵃ f) ⊗ᵃ (c ⊗ᵃ f)
  sclA′ f c = (c ⊗ᵃ c) ⊗ᵃ (f ⊗ᵃ f)

  cen-alg : ∀ a b p n → crossᵃ (cenA (a , b) (p , n)) (sqA (a , b) (p , n))
  cen-alg a b p n = solve 4 (λ a b p n → cross (cenP (a , b) (p , n)) (sqP (a , b) (p , n))) refl a b p n

  cen-sums : ∀ a b p n → sumsᵃ (cenA (a , b) (p , n)) (sqA (a , b) (p , n))
  cen-sums a b p n = solve 4 (λ a b p n → sums (cenP (a , b) (p , n)) (sqP (a , b) (p , n))) refl a b p n

  scl-alg : ∀ a b p n → crossᵃ (sclA (a , b) (p , n)) (sclA′ (a , b) (p , n))
  scl-alg a b p n = solve 4 (λ a b p n → cross (sclP (a , b) (p , n)) (sclP′ (a , b) (p , n))) refl a b p n

  scl-sums : ∀ a b p n → sumsᵃ (sclA (a , b) (p , n)) (sclA′ (a , b) (p , n))
  scl-sums a b p n = solve 4 (λ a b p n → sums (sclP (a , b) (p , n)) (sclP′ (a , b) (p , n))) refl a b p n

  -- ring identities for `Var-cen` (c = E f), `Var-shift`, `Var-scale`
  L1 : ∀ {n} → Pr n → Pr n → Pr n
  L1 m1 m2 = ((m2 ⊕ ng ((m1 ⊕ m1) ⊗ m1)) ⊕ (m1 ⊗ m1))
  LS : ∀ {n} → Pr n → Pr n → Pr n
  LS m c = ((ng ((ng c ⊕ ng c) ⊗ m) ⊕ (ng c ⊗ ng c)) ⊕ ng ((m ⊕ c) ⊗ (m ⊕ c)))
  RV : ∀ {n} → Pr n → Pr n → Pr n
  RV m1 m2 = (m2 ⊕ ng (m1 ⊗ m1))
  SQ : ∀ {n} → Pr n → Pr n → Pr n
  SQ m c = ((c ⊗ m) ⊗ (c ⊗ m))
  SQ′ : ∀ {n} → Pr n → Pr n → Pr n
  SQ′ m c = ((c ⊗ c) ⊗ (m ⊗ m))
  L1ᵃ : Pa → Pa → Pa
  L1ᵃ m1 m2 = ((m2 ⊕ᵃ ngᵃ ((m1 ⊕ᵃ m1) ⊗ᵃ m1)) ⊕ᵃ (m1 ⊗ᵃ m1))
  LSᵃ : Pa → Pa → Pa
  LSᵃ m c = (ngᵃ ((ngᵃ c ⊕ᵃ ngᵃ c) ⊗ᵃ m) ⊕ᵃ (ngᵃ c ⊗ᵃ ngᵃ c)) ⊕ᵃ ngᵃ ((m ⊕ᵃ c) ⊗ᵃ (m ⊕ᵃ c))
  RVᵃ : Pa → Pa → Pa
  RVᵃ m1 m2 = (m2 ⊕ᵃ ngᵃ (m1 ⊗ᵃ m1))
  SQᵃ : Pa → Pa → Pa
  SQᵃ m c = ((c ⊗ᵃ m) ⊗ᵃ (c ⊗ᵃ m))
  SQ′ᵃ : Pa → Pa → Pa
  SQ′ᵃ m c = ((c ⊗ᵃ c) ⊗ᵃ (m ⊗ᵃ m))

  R1-alg : ∀ a b c d → crossᵃ (L1ᵃ (a , b) (c , d)) (RVᵃ (a , b) (c , d))
  R1-alg a b c d = solve 4 (λ a b c d → cross (L1 (a , b) (c , d)) (RV (a , b) (c , d))) refl a b c d

  RS-alg : ∀ a b p n → crossᵃ (LSᵃ (a , b) (p , n)) (ngᵃ ((a , b) ⊗ᵃ (a , b)))
  RS-alg a b p n = solve 4 (λ a b p n → cross (LS (a , b) (p , n)) (ng ((a , b) ⊗ (a , b)))) refl a b p n

  SQ-alg : ∀ a b p n → crossᵃ (SQᵃ (a , b) (p , n)) (SQ′ᵃ (a , b) (p , n))
  SQ-alg a b p n = solve 4 (λ a b p n → cross (SQ (a , b) (p , n)) (SQ′ (a , b) (p , n))) refl a b p n

  fromCross : ∀ {x y : Sg} → pos x + neg y ≈ pos y + neg x → x ≃ y
  fromCross h = mk≃ 0# Is-0 (trans (+-identityʳ _) (trans h (sym (+-identityʳ _))))

  neg-mul : ∀ x y → (-S x) *S y ≃ -S (x *S y)
  neg-mul x y = fromCross (solve 4 (λ a b c d → cross (ng (a , b) ⊗ (c , d)) (ng ((a , b) ⊗ (c , d)))) refl
    (pos x) (neg x) (pos y) (neg y))

  mul-neg : ∀ x y → x *S (-S y) ≃ -S (x *S y)
  mul-neg x y = fromCross (solve 4 (λ a b c d → cross ((a , b) ⊗ ng (c , d)) (ng ((a , b) ⊗ (c , d)))) refl
    (pos x) (neg x) (pos y) (neg y))

  R-cen : ∀ m₁ m₂ → ((m₂ +S -S ((m₁ +S m₁) *S m₁)) +S m₁ *S m₁) ≃ m₂ +S -S (m₁ *S m₁)
  R-cen m₁ m₂ = fromCross (R1-alg (pos m₁) (neg m₁) (pos m₂) (neg m₂))

  -- (f + c)² − 2 (−c) m + c² − (m + c)² = −m²
  R-sh : ∀ m c → ((-S (((-S c) +S (-S c)) *S m) +S (-S c) *S (-S c)) +S -S ((m +S c) *S (m +S c))) ≃ -S (m *S m)
  R-sh m c = fromCross (RS-alg (pos m) (neg m) (pos c) (neg c))

  R-shift : ∀ m₁ m₂ c →
    ((m₂ +S -S (((-S c) +S (-S c)) *S m₁)) +S (-S c) *S (-S c)) +S -S ((m₁ +S c) *S (m₁ +S c)) ≃ m₂ +S -S (m₁ *S m₁)
  R-shift m₁ m₂ c =
    ≃-trans (+S-cong (+S-assoc _ _ _) ≃-refl) (≃-trans (+S-assoc _ _ _) (+S-cong ≃-refl (R-sh m₁ c)))

  R-scale : ∀ m₁ m₂ c → (c *S c) *S m₂ +S -S ((c *S m₁) *S (c *S m₁)) ≃ (c *S c) *S (m₂ +S -S (m₁ *S m₁))
  R-scale m₁ m₂ c = ≃-sym (≃-trans (*S-distribˡ (c *S c) m₂ (-S (m₁ *S m₁)))
    (+S-cong ≃-refl (≃-trans (mul-neg (c *S c) (m₁ *S m₁)) (-S-cong (≃-sym sq)))))
    where sq = fromCross (SQ-alg (pos m₁) (neg m₁) (pos c) (neg c))

  -- (1 + 1) c = c + c, and (−(c + c)) e = −(((1 + 1) c) e)
  two-c : ∀ c → (1S +S 1S) *S c ≃ c +S c
  two-c c = ≃-trans (*S-distribʳ c 1S 1S) (+S-cong (*S-identityˡ c) (*S-identityˡ c))

  bridge : ∀ c e → (-S (c +S c)) *S e ≃ -S (((1S +S 1S) *S c) *S e)
  bridge c e = ≃-trans (neg-mul (c +S c) e) (-S-cong (≃-sym (*S-congˡ e (two-c c))))

  -- pointwise facts for the tests
  module _ {X : QBS S} (f : SgT X) (c : Sg) where
    cen-eq : cen f c *T cen f c ≐ Sq f c
    cen-eq x = cen-alg (at⁺ f x) (at⁻ f x) (pos c) (neg c)

    cen-bnd : ∀ x → at⁺ (cen f c *T cen f c) x + at⁻ (cen f c *T cen f c) x ≈ at⁺ (Sq f c) x + at⁻ (Sq f c) x
    cen-bnd x = cen-sums (at⁺ f x) (at⁻ f x) (pos c) (neg c)

    scl-eq : (scaleT c f *T scaleT c f) ≐ scaleT (c *S c) (f *T f)
    scl-eq x = scl-alg (at⁺ f x) (at⁻ f x) (pos c) (neg c)

    scl-bnd : ∀ x → at⁺ (scaleT c f *T scaleT c f) x + at⁻ (scaleT c f *T scaleT c f) x
      ≈ at⁺ (scaleT (c *S c) (f *T f)) x + at⁻ (scaleT (c *S c) (f *T f)) x
    scl-bnd x = scl-sums (at⁺ f x) (at⁻ f x) (pos c) (neg c)

  -- integrability from a pointwise bound by the sum of the parts of an integrable test
  Int-via : ∀ {X : QBS S} (p : C.Pre (XW X)) (F G : SgT X) → Int p G →
    (∀ x → at⁺ F x + at⁻ F x ≈ at⁺ G x + at⁻ G x) → Int p F
  Int-via {X} p F G (i⁺ , i⁻) e = Int-dom p F (addX (posT G) (negT G))
    (bnd≈ {X} (∫+ {X} p (posT G) (negT G)) (Is-+ {_} {_} i⁺ i⁻)) (λ x → ≤-reflexive (e x))
