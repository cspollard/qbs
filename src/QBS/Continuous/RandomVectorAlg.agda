{-# OPTIONS --safe --without-K #-}

-- Pointwise facts for products of signed tests (plan 05, item 52; helper for `RandomVector`).
--   * `Int-mul`: for any s-finite measure, square-integrable tests have an integrable product;
--   * `comm-eq`, `comm-sums`: f g ≐ g f, and the sums of the parts agree pointwise;
--   * `sc-eq`: (c f)(d g) ≐ (c d)(f g);   `sh-eq`: (f + c)(g + d) ≐ (f g + d f) + (c g + c d).
-- Route: `Int-mul` by `SignedExpect.Int-dom` with the dominating test f² + g² and the pointwise bound a b ≤ a² + b² on
-- the sums a, b of the parts (`mul-le`: compare a and b, `MonusAlg.cut-total`); the identities are solver calls in
-- `RandomVectorRing`, transported by `SignedVarAlg.via-cross` and `via-sums`.
module QBS.Continuous.RandomVectorAlg where

import Relation.Binary.PropositionalEquality as ≡
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
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
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Continuous.SignedVarRing using (module Ring)
open import QBS.Continuous.RandomVectorRing using (module RVRing)

module RandomVectorAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; refl; sym; trans; *-comm; ≤-trans; ≤-reflexive; ≤-+ʳ; +-comm;
    *-mono; commutativeSemiring)
  open Bounded A using (Sg; _*S_)
  open Sg
  open SubSemiring (Bounded.finite A) using (Is-+)
  open SFinite (lemOf lem₁) using (XW; module C)
  open MonusAlg lem₁ using (cut-total)
  open FatouAux lem₁ using (addX)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Int-+; Int-dom; bnd≈; ∫+)
  open SignedVarAlg lem₁ using (via-cross; via-sums; ⟦_⟧; pr)
  open Ring commutativeSemiring using (_⊗ᵃ_)
  open RVRing commutativeSemiring using (SCᵃ; SC′ᵃ; SHᵃ; SH′ᵃ; comm-cross; sc-cross; sh-cross)
    renaming (comm-sums to comm-sumsᵃ)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring using (solve; _:+_; _:*_; _:=_)

  -- x y ≤ x² + y²
  sq-le : ∀ x y → x * y ≤ x * x + y * y
  sq-le x y with cut-total x y
  ... | inj₁ xy = ≤-trans (≤-reflexive (*-comm x y)) (≤-trans (*-mono y xy)
    (≤-trans (≤-+ʳ {y * y} {x * x}) (≤-reflexive (+-comm (y * y) (x * x)))))
  ... | inj₂ yx = ≤-trans (*-mono x yx) (≤-+ʳ {x * x} {y * y})

  -- a b ≤ a² + b² for the sums of the parts
  mul-le : ∀ a b c d → ((a * c + b * d) + (a * d + b * c)) ≤
    (((a * a + b * b) + (a * b + b * a)) + ((c * c + d * d) + (c * d + d * c)))
  mul-le a b c d = ≤-trans (≤-reflexive (solve 4 (λ a b c d → ((a :* c :+ b :* d) :+ (a :* d :+ b :* c))
      := (a :+ b) :* (c :+ d)) refl a b c d))
    (≤-trans (sq-le (a + b) (c + d)) (≤-reflexive (sym (solve 4 (λ a b c d →
      (((a :* a :+ b :* b) :+ (a :* b :+ b :* a)) :+ ((c :* c :+ d :* d) :+ (c :* d :+ d :* c)))
      := (a :+ b) :* (a :+ b) :+ (c :+ d) :* (c :+ d)) refl a b c d))))

  -- the product of square-integrable tests
  Int-mul : ∀ {Ω : QBS S} (p : C.Pre (XW Ω)) (f g : SgT Ω) → Int {Ω} p (f *T f) → Int {Ω} p (g *T g) → Int {Ω} p (f *T g)
  Int-mul {Ω} p f g (i⁺ , i⁻) (j⁺ , j⁻) = Int-dom {Ω} p (f *T g) D
    (bnd≈ {Ω} (∫+ {Ω} p _ _) (Is-+ {_} {_} (bnd≈ {Ω} (∫+ {Ω} p _ _) (Is-+ {_} {_} i⁺ i⁻))
      (bnd≈ {Ω} (∫+ {Ω} p _ _) (Is-+ {_} {_} j⁺ j⁻))))
    (λ x → mul-le (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x))
    where D = addX (addX (posT (f *T f)) (negT (f *T f))) (addX (posT (g *T g)) (negT (g *T g)))

  -- commutativity
  comm-eq : ∀ {X : QBS S} (f g : SgT X) → f *T g ≐ g *T f
  comm-eq f g x = via-cross {F = f *T g} {G = g *T f} {P = ⟦ f ⟧ x ⊗ᵃ ⟦ g ⟧ x} {Q = ⟦ g ⟧ x ⊗ᵃ ⟦ f ⟧ x} ≡.refl ≡.refl
    (comm-cross (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x))

  comm-sums : ∀ {X : QBS S} (f g : SgT X) x → at⁺ (f *T g) x + at⁻ (f *T g) x ≈ at⁺ (g *T f) x + at⁻ (g *T f) x
  comm-sums f g x = via-sums {F = f *T g} {G = g *T f} {P = ⟦ f ⟧ x ⊗ᵃ ⟦ g ⟧ x} {Q = ⟦ g ⟧ x ⊗ᵃ ⟦ f ⟧ x} ≡.refl ≡.refl
    (comm-sumsᵃ (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x))

  -- scaling and shifting
  sc-eq : ∀ {X : QBS S} (c d : Sg) (f g : SgT X) → scaleT c f *T scaleT d g ≐ scaleT (c *S d) (f *T g)
  sc-eq c d f g x = via-cross {F = scaleT c f *T scaleT d g} {G = scaleT (c *S d) (f *T g)}
    {P = SCᵃ (pr c) (⟦ f ⟧ x) (pr d) (⟦ g ⟧ x)} {Q = SC′ᵃ (pr c) (⟦ f ⟧ x) (pr d) (⟦ g ⟧ x)} ≡.refl ≡.refl
    (sc-cross (pos c) (neg c) (at⁺ f x) (at⁻ f x) (pos d) (neg d) (at⁺ g x) (at⁻ g x))

  sh-eq : ∀ {X : QBS S} (c d : Sg) (f g : SgT X) →
    (f +T constT c) *T (g +T constT d) ≐ ((f *T g) +T scaleT d f) +T (scaleT c g +T constT (c *S d))
  sh-eq {X} c d f g x = via-cross {F = (f +T constT c) *T (g +T constT d)}
    {G = ((f *T g) +T scaleT d f) +T (scaleT c g +T constT (c *S d))}
    {P = SHᵃ (⟦ f ⟧ x) (pr c) (⟦ g ⟧ x) (pr d)} {Q = SH′ᵃ (⟦ f ⟧ x) (pr c) (⟦ g ⟧ x) (pr d)} ≡.refl ≡.refl
    (sh-cross (at⁺ f x) (at⁻ f x) (pos c) (neg c) (at⁺ g x) (at⁻ g x) (pos d) (neg d))
