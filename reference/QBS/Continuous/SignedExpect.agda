{-# OPTIONS --safe --without-K #-}

-- Expectations of signed tests against any s-finite measure.  Signed integration here is the standard Jordan-decomposition
-- integral: for f = f⁺ − f⁻ it is ∫ f⁺ − ∫ f⁻, defined exactly when both integrals are finite (so `Ex` is linear on the
-- integrable differences of positive tests, and `Ex-irr` is its well-definedness).
--   * `Int p f`: both parts have finite integrals; `Ex p f i = ∫ f⁺ − ∫ f⁻ : Sg`.  The value never depends on the
--     integrability proof (`Ex-irr`), so statements may use any proof;
--   * `Ex-cong` (from `_≐_`), linearity (`Ex-+`, `Ex-neg`, `Ex-scale`), constants under a probability (`Ex-const`),
--     monotonicity (`Ex-mono`, cross-added on the integrals), integrability by domination (`Int-dom`);
--   * the one-sided expectation `Ex∞ p f i⁻ : Sg∞` (`SignedInf`) when only ∫ f⁻ is finite, with `Ex∞-ι` (it agrees
--     with `Ex` when both parts are finite), `Ex∞-+` and `Ex∞-mono`.
-- Route: integrate the pointwise cross-added equality with `FatouAux.∫ᴹ-addX` (`Ex-cong`, witness 0); `Ex-scale` from
-- `Product.cmul`; `Ex-const` from `Dominated.prob-mass`; `Int-dom` and `Ex-mono` from `SupTest.∫ᴹ-monoX`.
module QBS.Continuous.SignedExpect where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_×_; _,_; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.Dominated using (module Dominated)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedInf using (module SignedInf)

module SignedExpect (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; _*S_; -S_; _−_[_,_])
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SupTest (lemOf lem₁) using (∫ᴹ-monoX)
  open Product (lemOf lem₁) using (cmul)
  open Dominated lem₁ using (prob-mass)
  open Weights (lemOf lem₁) using (constW)
  open OmegaSemiring A using (refl; sym; trans; +-cong; +-comm; +-mono; ≤-trans; ≤-reflexive; ≤-+ʳ; +-identityʳ)
  open Bounded A using (mk≃; finite)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-+; Is-*; Is-0)
  open Sg
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; -T_; scaleT; constT)
  open SignedInf lem₁ using (mk≃∞; mk≤∞; Sg∞; _≃∞_; _≤∞_; _+∞_; ι∞; _−∞_[_])
  open QBS
  open Hom

  module _ {X : QBS S} where

    Int Int⁻ : C.Pre (XW X) → SgT X → Set₁
    Int p f = Bnd (∫ᴹ {X} p (posT f)) × Bnd (∫ᴹ {X} p (negT f))
    Int⁻ p f = Bnd (∫ᴹ {X} p (negT f))

    Ex : ∀ (p : C.Pre (XW X)) (f : SgT X) → Int p f → Sg
    Ex p f (i⁺ , i⁻) = ∫ᴹ {X} p (posT f) − ∫ᴹ {X} p (negT f) [ i⁺ , i⁻ ]

    Ex∞ : ∀ (p : C.Pre (XW X)) (f : SgT X) → Int⁻ p f → Sg∞
    Ex∞ p f i⁻ = ∫ᴹ {X} p (posT f) −∞ ∫ᴹ {X} p (negT f) [ i⁻ ]

    -- helpers: integrals of sums and of scaled sums; finiteness transfers along ≈ and ≤
    ∫+ : ∀ (p : C.Pre (XW X)) (u v : Hom S X WQ) → ∫ᴹ {X} p (addX u v) ≈ ∫ᴹ {X} p u + ∫ᴹ {X} p v
    ∫+ = ∫ᴹ-addX {X}

    ∫scal : ∀ (p : C.Pre (XW X)) a b (u v : Hom S X WQ) →
      ∫ᴹ {X} p (addX (mulH {X} (constW {X} a) u) (mulH {X} (constW {X} b) v)) ≈ a * ∫ᴹ {X} p u + b * ∫ᴹ {X} p v
    ∫scal p a b u v = trans (∫+ p _ _) (+-cong (cmul p a u) (cmul p b v))

    bnd≈ : ∀ {a b} → a ≈ b → Bnd b → Bnd a
    bnd≈ e (n , h) = n , ≤-trans (≤-reflexive e) h

    bnd≤ : ∀ {a b} → a ≤ b → Bnd b → Bnd a
    bnd≤ le (n , h) = n , ≤-trans le h

    -- the cross-added identity behind `Ex-+` and `Ex∞-+`
    sumEq : ∀ (p : C.Pre (XW X)) (f g : SgT X) →
      ∫ᴹ {X} p (posT (f +T g)) + (∫ᴹ {X} p (negT f) + ∫ᴹ {X} p (negT g)) + 0# ≈
      (∫ᴹ {X} p (posT f) + ∫ᴹ {X} p (posT g)) + ∫ᴹ {X} p (negT (f +T g)) + 0#
    sumEq p f g = +-cong (+-cong (∫+ p (posT f) (posT g)) (sym (∫+ p (negT f) (negT g)))) refl

    Ex-irr : ∀ p f (i j : Int p f) → Ex p f i ≃ Ex p f j
    Ex-irr p f i j = mk≃ 0# Is-0 refl

    Ex-cong : ∀ p (f g : SgT X) (i : Int p f) (j : Int p g) → f ≐ g → Ex p f i ≃ Ex p g j
    Ex-cong p f g i j e = mk≃ 0# Is-0 (+-cong (trans (sym (∫+ p (posT f) (negT g)))
      (trans (∫ᴹ-cong p {addX (posT f) (negT g)} {addX (posT g) (negT f)} e) (∫+ p (posT g) (negT f)))) refl)

    -- integrability
    Int-dom : ∀ p (f : SgT X) (g : Hom S X WQ) → Bnd (∫ᴹ {X} p g) →
      (∀ x → at⁺ f x + at⁻ f x ≤ map g ⟨$⟩ x) → Int p f
    Int-dom p f g bg le =
      bnd≤ (∫ᴹ-monoX p {posT f} {g} (λ x → ≤-trans (≤-+ʳ {at⁺ f x} {at⁻ f x}) (le x))) bg ,
      bnd≤ (∫ᴹ-monoX p {negT f} {g} (λ x → ≤-trans (≤-trans (≤-+ʳ {at⁻ f x} {at⁺ f x})
        (≤-reflexive (+-comm (at⁻ f x) (at⁺ f x)))) (le x))) bg

    Int-+ : ∀ p {f g : SgT X} → Int p f → Int p g → Int p (f +T g)
    Int-+ p (i⁺ , i⁻) (j⁺ , j⁻) =
      bnd≈ (∫+ p _ _) (Is-+ {_} {_} i⁺ j⁺) , bnd≈ (∫+ p _ _) (Is-+ {_} {_} i⁻ j⁻)

    Int-neg : ∀ p {f : SgT X} → Int p f → Int p (-T f)
    Int-neg p (i⁺ , i⁻) = i⁻ , i⁺

    Int-scale : ∀ p c {f : SgT X} → Int p f → Int p (scaleT c f)
    Int-scale p c (i⁺ , i⁻) =
      bnd≈ (∫scal p (pos c) (neg c) _ _) (Is-+ {_} {_} (Is-* {_} {_} (pos-fin c) i⁺) (Is-* {_} {_} (neg-fin c) i⁻)) ,
      bnd≈ (∫scal p (pos c) (neg c) _ _) (Is-+ {_} {_} (Is-* {_} {_} (pos-fin c) i⁻) (Is-* {_} {_} (neg-fin c) i⁺))

    -- linearity
    Ex-+ : ∀ p (f g : SgT X) (i : Int p f) (j : Int p g) → Ex p (f +T g) (Int-+ p i j) ≃ Ex p f i +S Ex p g j
    Ex-+ p f g i j = mk≃ 0# Is-0 (sumEq p f g)

    Ex-neg : ∀ p (f : SgT X) (i : Int p f) → Ex p (-T f) (Int-neg p i) ≃ -S (Ex p f i)
    Ex-neg p f i = mk≃ 0# Is-0 refl

    Ex-scale : ∀ p c (f : SgT X) (i : Int p f) → Ex p (scaleT c f) (Int-scale p c i) ≃ c *S Ex p f i
    Ex-scale p c f i = mk≃ 0# Is-0 (+-cong (+-cong (∫scal p (pos c) (neg c) _ _) (sym (∫scal p (pos c) (neg c) _ _))) refl)

    -- constants under a probability
    Int-const : ∀ (P : Pre X) c → Int (ιPre {X} P) (constT c)
    Int-const P c = bnd≈ (prob-mass P (pos c)) (pos-fin c) , bnd≈ (prob-mass P (neg c)) (neg-fin c)

    Ex-const : ∀ (P : Pre X) c → Ex (ιPre {X} P) (constT c) (Int-const P c) ≃ c
    Ex-const P c = mk≃ 0# Is-0 (+-cong (+-cong (prob-mass P (pos c)) (sym (prob-mass P (neg c)))) refl)

    -- monotonicity, cross-added
    Ex-mono : ∀ p (f g : SgT X) → (∀ x → at⁺ f x + at⁻ g x ≤ at⁺ g x + at⁻ f x) →
      ∫ᴹ {X} p (posT f) + ∫ᴹ {X} p (negT g) ≤ ∫ᴹ {X} p (posT g) + ∫ᴹ {X} p (negT f)
    Ex-mono p f g le = ≤-trans (≤-reflexive (sym (∫+ p (posT f) (negT g))))
      (≤-trans (∫ᴹ-monoX p {addX (posT f) (negT g)} {addX (posT g) (negT f)} le) (≤-reflexive (∫+ p (posT g) (negT f))))

    -- one-sided
    Ex∞-ι : ∀ p (f : SgT X) (i : Int p f) → Ex∞ p f (proj₂ i) ≃∞ ι∞ (Ex p f i)
    Ex∞-ι p f i = mk≃∞ 0# Is-0 refl

    Int⁻-+ : ∀ p {f g : SgT X} → Int⁻ p f → Int⁻ p g → Int⁻ p (f +T g)
    Int⁻-+ p i j = bnd≈ (∫+ p _ _) (Is-+ {_} {_} i j)

    Ex∞-+ : ∀ p (f g : SgT X) (i : Int⁻ p f) (j : Int⁻ p g) →
      Ex∞ p (f +T g) (Int⁻-+ p i j) ≃∞ Ex∞ p f i +∞ Ex∞ p g j
    Ex∞-+ p f g i j = mk≃∞ 0# Is-0 (sumEq p f g)

    Ex∞-mono : ∀ p (f g : SgT X) (i : Int⁻ p f) (j : Int⁻ p g) →
      (∀ x → at⁺ f x + at⁻ g x ≤ at⁺ g x + at⁻ f x) → Ex∞ p f i ≤∞ Ex∞ p g j
    Ex∞-mono p f g i j le = mk≤∞ 0# Is-0 (≤-trans (≤-reflexive (+-identityʳ _))
      (≤-trans (Ex-mono p f g le) (≤-reflexive (sym (+-identityʳ _)))))
