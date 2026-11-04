{-# OPTIONS --safe --without-K #-}

-- Expectations of signed tests against any s-finite measure (plan 03, "Signed layer").
--   * `Int p f`: both parts have finite integrals; `Ex p f i = ∫ f⁺ − ∫ f⁻ : Sg`.  The value never depends on the
--     integrability proof (`Ex-irr`), so statements may use any proof;
--   * `Ex-cong` (from `_≐_`), linearity (`Ex-+`, `Ex-neg`, `Ex-scale`), constants under a probability (`Ex-const`),
--     monotonicity (`Ex-mono`, cross-added on the integrals), integrability by domination (`Int-dom`);
--   * the one-sided expectation `Ex∞ p f i⁻ : Sg∞` (`SignedInf`) when only ∫ f⁻ is finite, with `Ex∞-ι` (it agrees
--     with `Ex` when both parts are finite), `Ex∞-+` and `Ex∞-mono`.
-- Route: integrate the pointwise cross-added equality with `FatouAux.∫ᴹ-addX` (`Ex-cong`, witness 0); `Ex-scale` from
-- `Product.cmul`; `Ex-const` from `Dominated.prob-mass`; `Int-dom` and `Ex-mono` from `SupTest.∫ᴹ-monoX`.
--   Skeleton: holes first.
module QBS.Continuous.SignedExpect where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

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
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedInf using (module SignedInf)

module SignedExpect (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; _+_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; _*S_; -S_; _−_[_,_])
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; -T_; scaleT; constT)
  open SignedInf lem₁ using (Sg∞; _≃∞_; _≤∞_; _+∞_; ι∞; _−∞_[_])
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

    Ex-irr : ∀ p f (i j : Int p f) → Ex p f i ≃ Ex p f j
    Ex-irr = ?

    Ex-cong : ∀ p (f g : SgT X) (i : Int p f) (j : Int p g) → f ≐ g → Ex p f i ≃ Ex p g j
    Ex-cong = ?

    -- integrability
    Int-dom : ∀ p (f : SgT X) (g : Hom S X WQ) → Bnd (∫ᴹ {X} p g) → (∀ x → at⁺ f x + at⁻ f x ≤ map g ⟨$⟩ x) → Int p f
    Int-dom = ?

    Int-+ : ∀ p {f g : SgT X} → Int p f → Int p g → Int p (f +T g)
    Int-+ = ?

    Int-neg : ∀ p {f : SgT X} → Int p f → Int p (-T f)
    Int-neg p (i⁺ , i⁻) = i⁻ , i⁺

    Int-scale : ∀ p c {f : SgT X} → Int p f → Int p (scaleT c f)
    Int-scale = ?

    -- linearity
    Ex-+ : ∀ p (f g : SgT X) (i : Int p f) (j : Int p g) → Ex p (f +T g) (Int-+ p i j) ≃ Ex p f i +S Ex p g j
    Ex-+ = ?

    Ex-neg : ∀ p (f : SgT X) (i : Int p f) → Ex p (-T f) (Int-neg p i) ≃ -S (Ex p f i)
    Ex-neg = ?

    Ex-scale : ∀ p c (f : SgT X) (i : Int p f) → Ex p (scaleT c f) (Int-scale p c i) ≃ c *S Ex p f i
    Ex-scale = ?

    -- constants under a probability
    Int-const : ∀ (P : Pre X) c → Int (ιPre {X} P) (constT c)
    Int-const = ?

    Ex-const : ∀ (P : Pre X) c → Ex (ιPre {X} P) (constT c) (Int-const P c) ≃ c
    Ex-const = ?

    -- monotonicity, cross-added
    Ex-mono : ∀ p (f g : SgT X) → (∀ x → at⁺ f x + at⁻ g x ≤ at⁺ g x + at⁻ f x) →
      ∫ᴹ {X} p (posT f) + ∫ᴹ {X} p (negT g) ≤ ∫ᴹ {X} p (posT g) + ∫ᴹ {X} p (negT f)
    Ex-mono = ?

    -- one-sided
    Ex∞-ι : ∀ p (f : SgT X) (i : Int p f) → Ex∞ p f (proj₂ i) ≃∞ ι∞ (Ex p f i)
    Ex∞-ι = ?

    Int⁻-+ : ∀ p {f g : SgT X} → Int⁻ p f → Int⁻ p g → Int⁻ p (f +T g)
    Int⁻-+ = ?

    Ex∞-+ : ∀ p (f g : SgT X) (i : Int⁻ p f) (j : Int⁻ p g) → Ex∞ p (f +T g) (Int⁻-+ p i j) ≃∞ Ex∞ p f i +∞ Ex∞ p g j
    Ex∞-+ = ?

    Ex∞-mono : ∀ p (f g : SgT X) (i : Int⁻ p f) (j : Int⁻ p g) →
      (∀ x → at⁺ f x + at⁻ g x ≤ at⁺ g x + at⁻ f x) → Ex∞ p f i ≤∞ Ex∞ p g j
    Ex∞-mono = ?
