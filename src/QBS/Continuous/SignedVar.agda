{-# OPTIONS --safe --without-K #-}

-- Variance of a signed test under a probability distribution (plan 03, "Information quantities").
-- For P : Pre X, p = ιPre P and f with f and f² integrable (`Int₂`):
--   * `Var P f i = E[f²] − (E f)²` as a signed value;
--   * the centred test `cen f c = f − c`, its square is integrable (`Int-cen`), and
--     E[(f − c)²] ≃ E[f²] − 2c E f + c² (`Ex-cen`); with c = E f this is the variance (`Var-cen`);
--   * `Var-shift` (Var (f + c) ≃ Var f) and `Var-scale` (Var (c f) ≃ c² Var f), with `Int₂-shift`, `Int₂-scale`.
-- Route: expand (f + c)·(f + c) ≐ f² + 2c f + c² as signed tests (pointwise ring identities on the parts, `_≐_`), then
-- `Ex-cong`, `Ex-+`, `Ex-scale`, `Ex-const` (P is a probability) and `Analysis/Signed` ring algebra on `Sg`.
-- Integrability of (f + c)² by `Int-dom` with g = (1 + c⁺ + c⁻)·(f⁺ + f⁻ + f²-parts + 1), or by `Int-+`/`Int-scale`
-- applied to the expansion and `Ex-cong`-style transport of `Int` along `_≐_` (a helper, if needed).
--   Skeleton: holes first.
module QBS.Continuous.SignedVar where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedVar (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; 1S)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; _≐_; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex)

  module _ {X : QBS S} (P : Pre X) where

    -- f and f² integrable
    Int₂ : SgT X → Set₁
    Int₂ f = Int (ιPre {X} P) f × Int (ιPre {X} P) (f *T f)

    -- E[f²] − (E f)²
    Var : ∀ (f : SgT X) → Int₂ f → Sg
    Var f (i , j) = Ex (ιPre {X} P) (f *T f) j +S -S (Ex (ιPre {X} P) f i *S Ex (ιPre {X} P) f i)

    Var-irr : ∀ f (i j : Int₂ f) → Var f i ≃ Var f j
    Var-irr = ?

    Var-cong : ∀ (f g : SgT X) (i : Int₂ f) (j : Int₂ g) → f ≐ g → Var f i ≃ Var g j
    Var-cong = ?

    -- the centred test f − c
    cen : SgT X → Sg → SgT X
    cen f c = f +T constT (-S c)

    Int-cen : ∀ f c → Int₂ f → Int (ιPre {X} P) (cen f c *T cen f c)
    Int-cen = ?

    -- E[(f − c)²] ≃ E[f²] − 2c E f + c²
    Ex-cen : ∀ f c (ij : Int₂ f) →
      Ex (ιPre {X} P) (cen f c *T cen f c) (Int-cen f c ij)
        ≃ (Ex (ιPre {X} P) (f *T f) (proj₂ ij) +S -S (((1S +S 1S) *S c) *S Ex (ιPre {X} P) f (proj₁ ij))) +S c *S c
    Ex-cen = ?

    -- E[(f − E f)²] ≃ Var f
    Var-cen : ∀ f (ij : Int₂ f) →
      Ex (ιPre {X} P) (cen f (Ex (ιPre {X} P) f (proj₁ ij)) *T cen f (Ex (ιPre {X} P) f (proj₁ ij)))
        (Int-cen f (Ex (ιPre {X} P) f (proj₁ ij)) ij) ≃ Var f ij
    Var-cen = ?

    -- shifting and scaling
    Int₂-shift : ∀ f c → Int₂ f → Int₂ (f +T constT c)
    Int₂-shift = ?

    Var-shift : ∀ f c (ij : Int₂ f) → Var (f +T constT c) (Int₂-shift f c ij) ≃ Var f ij
    Var-shift = ?

    Int₂-scale : ∀ f c → Int₂ f → Int₂ (scaleT c f)
    Int₂-scale = ?

    Var-scale : ∀ f c (ij : Int₂ f) → Var (scaleT c f) (Int₂-scale f c ij) ≃ (c *S c) *S Var f ij
    Var-scale = ?
