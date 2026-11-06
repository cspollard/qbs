{-# OPTIONS --safe --without-K #-}

-- Finite signed tests are closed under the test operations (plan 07, items 59 and 60; helper for
-- `Continuous/ExpFamilyAux` and `Continuous/ExpFamilyPostAux`).  `FinT f` says both parts of f are finite everywhere:
--   * `FinT-+T`, `FinT-negT`, `FinT-scaleT`, `FinT-constT`: closure under `_+T_`, `-T_`, `scaleT c` and `constT c`
--     (signed constants have finite parts);
--   * `FinT-∘T`: closure under precomposition.
-- Route: pointwise from `SubSemiring.Is-+` and `Is-*` for `Bounded.finite`.
module QBS.Continuous.FinTest where

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SignedTest using (module SignedTest)

module FinTest (lem₁ : LEM₁) where
  private
    A = Lebesgue.A (lemOf lem₁)
  open Bounded A using (Sg; finite)
  open Sg
  open SubSemiring finite using (Is-+; Is-*)
  open SignedTest lem₁ using (SgT; FinT; _+T_; -T_; scaleT; constT; _∘T_)
  open Hom

  FinT-+T : ∀ {X : QBS S} {f g : SgT X} → FinT f → FinT g → FinT (f +T g)
  FinT-+T ff fg x = Is-+ (proj₁ (ff x)) (proj₁ (fg x)) , Is-+ (proj₂ (ff x)) (proj₂ (fg x))

  FinT-negT : ∀ {X : QBS S} {f : SgT X} → FinT f → FinT (-T f)
  FinT-negT ff x = proj₂ (ff x) , proj₁ (ff x)

  FinT-scaleT : ∀ {X : QBS S} (c : Sg) {f : SgT X} → FinT f → FinT (scaleT c f)
  FinT-scaleT c ff x = Is-+ (Is-* (pos-fin c) (proj₁ (ff x))) (Is-* (neg-fin c) (proj₂ (ff x)))
                     , Is-+ (Is-* (pos-fin c) (proj₂ (ff x))) (Is-* (neg-fin c) (proj₁ (ff x)))

  FinT-constT : ∀ {X : QBS S} (c : Sg) → FinT (constT {X} c)
  FinT-constT c x = pos-fin c , neg-fin c

  FinT-∘T : ∀ {X Y : QBS S} {f : SgT Y} (φ : Hom S X Y) → FinT f → FinT (f ∘T φ)
  FinT-∘T φ ff x = ff (map φ ⟨$⟩ x)
