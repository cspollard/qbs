{-# OPTIONS --safe --without-K #-}

-- Fubini and independence for signed tests (plan 03, "Signed layer").
-- For s-finite s on X, t on Y and a signed test f on X × Y integrable against s ⊗ t (`Product.prodPre`):
--   * `innerT s f`: y ↦ ∫ f(x, y) ds(x), as a signed test on Y, cut to where both inner integrals are finite
--     (`NullInf.finχ`); `Int-inner`, and `Ex-fubini : Ex (s ⊗ t) f ≃ Ex t (innerT s f)`;
--   * `_⊗T_`: f(x) g(y) for signed tests on X and Y; `Int-⊗` and independence `Ex-⊗ : Ex (s ⊗ t) (f ⊗ g) ≃ Ex s f · Ex t g`.
-- Route: `Product.∫-prod` for each part, so ∫ (intL s f±) dt = ∫ f± d(s ⊗ t) is finite; the set where an inner
-- integral is infinite is t-null (`NullInf.∫-fin-cut` with g = intL f⁺ + intL f⁻).  `Ex-⊗` from `Product.∫-rect`
-- on the four products of parts and `FatouAux.∫ᴹ-addX`.
--   Skeleton: holes first.
module QBS.Continuous.SignedFubini where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; fstQ; sndQ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.NullInf using (module NullInf)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedFubini (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Bnd; Sg; _≃_; _*S_)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open FatouAux lem₁ using (addX)
  open Product (lemOf lem₁) using (prodPre; intL)
  open NullInf lem₁ using (finχ)
  open SignedTest lem₁ using (SgT; posT; negT; _*T_; _∘T_)
  open SignedExpect lem₁ using (Int; Ex)
  open QBS
  open Hom

  module _ {X Y : QBS S} where

    XY : QBS S
    XY = _×Q_ S X Y

    -- the inner integral y ↦ ∫ f(x, y) ds(x), cut to where both parts are finite
    innerT : C.Pre (XW X) → SgT XY → SgT Y
    innerT s f = mulH {Y} cut (intL {X} {Y} s (posT f)) , mulH {Y} cut (intL {X} {Y} s (negT f))
      where cut = finχ {Y} (addX (intL {X} {Y} s (posT f)) (intL {X} {Y} s (negT f)))

    Int-inner : ∀ s t (f : SgT XY) → Int {XY} (prodPre {X} {Y} s t) f → Int {Y} t (innerT s f)
    Int-inner = ?

    Ex-fubini : ∀ s t (f : SgT XY) (i : Int {XY} (prodPre {X} {Y} s t) f) →
      Ex {XY} (prodPre {X} {Y} s t) f i ≃ Ex {Y} t (innerT s f) (Int-inner s t f i)
    Ex-fubini = ?

    -- f(x) g(y)
    infixl 7 _⊗T_
    _⊗T_ : SgT X → SgT Y → SgT XY
    f ⊗T g = (f ∘T fstQ S) *T (g ∘T sndQ S)

    Int-⊗ : ∀ s t (f : SgT X) (g : SgT Y) → Int {X} s f → Int {Y} t g → Int {XY} (prodPre {X} {Y} s t) (f ⊗T g)
    Int-⊗ = ?

    Ex-⊗ : ∀ s t (f : SgT X) (g : SgT Y) (i : Int {X} s f) (j : Int {Y} t g) →
      Ex {XY} (prodPre {X} {Y} s t) (f ⊗T g) (Int-⊗ s t f g i j) ≃ Ex {X} s f i *S Ex {Y} t g j
    Ex-⊗ = ?
