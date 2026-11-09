{-# OPTIONS --safe --without-K #-}

-- Fubini and independence for signed tests.
-- For s-finite s on X, t on Y and a signed test f on X × Y integrable against s ⊗ t (`Product.prodPre`):
--   * `innerT s f`: y ↦ ∫ f(x, y) ds(x), as a signed test on Y, cut to where both inner integrals are finite
--     (`IntegrableFinite.finχ`); `Int-inner`, and `Ex-fubini : Ex (s ⊗ t) f ≃ Ex t (innerT s f)`;
--   * `_⊗T_`: f(x) g(y) for signed tests on X and Y; `Int-⊗` and independence `Ex-⊗ : Ex (s ⊗ t) (f ⊗ g) ≃ Ex s f · Ex t g`.
-- Route: `Product.∫-prod` for each part, so ∫ (intL s f±) dt = ∫ f± d(s ⊗ t) is finite; the set where an inner
-- integral is infinite is t-null (`IntegrableFinite.∫-fin-cut` with g = intL f⁺ + intL f⁻).  `Ex-⊗` from `Product.∫-rect`
-- on the four products of parts and `FatouAux.∫ᴹ-addX`.
module QBS.Continuous.SignedFubini where

open import Data.Product.Base using (_,_; proj₁; proj₂)

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
open import QBS.Continuous.IntegrableFinite using (module IntegrableFinite)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedFubini (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Bnd; Sg; _≃_; _*S_)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open Product (lemOf lem₁) using (prodPre; intL; ∫-prod; ∫-rect)
  open IntegrableFinite lem₁ using (finχ; ∫-fin-cut)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; refl; sym; trans; +-cong)
  open Bounded A using (mk≃; finite)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-+; Is-*; Is-0)
  open Sg
  open SignedTest lem₁ using (SgT; posT; negT; _*T_; _∘T_)
  open SignedExpect lem₁ using (Int; Ex; bnd≈)
  open QBS
  open Hom

  module _ {X Y : QBS S} where

    XY : QBS S
    XY = _×Q_ S X Y

    -- the inner integral y ↦ ∫ f(x, y) ds(x), cut to where both parts are finite
    innerT : C.Pre (XW X) → SgT XY → SgT Y
    innerT s f = mulH {Y} cut (intL {X} {Y} s (posT f)) , mulH {Y} cut (intL {X} {Y} s (negT f))
      where cut = finχ {Y} (addX (intL {X} {Y} s (posT f)) (intL {X} {Y} s (negT f)))

    -- the inner integrals are t-integrable, and the cut does not change their integrals
    bnd-sum : ∀ s t (f : SgT XY) → Int {XY} (prodPre {X} {Y} s t) f →
      Bnd (∫ᴹ {Y} t (addX (intL {X} {Y} s (posT f)) (intL {X} {Y} s (negT f))))
    bnd-sum s t f (i⁺ , i⁻) = bnd≈ {Y} (∫ᴹ-addX {Y} t _ _) (Is-+ {_} {_}
      (bnd≈ {XY} (sym (∫-prod {X} {Y} s t (posT f))) i⁺) (bnd≈ {XY} (sym (∫-prod {X} {Y} s t (negT f))) i⁻))

    ∫-cut : ∀ s t (f : SgT XY) → Int {XY} (prodPre {X} {Y} s t) f → ∀ (u : SgT XY → Hom S XY WQ) →
      ∫ᴹ {Y} t (mulH {Y} (finχ {Y} (addX (intL {X} {Y} s (posT f)) (intL {X} {Y} s (negT f)))) (intL {X} {Y} s (u f)))
        ≈ ∫ᴹ {XY} (prodPre {X} {Y} s t) (u f)
    ∫-cut s t f i u = trans (∫-fin-cut {Y} t _ _ (bnd-sum s t f i)) (sym (∫-prod {X} {Y} s t (u f)))

    Int-inner : ∀ s t (f : SgT XY) → Int {XY} (prodPre {X} {Y} s t) f → Int {Y} t (innerT s f)
    Int-inner s t f i = bnd≈ {Y} (∫-cut s t f i posT) (proj₁ i) , bnd≈ {Y} (∫-cut s t f i negT) (proj₂ i)

    Ex-fubini : ∀ s t (f : SgT XY) (i : Int {XY} (prodPre {X} {Y} s t) f) →
      Ex {XY} (prodPre {X} {Y} s t) f i ≃ Ex {Y} t (innerT s f) (Int-inner s t f i)
    Ex-fubini s t f i = mk≃ 0# Is-0 (+-cong (+-cong (sym (∫-cut s t f i posT)) (∫-cut s t f i negT)) refl)

    -- f(x) g(y)
    infixl 7 _⊗T_
    _⊗T_ : SgT X → SgT Y → SgT XY
    f ⊗T g = (f ∘T fstQ S) *T (g ∘T sndQ S)

    -- the parts of f ⊗ g integrate to the cross products of the parts' integrals
    ∫⊗⁺ : ∀ s t (f : SgT X) (g : SgT Y) → ∫ᴹ {XY} (prodPre {X} {Y} s t) (posT (f ⊗T g)) ≈
      ∫ᴹ {X} s (posT f) * ∫ᴹ {Y} t (posT g) + ∫ᴹ {X} s (negT f) * ∫ᴹ {Y} t (negT g)
    ∫⊗⁺ s t f g = trans (∫ᴹ-addX {XY} (prodPre {X} {Y} s t) _ _)
      (+-cong (∫-rect {X} {Y} s t (posT f) (posT g))
        (∫-rect {X} {Y} s t (negT f) (negT g)))

    ∫⊗⁻ : ∀ s t (f : SgT X) (g : SgT Y) → ∫ᴹ {XY} (prodPre {X} {Y} s t) (negT (f ⊗T g)) ≈
      ∫ᴹ {X} s (posT f) * ∫ᴹ {Y} t (negT g) + ∫ᴹ {X} s (negT f) * ∫ᴹ {Y} t (posT g)
    ∫⊗⁻ s t f g = trans (∫ᴹ-addX {XY} (prodPre {X} {Y} s t) _ _)
      (+-cong (∫-rect {X} {Y} s t (posT f) (negT g))
        (∫-rect {X} {Y} s t (negT f) (posT g)))

    Int-⊗ : ∀ s t (f : SgT X) (g : SgT Y) → Int {X} s f → Int {Y} t g → Int {XY} (prodPre {X} {Y} s t) (f ⊗T g)
    Int-⊗ s t f g (i⁺ , i⁻) (j⁺ , j⁻) =
      bnd≈ {XY} (∫⊗⁺ s t f g) (Is-+ {_} {_} (Is-* {_} {_} i⁺ j⁺) (Is-* {_} {_} i⁻ j⁻)) ,
      bnd≈ {XY} (∫⊗⁻ s t f g) (Is-+ {_} {_} (Is-* {_} {_} i⁺ j⁻) (Is-* {_} {_} i⁻ j⁺))

    Ex-⊗ : ∀ s t (f : SgT X) (g : SgT Y) (i : Int {X} s f) (j : Int {Y} t g) →
      Ex {XY} (prodPre {X} {Y} s t) (f ⊗T g) (Int-⊗ s t f g i j) ≃ Ex {X} s f i *S Ex {Y} t g j
    Ex-⊗ s t f g i j = mk≃ 0# Is-0 (trans (+-cong (+-cong (∫⊗⁺ s t f g) refl) refl)
      (+-cong (+-cong refl (sym (∫⊗⁻ s t f g))) refl))
