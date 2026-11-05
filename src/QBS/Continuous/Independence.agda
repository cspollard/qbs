{-# OPTIONS --safe --without-K #-}

-- Independence of random variables (plan 05, item 45).  On a probability space P on Ω (`Continuous/Monad`), a random
-- variable is a morphism X : Ω ⇒ Y and its law is the push-forward of ιPre P (`law`).
--   * `Indep₂ X W`: the joint law of (X, W) is ≈ᴹ the product of the laws (`Product.prodPre`); `Indep n Ys Xs`, mutual
--     independence of a family: the law of the tuple is the n-fold product of the laws (`FinProd.prodⁿ`);
--   * symmetry (`Indep₂-sym`), functions of independent variables are independent (`Indep₂-map`), mutual implies
--     pairwise (`Indep-pair`);
--   * factorisation ∫ g(X) h(W) ≈ ∫ g(X) · ∫ h(W) (`∫-indep`); for signed tests u, v integrability of the product
--     (`Int-indep`) and E[u(X) v(W)] ≃ E[u(X)] E[v(W)] (`Ex-indep`);
--   * variances add: Var(u(X) + v(W)) ≃ Var u(X) + Var v(W) (`Var-indep`, with `Int₂-indep`).
-- Independence is the strong form (equality of laws); factorisation on rectangles alone would need uniqueness of
-- measures from rectangles, which is not available.
-- Route: `SFinite.∫ᴹ-map` moves integrals to the joint law, then `Product.∫-rect`, `SignedFubini.Int-⊗`/`Ex-⊗`;
-- symmetry by `Product.∫-prod`/`∫-prod′`; pairwise from `FinProd.margⁿ`-style marginals of `prodⁿ` on two coordinates;
-- `Var-indep` from `SignedExpect.Ex-+` and `Ex-indep` (the cross terms cancel).
--   Skeleton: holes first.
module QBS.Continuous.Independence where

open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import QBS.Core
open import QBS.Limits using (_×Q_; pairQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.FinProd using (module FinProd)

module Independence (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_)
  open Bounded A using (_≃_; _+S_; _*S_)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Product (lemOf lem₁) using (prodPre)
  open SignedTest lem₁ using (SgT; _∘T_; _*T_; _+T_)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Int₂; Var)
  open FinProd lem₁ using (ΠQ; tupleQ; prodⁿ)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- the law of X : Ω ⇒ Y
    law : ∀ {Y : QBS S} → Hom S Ω Y → C.Pre (XW Y)
    law {Y} X = mapM {Ω} {Y} X (ιPre {Ω} P)

    Indep₂ : ∀ {Y Z : QBS S} → Hom S Ω Y → Hom S Ω Z → Set₁
    Indep₂ {Y} {Z} X W = _≈ᴹ_ {_×Q_ S Y Z} (law (pairQ S {Ω} {Y} {Z} X W)) (prodPre {Y} {Z} (law X) (law W))

    Indep : ∀ n (Ys : Fin n → QBS S) → (∀ i → Hom S Ω (Ys i)) → Set₁
    Indep n Ys Xs = _≈ᴹ_ {ΠQ n Ys} (law (tupleQ n Ys Xs)) (prodⁿ n Ys (λ i → law (Xs i)))

    Indep₂-sym : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → Indep₂ W X
    Indep₂-sym = ?

    Indep₂-map : ∀ {Y Z Y′ Z′ : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (f : Hom S Y Y′) (g : Hom S Z Z′) →
      Indep₂ X W → Indep₂ (_∘H_ S f X) (_∘H_ S g W)
    Indep₂-map = ?

    Indep-pair : ∀ n Ys (Xs : ∀ i → Hom S Ω (Ys i)) → Indep n Ys Xs → ∀ i j → i ≢ j → Indep₂ (Xs i) (Xs j)
    Indep-pair = ?

    -- factorisation
    ∫-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (g : Hom S Y WQ) (h : Hom S Z WQ) →
      ∫ᴹ {Ω} (ιPre {Ω} P) (mulH {Ω} (_∘H_ S g X) (_∘H_ S h W))
        ≈ ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S g X) * ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S h W)
    ∫-indep = ?

    Int-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      Int {Ω} (ιPre {Ω} P) (u ∘T X) → Int {Ω} (ιPre {Ω} P) (v ∘T W) → Int {Ω} (ιPre {Ω} P) ((u ∘T X) *T (v ∘T W))
    Int-indep = ?

    Ex-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (d : Indep₂ X W) (u : SgT Y) (v : SgT Z)
      (i : Int {Ω} (ιPre {Ω} P) (u ∘T X)) (j : Int {Ω} (ιPre {Ω} P) (v ∘T W)) →
      Ex {Ω} (ιPre {Ω} P) ((u ∘T X) *T (v ∘T W)) (Int-indep X W d u v i j)
        ≃ Ex {Ω} (ιPre {Ω} P) (u ∘T X) i *S Ex {Ω} (ιPre {Ω} P) (v ∘T W) j
    Ex-indep = ?

    -- variances add
    Int₂-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      Int₂ {Ω} P (u ∘T X) → Int₂ {Ω} P (v ∘T W) → Int₂ {Ω} P ((u ∘T X) +T (v ∘T W))
    Int₂-indep = ?

    Var-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (d : Indep₂ X W) (u : SgT Y) (v : SgT Z)
      (i : Int₂ {Ω} P (u ∘T X)) (j : Int₂ {Ω} P (v ∘T W)) →
      Var {Ω} P ((u ∘T X) +T (v ∘T W)) (Int₂-indep X W d u v i j) ≃ Var {Ω} P (u ∘T X) i +S Var {Ω} P (v ∘T W) j
    Var-indep = ?
