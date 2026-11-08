{-# OPTIONS --safe --without-K #-}

-- Independence of random variables (independence means the law of the tuple is the product of the laws; this is a strong definition, with `Ex-indep`/`Var-indep` as consequences).  On a probability space P on Ω (`Continuous/Monad`), a random
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
module QBS.Continuous.Independence where

open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
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
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.Dominated using (module Dominated)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.FinProdPair using (module FinProdPair)
open import QBS.Continuous.IndepAlg using (module IndepAlg)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)

module Independence (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; _+_; 0#; 1#; refl; sym; trans; *-cong; +-cong)
  open Bounded A using (_≃_; _+S_; _*S_; mk≃; finite)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-+; Is-*; Is-0)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; _≈ᴹ_; mapM; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Product (lemOf lem₁) using (prodPre; ∫-rect; prod-cong)
  open FatouAux lem₁ using (∫ᴹ-addX)
  open ProdMap (lemOf lem₁) using (mapM-comp; mapM-cong; mapM-ext; _×H_; map-prod; swapQ; swapM)
  open SignedTest lem₁ using (SgT; posT; negT; _∘T_; _*T_; _+T_)
  open SignedExpect lem₁ using (Int; Ex; bnd≈; Ex-cong; Ex-+; Int-+)
  open Bounded A using (≃-refl; ≃-trans; +S-cong; -S-cong; *S-cong)
  open SignedVarAlg lem₁ using (Int-via)
  open SignedVar lem₁ using (Int₂; Var)
  open Dominated lem₁ using (prob-mass)
  open IndepAlg lem₁ using (sqadd-eq; sqadd-sums; R-var)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ; proj-tuple)
  open FinProdPair lem₁ using (pairⁿ)
  open QBS
  open Hom

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- the law of X : Ω ⇒ Y
    law : ∀ {Y : QBS S} → Hom S Ω Y → C.Pre (XW Y)
    law {Y} X = mapM {Ω} {Y} X (ιPre {Ω} P)

    Indep₂ : ∀ {Y Z : QBS S} → Hom S Ω Y → Hom S Ω Z → Set₁
    Indep₂ {Y} {Z} X W = _≈ᴹ_ {_×Q_ S Y Z} (law (pairQ S {Ω} {Y} {Z} X W)) (prodPre {Y} {Z} (law X) (law W))

    Indep : ∀ n (Ys : Fin n → QBS S) → (∀ i → Hom S Ω (Ys i)) → Set₁
    Indep n Ys Xs = _≈ᴹ_ {ΠQ n Ys} (law (tupleQ n Ys Xs)) (prodⁿ n Ys (λ i → law (Xs i)))

    Indep₂-sym : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → Indep₂ W X
    Indep₂-sym {Y} {Z} X W d f = trans
      (mapM-ext {Ω} {_×Q_ S Z Y} (pairQ S {Ω} {Z} {Y} W X) (_∘H_ S (swapQ {Y} {Z}) (pairQ S {Ω} {Y} {Z} X W)) (ιPre {Ω} P)
        (λ ω → Setoid.refl (Carrier (_×Q_ S Z Y))) f)
      (trans (sym (mapM-comp {Ω} {_×Q_ S Y Z} {_×Q_ S Z Y} (pairQ S {Ω} {Y} {Z} X W) (swapQ {Y} {Z}) (ιPre {Ω} P) f))
        (trans (mapM-cong {_×Q_ S Y Z} {_×Q_ S Z Y} (swapQ {Y} {Z}) d f) (swapM {Y} {Z} (law X) (law W) f)))

    Indep₂-map : ∀ {Y Z Y′ Z′ : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (f : Hom S Y Y′) (g : Hom S Z Z′) →
      Indep₂ X W → Indep₂ (_∘H_ S f X) (_∘H_ S g W)
    Indep₂-map {Y} {Z} {Y′} {Z′} X W f g d h = trans
      (mapM-ext {Ω} {_×Q_ S Y′ Z′} (pairQ S {Ω} {Y′} {Z′} (_∘H_ S f X) (_∘H_ S g W))
        (_∘H_ S (_×H_ {Y} {Z} {Y′} {Z′} f g) (pairQ S {Ω} {Y} {Z} X W)) (ιPre {Ω} P) (λ ω → Setoid.refl (Carrier (_×Q_ S Y′ Z′))) h)
      (trans (sym (mapM-comp {Ω} {_×Q_ S Y Z} {_×Q_ S Y′ Z′} (pairQ S {Ω} {Y} {Z} X W) (_×H_ {Y} {Z} {Y′} {Z′} f g) (ιPre {Ω} P) h))
        (trans (mapM-cong {_×Q_ S Y Z} {_×Q_ S Y′ Z′} (_×H_ {Y} {Z} {Y′} {Z′} f g) d h)
          (trans (map-prod {Y} {Z} {Y′} {Z′} f g (law X) (law W) h)
            (prod-cong {Y′} {Z′} (mapM-comp {Ω} {Y} {Y′} X f (ιPre {Ω} P)) (mapM-comp {Ω} {Z} {Z′} W g (ιPre {Ω} P)) h))))

    -- the law of a random variable is a probability
    mass : ∀ {Y : QBS S} (X : Hom S Ω Y) → ∫ᴹ {Y} (law X) (constW {Y} 1#) ≈ 1#
    mass {Y} X = trans (∫ᴹ-map {Ω} {Y} X (ιPre {Ω} P) (constW {Y} 1#))
      (trans (∫ᴹ-cong {Ω} (ιPre {Ω} P) {_∘H_ S (constW {Y} 1#) X} {constW {Ω} 1#} (λ _ → refl)) (prob-mass {Ω} P 1#))

    Indep-pair : ∀ n Ys (Xs : ∀ i → Hom S Ω (Ys i)) → Indep n Ys Xs → ∀ i j → i ≢ j → Indep₂ (Xs i) (Xs j)
    Indep-pair n Ys Xs d i j ne f = trans
      (mapM-ext {Ω} {_×Q_ S (Ys i) (Ys j)} (pairQ S {Ω} {Ys i} {Ys j} (Xs i) (Xs j))
        (_∘H_ S (pairQ S (projQ n Ys i) (projQ n Ys j)) (tupleQ n Ys Xs)) (ιPre {Ω} P)
        (λ ω → Setoid.sym (Carrier (Ys i)) (proj-tuple n Ys Xs i ω)
             , Setoid.sym (Carrier (Ys j)) (proj-tuple n Ys Xs j ω)) f)
      (trans (sym (mapM-comp {Ω} {ΠQ n Ys} {_×Q_ S (Ys i) (Ys j)} (tupleQ n Ys Xs)
        (pairQ S (projQ n Ys i) (projQ n Ys j)) (ιPre {Ω} P) f))
        (trans (mapM-cong {ΠQ n Ys} {_×Q_ S (Ys i) (Ys j)} (pairQ S (projQ n Ys i) (projQ n Ys j)) d f)
          (pairⁿ n Ys (λ k → law (Xs k)) (λ k → mass (Xs k)) i j ne f)))

    -- factorisation
    ∫-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (g : Hom S Y WQ) (h : Hom S Z WQ) →
      ∫ᴹ {Ω} (ιPre {Ω} P) (mulH {Ω} (_∘H_ S g X) (_∘H_ S h W))
        ≈ ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S g X) * ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S h W)
    ∫-indep {Y} {Z} X W d g h =
      trans (∫ᴹ-cong {Ω} (ιPre {Ω} P) {mulH {Ω} (_∘H_ S g X) (_∘H_ S h W)} {_∘H_ S G (pairQ S {Ω} {Y} {Z} X W)} (λ ω → refl))
      (trans (sym (∫ᴹ-map {Ω} {_×Q_ S Y Z} (pairQ S {Ω} {Y} {Z} X W) (ιPre {Ω} P) G))
      (trans (d G) (trans (∫-rect {Y} {Z} (law X) (law W) g h)
        (*-cong (∫ᴹ-map {Ω} {Y} X (ιPre {Ω} P) g) (∫ᴹ-map {Ω} {Z} W (ιPre {Ω} P) h)))))
      where G = mulH {_×Q_ S Y Z} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S))

    -- the parts of the product (u ∘ X)(v ∘ W) integrate to cross products
    ∫*⁺ : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      ∫ᴹ {Ω} (ιPre {Ω} P) (posT ((u ∘T X) *T (v ∘T W))) ≈
      ∫ᴹ {Ω} (ιPre {Ω} P) (posT (u ∘T X)) * ∫ᴹ {Ω} (ιPre {Ω} P) (posT (v ∘T W))
        + ∫ᴹ {Ω} (ιPre {Ω} P) (negT (u ∘T X)) * ∫ᴹ {Ω} (ιPre {Ω} P) (negT (v ∘T W))
    ∫*⁺ X W d u v = trans (∫ᴹ-addX {Ω} (ιPre {Ω} P) _ _)
      (+-cong (∫-indep X W d (posT u) (posT v)) (∫-indep X W d (negT u) (negT v)))

    ∫*⁻ : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      ∫ᴹ {Ω} (ιPre {Ω} P) (negT ((u ∘T X) *T (v ∘T W))) ≈
      ∫ᴹ {Ω} (ιPre {Ω} P) (posT (u ∘T X)) * ∫ᴹ {Ω} (ιPre {Ω} P) (negT (v ∘T W))
        + ∫ᴹ {Ω} (ιPre {Ω} P) (negT (u ∘T X)) * ∫ᴹ {Ω} (ιPre {Ω} P) (posT (v ∘T W))
    ∫*⁻ X W d u v = trans (∫ᴹ-addX {Ω} (ιPre {Ω} P) _ _)
      (+-cong (∫-indep X W d (posT u) (negT v)) (∫-indep X W d (negT u) (posT v)))

    Int-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      Int {Ω} (ιPre {Ω} P) (u ∘T X) → Int {Ω} (ιPre {Ω} P) (v ∘T W) → Int {Ω} (ιPre {Ω} P) ((u ∘T X) *T (v ∘T W))
    Int-indep X W d u v (i⁺ , i⁻) (j⁺ , j⁻) =
      bnd≈ {Ω} (∫*⁺ X W d u v) (Is-+ {_} {_} (Is-* {_} {_} i⁺ j⁺) (Is-* {_} {_} i⁻ j⁻)) ,
      bnd≈ {Ω} (∫*⁻ X W d u v) (Is-+ {_} {_} (Is-* {_} {_} i⁺ j⁻) (Is-* {_} {_} i⁻ j⁺))

    Ex-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (d : Indep₂ X W) (u : SgT Y) (v : SgT Z)
      (i : Int {Ω} (ιPre {Ω} P) (u ∘T X)) (j : Int {Ω} (ιPre {Ω} P) (v ∘T W)) →
      Ex {Ω} (ιPre {Ω} P) ((u ∘T X) *T (v ∘T W)) (Int-indep X W d u v i j)
        ≃ Ex {Ω} (ιPre {Ω} P) (u ∘T X) i *S Ex {Ω} (ιPre {Ω} P) (v ∘T W) j
    Ex-indep X W d u v i j = mk≃ 0# Is-0 (trans (+-cong (+-cong (∫*⁺ X W d u v) refl) refl)
      (+-cong (+-cong refl (sym (∫*⁻ X W d u v))) refl))

    -- the square of a sum of independent integrable tests
    Int-sq : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      Int {Ω} (ιPre {Ω} P) (u ∘T X) → Int {Ω} (ιPre {Ω} P) ((u ∘T X) *T (u ∘T X)) →
      Int {Ω} (ιPre {Ω} P) (v ∘T W) → Int {Ω} (ιPre {Ω} P) ((v ∘T W) *T (v ∘T W)) →
      Int {Ω} (ιPre {Ω} P) (((u ∘T X) +T (v ∘T W)) *T ((u ∘T X) +T (v ∘T W)))
    Int-sq X W d u v i i₂ j j₂ = Int-via {Ω} (ιPre {Ω} P) _ _
      (Int-+ {Ω} (ιPre {Ω} P) (Int-+ {Ω} (ιPre {Ω} P) i₂ fg) (Int-+ {Ω} (ιPre {Ω} P) fg j₂)) (sqadd-sums (u ∘T X) (v ∘T W))
      where fg = Int-indep X W d u v i j

    -- variances add
    Int₂-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) → Indep₂ X W → ∀ (u : SgT Y) (v : SgT Z) →
      Int₂ {Ω} P (u ∘T X) → Int₂ {Ω} P (v ∘T W) → Int₂ {Ω} P ((u ∘T X) +T (v ∘T W))
    Int₂-indep X W d u v (i , i₂) (j , j₂) = Int-+ {Ω} (ιPre {Ω} P) i j , Int-sq X W d u v i i₂ j j₂

    Var-indep : ∀ {Y Z : QBS S} (X : Hom S Ω Y) (W : Hom S Ω Z) (d : Indep₂ X W) (u : SgT Y) (v : SgT Z)
      (i : Int₂ {Ω} P (u ∘T X)) (j : Int₂ {Ω} P (v ∘T W)) →
      Var {Ω} P ((u ∘T X) +T (v ∘T W)) (Int₂-indep X W d u v i j) ≃ Var {Ω} P (u ∘T X) i +S Var {Ω} P (v ∘T W) j
    Var-indep X W d u v (i , i₂) (j , j₂) = ≃-trans
      (+S-cong (≃-trans (Ex-cong {Ω} E _ _ _ IG (sqadd-eq f g))
        (≃-trans (Ex-+ {Ω} E _ _ _ _) (+S-cong (Ex-+ {Ω} E _ _ _ _) (Ex-+ {Ω} E _ _ _ _))))
        (-S-cong (*S-cong ea ea)))
      (≃-trans (+S-cong (+S-cong (+S-cong ≃-refl (Ex-indep X W d u v i j)) (+S-cong (Ex-indep X W d u v i j) ≃-refl)) ≃-refl)
        (R-var _ _ _ _))
      where E = ιPre {Ω} P
            f = u ∘T X
            g = v ∘T W
            IG = Int-+ {Ω} E (Int-+ {Ω} E i₂ (Int-indep X W d u v i j)) (Int-+ {Ω} E (Int-indep X W d u v i j) j₂)
            ea = Ex-+ {Ω} E f g i j
