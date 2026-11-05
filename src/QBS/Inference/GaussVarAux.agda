{-# OPTIONS --safe --without-K #-}

-- Generic helpers for `GaussVar` (plan 03, "Information quantities"): signed tests with a vanishing part, and
-- push-forward of expectations.
--   * `norm-le`: a + d ≈ c + b with b ≈ 0 or a ≈ 0 gives a + b ≤ c + d; `Int-norm`: if f ≐ g with g integrable and one part
--     of f zero at every point, then f is integrable (`Int-dom` against g⁺ + g⁻);
--   * `idT-norm`, `sq-pos`, `sq-neg`: one part of `idT` vanishes at every point; (idT idT)⁺ = x², (idT idT)⁻ = 0;
--   * `∫-map`, `Int-map`, `Int-map⁻`, `Ex-map`, `Var-map`: for the image `mapPre h P`, E_{h P}[f] is E_P[f ∘ h] (and so
--     for the variance, f² ∘ h being (f ∘ h)² pointwise).
-- Route: `SFiniteIncl.ι-nat` and `SFinite.∫ᴹ-map` as in `GaussShift.∫-gaussμ`; everything else is pointwise.
module QBS.Inference.GaussVarAux where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SignedSq using (module SignedSq)
open import QBS.Inference.GaussReal using (module GaussReal)

module GaussVarAux (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; +-comm;
    +-identityˡ; +-identityʳ; zeroˡ; zeroʳ;
    ≤-trans; ≤-reflexive; ≤-+ʳ) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; mk≃; finite; 0S; _+S_; -S_; _*S_; ≃-trans; +S-cong; -S-cong; *S-cong; +S-identityˡ)
  open SubSemiring finite using (Is-0; Is-+)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-map; XW; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-nat)
  open FatouAux lem₁ using (addX)
  open RealLine lem₁ using (RQ)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; _*T_; _∘T_; constT; idT)
  open SignedExpect lem₁ using (Int; Ex; Ex-cong; Ex-+; Ex-const; Int-+; Int-const; Int-dom; bnd≈; ∫+)
  open SignedVar lem₁ using (Var; Int₂; Int₂-shift; Var-cong; Var-shift)
  open SignedSq lem₁ using (sq-cong)
  open GaussReal lem₁ using (Q2)
  open QBS
  open Hom

  -- a + b ≤ c + d from a + d ≈ c + b when a or b vanishes
  norm-le : ∀ {a b c d} → a + d ≈ c + b → (b ≈ 0# ⊎ a ≈ 0#) → a + b ≤ c + d
  norm-le {a} {b} {c} {d} e (inj₁ zb) = ≤-trans (≤-reflexive (trans (+-cong (refl {a}) zb) (+-identityʳ a)))
    (≤-trans (≤-+ʳ {a} {d}) (≤-trans (≤-reflexive (trans e (trans (+-cong (refl {c}) zb) (+-identityʳ c)))) (≤-+ʳ {c} {d})))
  norm-le {a} {b} {c} {d} e (inj₂ za) = ≤-trans (≤-reflexive (trans (+-cong za (refl {b})) (+-identityˡ b)))
    (≤-trans (≤-+ʳ {b} {c}) (≤-trans (≤-reflexive (trans (+-comm b c)
      (trans (sym e) (trans (+-cong za (refl {d})) (+-identityˡ d)))))
      (≤-trans (≤-+ʳ {d} {c}) (≤-reflexive (+-comm d c)))))

  Int-norm : ∀ {X : QBS S} (p : C.Pre (XW X)) (f g : SgT X) → Int p g → f ≐ g →
    (∀ x → at⁻ f x ≈ 0# ⊎ at⁺ f x ≈ 0#) → Int p f
  Int-norm {X} p f g (i⁺ , i⁻) e n = Int-dom p f (addX (posT g) (negT g))
    (bnd≈ {X} (∫+ {X} p (posT g) (negT g)) (Is-+ {_} {_} i⁺ i⁻)) (λ x → norm-le (e x) (n x))

  -- the identity test and its square
  idT-norm : ∀ w → at⁻ idT w ≈ 0# ⊎ at⁺ idT w ≈ 0#
  idT-norm (inj₁ x) = inj₁ refl
  idT-norm (inj₂ x) = inj₂ refl

  sq-pos : ∀ w → at⁺ (idT *T idT) w ≈ map Q2 ⟨$⟩ w
  sq-pos (inj₁ x) = trans (+-cong (refl {x * x}) (zeroˡ 0#)) (+-identityʳ (x * x))
  sq-pos (inj₂ x) = trans (+-cong (zeroˡ 0#) (refl {x * x})) (+-identityˡ (x * x))

  sq-neg : ∀ w → at⁻ (idT *T idT) w ≈ 0#
  sq-neg (inj₁ x) = trans (+-cong (zeroʳ x) (zeroˡ x)) (+-identityˡ 0#)
  sq-neg (inj₂ x) = trans (+-cong (zeroˡ x) (zeroʳ x)) (+-identityˡ 0#)

  -- push-forward
  module _ (h : Hom S RQ RQ) (P : C.Pre RQ) where
    ∫-map : ∀ f → ∫ᴹ {RQ} (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) f ≈ ∫ᴹ {RQ} (ιPre {RQ} P) (_∘H_ S f h)
    ∫-map f = trans (ι-nat {RQ} {RQ} h P f) (∫ᴹ-map {RQ} {RQ} h (ιPre {RQ} P) f)

    Int-map : ∀ f → Int (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) f → Int (ιPre {RQ} P) (f ∘T h)
    Int-map f (i⁺ , i⁻) = bnd≈ {RQ} (sym (∫-map (posT f))) i⁺ , bnd≈ {RQ} (sym (∫-map (negT f))) i⁻

    Int-map⁻ : ∀ f → Int (ιPre {RQ} P) (f ∘T h) → Int (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) f
    Int-map⁻ f (i⁺ , i⁻) = bnd≈ {RQ} (∫-map (posT f)) i⁺ , bnd≈ {RQ} (∫-map (negT f)) i⁻

    Ex-map : ∀ f i j → Ex (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) f i ≃ Ex (ιPre {RQ} P) (f ∘T h) j
    Ex-map f i j = mk≃ 0# Is-0 (+-cong (+-cong (∫-map (posT f)) (sym (∫-map (negT f)))) refl)

    -- the variance transfers, f² ∘ h being (f ∘ h)² pointwise
    Var-map : ∀ f (i : Int (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) f) (j : Int (ιPre {RQ} (C.mapPre {RQ} {RQ} h P)) (f *T f))
      (i′ : Int (ιPre {RQ} P) (f ∘T h)) (j′ : Int (ιPre {RQ} P) ((f ∘T h) *T (f ∘T h))) →
      Var (C.mapPre {RQ} {RQ} h P) f (i , j) ≃ Var P (f ∘T h) (i′ , j′)
    Var-map f i j i′ j′ = +S-cong (≃-trans (Ex-map (f *T f) j (Int-map (f *T f) j))
      (Ex-cong {RQ} (ιPre {RQ} P) ((f *T f) ∘T h) ((f ∘T h) *T (f ∘T h)) (Int-map (f *T f) j) j′ (λ x → refl)))
      (-S-cong (*S-cong e e))
      where e = Ex-map f i i′

  -- a ≈ b·0-style fact: a vanishing part kills the cross products
  sqz : ∀ {a b} → (b ≈ 0# ⊎ a ≈ 0#) → a * b + b * a ≈ 0#
  sqz {a} {b} (inj₁ zb) = trans (+-cong (trans (*-cong (refl {a}) zb) (zeroʳ a))
    (trans (*-cong zb (refl {a})) (zeroˡ a))) (+-identityˡ 0#)
  sqz {a} {b} (inj₂ za) = trans (+-cong (trans (*-cong za (refl {b})) (zeroˡ b))
    (trans (*-cong (refl {b}) za) (zeroʳ b))) (+-identityˡ 0#)

  -- the push-forward of a distribution with mean 0 and variance w under h, when idT ∘ h ≐ idT + c
  module _ (P : C.Pre RQ) (h : Hom S RQ RQ) (c : Sg) (ij0 : Int₂ {RQ} P idT) (sh : (idT ∘T h) ≐ (idT +T constT c)) where
    private
      E0 = ιPre {RQ} P
      G = C.mapPre {RQ} {RQ} h P
      ijc = Int₂-shift {RQ} P idT c ij0
      norm1 : ∀ x → at⁻ (idT ∘T h) x ≈ 0# ⊎ at⁺ (idT ∘T h) x ≈ 0#
      norm1 x = idT-norm (map h ⟨$⟩ x)

    i-idh : Int E0 (idT ∘T h)
    i-idh = Int-norm E0 (idT ∘T h) (idT +T constT c) (proj₁ ijc) sh norm1

    j-idh : Int E0 ((idT ∘T h) *T (idT ∘T h))
    j-idh = Int-norm E0 _ ((idT +T constT c) *T (idT +T constT c)) (proj₂ ijc) (sq-cong sh) (λ x → inj₁ (sqz (norm1 x)))

    map-id : Int (ιPre {RQ} G) idT
    map-id = Int-map⁻ h P idT i-idh

    map-sq : Int (ιPre {RQ} G) (idT *T idT)
    map-sq = Int-map⁻ h P (idT *T idT) (Int-norm E0 ((idT *T idT) ∘T h) ((idT +T constT c) *T (idT +T constT c))
      (proj₂ ijc) (λ x → sq-cong sh x) (λ x → inj₁ (sq-neg (map h ⟨$⟩ x))))

    map-Ex : Ex (ιPre {RQ} P) idT (proj₁ ij0) ≃ 0S → Ex (ιPre {RQ} G) idT map-id ≃ c
    map-Ex e0 = ≃-trans (Ex-map h P idT map-id i-idh) (≃-trans (Ex-cong {RQ} E0 (idT ∘T h) (idT +T constT c) i-idh (proj₁ ijc) sh)
      (≃-trans (Ex-+ {RQ} E0 idT (constT c) (proj₁ ij0) (Int-const P c)) (≃-trans (+S-cong e0 (Ex-const P c)) (+S-identityˡ c))))

    map-Var : ∀ {w} → Var P idT ij0 ≃ w → Var G idT (map-id , map-sq) ≃ w
    map-Var v0 = ≃-trans (Var-map h P idT map-id map-sq i-idh j-idh) (≃-trans
      (Var-cong P (idT ∘T h) (idT +T constT c) (i-idh , j-idh) ijc sh) (≃-trans (Var-shift P idT c ij0) v0))
