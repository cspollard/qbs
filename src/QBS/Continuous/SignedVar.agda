{-# OPTIONS --safe --without-K #-}

-- Variance of a signed test under a probability distribution.
-- For P : Pre X, p = ιPre P and f with f and f² integrable (`Int₂`):
--   * `Var P f i = E[f²] − (E f)²` as a signed value;
--   * the centred test `cen f c = f − c`, its square is integrable (`Int-cen`), and
--     E[(f − c)²] ≃ E[f²] − 2c E f + c² (`Ex-cen`); with c = E f this is the variance (`Var-cen`);
--   * `Var-shift` (Var (f + c) ≃ Var f) and `Var-scale` (Var (c f) ≃ c² Var f), with `Int₂-shift`, `Int₂-scale`.
-- Route: (f − c)² ≐ f² − 2c f + c² (`SignedVarAlg.Sq`, pointwise identities by the ring solver on the parts), so
-- integrability is `SignedVarAlg.Int-via` (domination by the sum of the parts of the expansion, `Int-dom`) and the
-- expectation is `Ex-cong`, `Ex-+`, `Ex-scale`, `Ex-const` followed by an identity in the signed ring (`R-cen`, `R-shift`,
-- `R-scale`).  `Var-shift` is `Ex-cen` at −c (f + c = cen f (−c) by η for `Sg`).  `Var-cong` needs squares to respect `≐`,
-- also at points where a part is ∞ (`SignedSq.sq-cong`).
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
open import QBS.Continuous.SignedSq using (module SignedSq)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)

module SignedVar (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; 1S; ≃-refl; ≃-trans; +S-cong; -S-cong; *S-cong; *S-congˡ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; _≐_; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Ex; Ex-irr; Ex-cong; Ex-+; Ex-scale; Ex-const; Int-+; Int-scale; Int-const)
  open SignedSq lem₁ using (sq-cong)
  open SignedVarAlg lem₁ using (Sq; cen-eq; cen-bnd; scl-eq; scl-bnd; Int-via; R-cen; R-shift; R-scale; bridge; two-c)

  module _ {X : QBS S} (P : Pre X) where

    -- f and f² integrable
    Int₂ : SgT X → Set₁
    Int₂ f = Int (ιPre {X} P) f × Int (ιPre {X} P) (f *T f)

    -- E[f²] − (E f)²
    Var : ∀ (f : SgT X) → Int₂ f → Sg
    Var f (i , j) = Ex (ιPre {X} P) (f *T f) j +S -S (Ex (ιPre {X} P) f i *S Ex (ιPre {X} P) f i)

    private
      E = ιPre {X} P
      xirr = Ex-irr {X} E
      xcong = Ex-cong {X} E
      x+ = Ex-+ {X} E
      xscale = Ex-scale {X} E
      i+ = Int-+ {X} E
      iscale = Int-scale {X} E

    Var-irr : ∀ f (i j : Int₂ f) → Var f i ≃ Var f j
    Var-irr f i j = +S-cong (xirr (f *T f) (proj₂ i) (proj₂ j)) (-S-cong (*S-cong e e))
      where e = xirr f (proj₁ i) (proj₁ j)

    Var-cong : ∀ (f g : SgT X) (i : Int₂ f) (j : Int₂ g) → f ≐ g → Var f i ≃ Var g j
    Var-cong f g i j e = +S-cong (xcong (f *T f) (g *T g) (proj₂ i) (proj₂ j) (sq-cong e)) (-S-cong (*S-cong e′ e′))
      where e′ = xcong f g (proj₁ i) (proj₁ j) e

    -- the centred test f − c
    cen : SgT X → Sg → SgT X
    cen f c = f +T constT (-S c)

    -- the expansion f² − 2c f + c² is integrable
    Int-Sq : ∀ f c → Int₂ f → Int (ιPre {X} P) (Sq f c)
    Int-Sq f c (i , j) = i+ (i+ j (iscale (-S (c +S c)) i)) (Int-const P (c *S c))

    Int-cen : ∀ f c → Int₂ f → Int (ιPre {X} P) (cen f c *T cen f c)
    Int-cen f c ij = Int-via E (cen f c *T cen f c) (Sq f c) (Int-Sq f c ij) (cen-bnd f c)

    -- E[(f − c)²] ≃ E[f²] − 2c E f + c²
    Ex-cen : ∀ f c (ij : Int₂ f) →
      Ex (ιPre {X} P) (cen f c *T cen f c) (Int-cen f c ij)
        ≃ (Ex (ιPre {X} P) (f *T f) (proj₂ ij) +S -S (((1S +S 1S) *S c) *S Ex (ιPre {X} P) f (proj₁ ij))) +S c *S c
    Ex-cen f c ij = ≃-trans (xcong _ (Sq f c) (Int-cen f c ij) (Int-Sq f c ij) (cen-eq f c))
      (≃-trans (x+ _ _ _ (Int-const P (c *S c))) (+S-cong inner (Ex-const P (c *S c))))
      where k = -S (c +S c)
            inner = ≃-trans (x+ (f *T f) _ (proj₂ ij) (iscale k (proj₁ ij)))
              (+S-cong ≃-refl (≃-trans (xscale k f (proj₁ ij)) (bridge c _)))

    -- E[(f − E f)²] ≃ Var f
    Var-cen : ∀ f (ij : Int₂ f) →
      Ex (ιPre {X} P) (cen f (Ex (ιPre {X} P) f (proj₁ ij)) *T cen f (Ex (ιPre {X} P) f (proj₁ ij)))
        (Int-cen f (Ex (ιPre {X} P) f (proj₁ ij)) ij) ≃ Var f ij
    Var-cen f ij = ≃-trans (Ex-cen f _ ij)
      (≃-trans (+S-cong (+S-cong ≃-refl (-S-cong (*S-congˡ _ (two-c _)))) ≃-refl) (R-cen _ _))

    -- shifting and scaling
    Int₂-shift : ∀ f c → Int₂ f → Int₂ (f +T constT c)
    Int₂-shift f c (i , j) = i+ i (Int-const P c) , Int-cen f (-S c) (i , j)

    Var-shift : ∀ f c (ij : Int₂ f) → Var (f +T constT c) (Int₂-shift f c ij) ≃ Var f ij
    Var-shift f c ij = ≃-trans (+S-cong (≃-trans (Ex-cen f (-S c) ij)
      (+S-cong (+S-cong ≃-refl (-S-cong (*S-congˡ _ (two-c (-S c))))) ≃-refl)) (-S-cong (*S-cong ec ec))) (R-shift _ _ c)
      where ec = ≃-trans (x+ f (constT c) (proj₁ ij) (Int-const P c)) (+S-cong ≃-refl (Ex-const P c))

    Int₂-scale : ∀ f c → Int₂ f → Int₂ (scaleT c f)
    Int₂-scale f c (i , j) = iscale c i ,
      Int-via E (scaleT c f *T scaleT c f) (scaleT (c *S c) (f *T f)) (iscale (c *S c) j) (scl-bnd f c)

    Var-scale : ∀ f c (ij : Int₂ f) → Var (scaleT c f) (Int₂-scale f c ij) ≃ (c *S c) *S Var f ij
    Var-scale f c ij = ≃-trans (+S-cong sq (-S-cong (*S-cong ec ec))) (R-scale _ _ c)
      where ec = xscale c f (proj₁ ij)
            sq = ≃-trans (xcong _ (scaleT (c *S c) (f *T f)) _ (iscale (c *S c) (proj₂ ij)) (scl-eq f c))
                         (xscale (c *S c) _ (proj₂ ij))
