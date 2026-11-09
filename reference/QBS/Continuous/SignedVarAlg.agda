{-# OPTIONS --safe --without-K #-}

-- Pointwise and ring identities for the variance of signed tests (used by
-- `SignedVar`).
--   * the expansion `Sq f c = f² − 2c f + c²` of `(f − c)²` as a signed test, with `cen-eq` ((f − c)² ≐ Sq f c) and
--     `cen-bnd` (the sums of the two parts agree pointwise), likewise `scl-eq`, `scl-bnd` for (c f)² and c² f²;
--   * `Int-via`: integrability of F from that of S when F⁺ + F⁻ ≈ S⁺ + S⁻ pointwise (by `Int-dom`);
--   * the three identities in the signed ring `R-cen`, `R-shift`, `R-scale` behind `Var-cen`, `Var-shift`, `Var-scale`.
-- Route: parts of signed sums and products are polynomials in the parts (`_⊕_`, `_⊗_`, `ng` mirror `_+S_`, `_*S_`, `-S_`),
-- so every identity is one `solve` of the natural-coefficient ring solver (cross-added form, witness 0).
module QBS.Continuous.SignedVarAlg where

open import Data.Product.Base using (_×_; _,_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)
open import QBS.Continuous.SignedVarRing using (module Ring)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedVarAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; 1#; +-identityʳ; refl; trans; sym; ≤-reflexive; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; _*S_; -S_; 1S; mk≃; finite; ≃-refl; ≃-sym; ≃-trans;
    +S-cong; -S-cong; *S-congˡ; +S-assoc;
    *S-distribˡ; *S-distribʳ; *S-identityˡ)
  open Sg
  open SubSemiring finite using (Is-+; Is-0)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SFinite (lemOf lem₁) using (XW; module C)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _≐_; _+T_; _*T_; scaleT; constT)
  open SignedExpect lem₁ using (Int; Int-dom; bnd≈; ∫+)
  open QBS
  open Hom

  -- (f − c)² expanded: f² − 2c f + c²
  cen : ∀ {X : QBS S} → SgT X → Sg → SgT X
  cen f c = f +T constT (-S c)

  Sq : ∀ {X : QBS S} → SgT X → Sg → SgT X
  Sq f c = (f *T f +T scaleT (-S (c +S c)) f) +T constT (c *S c)

  open Ring commutativeSemiring using (Pa; _⊕ᵃ_; _⊗ᵃ_; ngᵃ; crossᵃ; sumsᵃ; cenA; sqA; sclA; sclA′;
    cen-alg; cen-sums; scl-alg; scl-sums; R1-alg; RS-alg; SQ-alg; neg-mul-alg; mul-neg-alg; L1ᵃ; LSᵃ; RVᵃ; SQᵃ; SQ′ᵃ)

  fromCross : ∀ {x y : Sg} → pos x + neg y ≈ pos y + neg x → x ≃ y
  fromCross h = mk≃ 0# Is-0 (trans (+-identityʳ _) (trans h (sym (+-identityʳ _))))

  neg-mul : ∀ x y → (-S x) *S y ≃ -S (x *S y)
  neg-mul x y = fromCross (neg-mul-alg (pos x) (neg x) (pos y) (neg y))

  mul-neg : ∀ x y → x *S (-S y) ≃ -S (x *S y)
  mul-neg x y = fromCross (mul-neg-alg (pos x) (neg x) (pos y) (neg y))

  R-cen : ∀ m₁ m₂ → ((m₂ +S -S ((m₁ +S m₁) *S m₁)) +S m₁ *S m₁) ≃ m₂ +S -S (m₁ *S m₁)
  R-cen m₁ m₂ = fromCross (R1-alg (pos m₁) (neg m₁) (pos m₂) (neg m₂))

  -- (f + c)² − 2 (−c) m + c² − (m + c)² = −m²
  R-sh : ∀ m c → ((-S (((-S c) +S (-S c)) *S m) +S (-S c) *S (-S c)) +S -S ((m +S c) *S (m +S c))) ≃ -S (m *S m)
  R-sh m c = fromCross (RS-alg (pos m) (neg m) (pos c) (neg c))

  R-shift : ∀ m₁ m₂ c →
    ((m₂ +S -S (((-S c) +S (-S c)) *S m₁)) +S (-S c) *S (-S c)) +S -S ((m₁ +S c) *S (m₁ +S c)) ≃ m₂ +S -S (m₁ *S m₁)
  R-shift m₁ m₂ c =
    ≃-trans (+S-cong (+S-assoc _ _ _) ≃-refl) (≃-trans (+S-assoc _ _ _) (+S-cong ≃-refl (R-sh m₁ c)))

  R-scale : ∀ m₁ m₂ c → (c *S c) *S m₂ +S -S ((c *S m₁) *S (c *S m₁)) ≃ (c *S c) *S (m₂ +S -S (m₁ *S m₁))
  R-scale m₁ m₂ c = ≃-sym (≃-trans (*S-distribˡ (c *S c) m₂ (-S (m₁ *S m₁)))
    (+S-cong ≃-refl (≃-trans (mul-neg (c *S c) (m₁ *S m₁)) (-S-cong (≃-sym sq)))))
    where sq = fromCross (SQ-alg (pos m₁) (neg m₁) (pos c) (neg c))

  -- (1 + 1) c = c + c, and (−(c + c)) e = −(((1 + 1) c) e)
  two-c : ∀ c → (1S +S 1S) *S c ≃ c +S c
  two-c c = ≃-trans (*S-distribʳ c 1S 1S) (+S-cong (*S-identityˡ c) (*S-identityˡ c))

  bridge : ∀ c e → (-S (c +S c)) *S e ≃ -S (((1S +S 1S) *S c) *S e)
  bridge c e = ≃-trans (neg-mul (c +S c) e) (-S-cong (≃-sym (*S-congˡ e (two-c c))))

  -- parts of tests and of signed constants as pairs; the operations on tests act on them as on `Pa` (all by `refl`)
  ⟦_⟧ : ∀ {X : QBS S} → SgT X → ∣ X ∣ → Pa
  ⟦ f ⟧ x = at⁺ f x , at⁻ f x

  pr : Sg → Pa
  pr c = pos c , neg c

  addP : ∀ {X : QBS S} (f g : SgT X) x → ⟦ f +T g ⟧ x ≡ ⟦ f ⟧ x ⊕ᵃ ⟦ g ⟧ x
  addP f g x = ≡.refl

  mulP : ∀ {X : QBS S} (f g : SgT X) x → ⟦ f *T g ⟧ x ≡ ⟦ f ⟧ x ⊗ᵃ ⟦ g ⟧ x
  mulP f g x = ≡.refl

  sclT : ∀ {X : QBS S} (c : Sg) (f : SgT X) x → ⟦ scaleT c f ⟧ x ≡ pr c ⊗ᵃ ⟦ f ⟧ x
  sclT c f x = ≡.refl

  cstP : ∀ (X : QBS S) (c : Sg) (x : ∣ X ∣) → ⟦ constT {X} c ⟧ x ≡ pr c
  cstP X c x = ≡.refl

  prP : ∀ c d → pr (-S c) ≡ ngᵃ (pr c) × pr (c +S d) ≡ pr c ⊕ᵃ pr d × pr (c *S d) ≡ pr c ⊗ᵃ pr d
  prP c d = ≡.refl , ≡.refl , ≡.refl

  via-cross : ∀ {X : QBS S} {F G : SgT X} {P Q x} → ⟦ F ⟧ x ≡ P → ⟦ G ⟧ x ≡ Q → crossᵃ P Q →
    at⁺ F x + at⁻ G x ≈ at⁺ G x + at⁻ F x
  via-cross ≡.refl ≡.refl h = h

  via-sums : ∀ {X : QBS S} {F G : SgT X} {P Q x} → ⟦ F ⟧ x ≡ P → ⟦ G ⟧ x ≡ Q → sumsᵃ P Q →
    at⁺ F x + at⁻ F x ≈ at⁺ G x + at⁻ G x
  via-sums ≡.refl ≡.refl h = h

  -- pointwise facts for the tests
  module _ {X : QBS S} (f : SgT X) (c : Sg) where
    cen-l : ∀ x → ⟦ cen f c *T cen f c ⟧ x ≡ cenA (⟦ f ⟧ x) (pr c)
    cen-l x = ≡.trans (mulP _ _ x) (≡.cong₂ _⊗ᵃ_ e e)
      where e = ≡.trans (addP f (constT (-S c)) x) (≡.cong (⟦ f ⟧ x ⊕ᵃ_) (cstP X (-S c) x))

    cen-r : ∀ x → ⟦ Sq f c ⟧ x ≡ sqA (⟦ f ⟧ x) (pr c)
    cen-r x = ≡.trans (addP _ (constT (c *S c)) x) (≡.cong₂ _⊕ᵃ_ e (cstP X (c *S c) x))
      where d = -S (c +S c)
            e = ≡.trans (addP (f *T f) (scaleT d f) x) (≡.cong₂ _⊕ᵃ_ (mulP f f x) (sclT d f x))

    scl-l : ∀ x → ⟦ scaleT c f *T scaleT c f ⟧ x ≡ sclA (⟦ f ⟧ x) (pr c)
    scl-l x = ≡.trans (mulP _ _ x) (≡.cong₂ _⊗ᵃ_ (sclT c f x) (sclT c f x))

    scl-r : ∀ x → ⟦ scaleT (c *S c) (f *T f) ⟧ x ≡ sclA′ (⟦ f ⟧ x) (pr c)
    scl-r x = ≡.trans (sclT _ _ x) (≡.cong₂ _⊗ᵃ_ ≡.refl (mulP f f x))

    cen-eq : cen f c *T cen f c ≐ Sq f c
    cen-eq x = via-cross (cen-l x) (cen-r x) (cen-alg (at⁺ f x) (at⁻ f x) (pos c) (neg c))

    cen-bnd : ∀ x → at⁺ (cen f c *T cen f c) x + at⁻ (cen f c *T cen f c) x ≈ at⁺ (Sq f c) x + at⁻ (Sq f c) x
    cen-bnd x = via-sums (cen-l x) (cen-r x) (cen-sums (at⁺ f x) (at⁻ f x) (pos c) (neg c))

    scl-eq : (scaleT c f *T scaleT c f) ≐ scaleT (c *S c) (f *T f)
    scl-eq x = via-cross (scl-l x) (scl-r x) (scl-alg (at⁺ f x) (at⁻ f x) (pos c) (neg c))

    scl-bnd : ∀ x → at⁺ (scaleT c f *T scaleT c f) x + at⁻ (scaleT c f *T scaleT c f) x
      ≈ at⁺ (scaleT (c *S c) (f *T f)) x + at⁻ (scaleT (c *S c) (f *T f)) x
    scl-bnd x = via-sums (scl-l x) (scl-r x) (scl-sums (at⁺ f x) (at⁻ f x) (pos c) (neg c))

  -- integrability from a pointwise bound by the sum of the parts of an integrable test
  Int-via : ∀ {X : QBS S} (p : C.Pre (XW X)) (F G : SgT X) → Int p G →
    (∀ x → at⁺ F x + at⁻ F x ≈ at⁺ G x + at⁻ G x) → Int p F
  Int-via {X} p F G (i⁺ , i⁻) e = Int-dom p F (addX (posT G) (negT G))
    (bnd≈ {X} (∫+ {X} p (posT G) (negT G)) (Is-+ {_} {_} i⁺ i⁻)) (λ x → ≤-reflexive (e x))
