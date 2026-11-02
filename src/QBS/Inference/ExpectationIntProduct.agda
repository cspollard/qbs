{-# OPTIONS --safe --without-K #-}

-- Independence for integrable (possibly unbounded) signed tests against the product measure `p ⊗ᵖ q`
-- (`Inference/ExpectationProduct`), extending `E-at-⊗` beyond bounded tests.
--
--   * `J-join`: for `P : Pre (TQ X)`, `J (joinPre P) h ≈ J P Φ` whenever `J (P r) h ≈ Φ r` pointwise (Tonelli for
--     the kernel underlying `joinPre`: `J-bind`, `J-push` and `J-resp∞`, the unbounded analogue of `∫-join`);
--   * `J-⊠`: for unbounded `u v ≥ 0`, `J (p ⊗ᵖ q) (u·v) ≈ J p u * J q v`, from `J-join` and `J-scale` (`J-σ`: against
--     `σPre (x , q)` it is `u x * J q v`);
--   * `J-prodH`, `f ⊗I g : ITest (p ⊗ᵖ q)` with parts `f⁺g⁺ + f⁻g⁻` and `f⁺g⁻ + f⁻g⁺`, finite by `J-⊠`;
--   * `E-atᴵ-⊗ : E-atᴵ (p ⊗ᵖ q) (f ⊗I g) ≃ E-atᴵ p f *S E-atᴵ q g`.
module QBS.Inference.ExpectationIntProduct where

open import Level using (lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Param using (module Param)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S; mergeR; merge-evens; merge-odds)
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.SignedTests using (module SignedTests)
import QBS.Inference.ExpectationInt as EI
import QBS.Inference.ExpectationProduct as EP

module ExpectationIntProduct (lem₁ : LEM₁) where
  open JParam (lemOf lem₁) using (A; J; J-cong; J-add; J-scale; J-push)
  open Meas (lemOf lem₁) using (Meas; Meas-⊕; Meas-⊗; Meas-const; Meas-pre)
  open Tonelli (lemOf lem₁) using (Meas-J; J-bind)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; *-comm)
  open Bounded A using (Sg; Bnd; finite; _≃_; mk≃; _*S_)
  open SignedTests (lemOf lem₁) using (CutQ)
  module P₁ = Param A (lemOf lem₁) mergeC measurable-merge₁ Cyl-rect
  open Continuous A (lemOf lem₁) probClass using (Pre; _≈ᵖ_; mapPre; joinPre; TQ; Wit; sec; sec-random; mk)
  open Strength A (lemOf lem₁) probClass using (σPre)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ; J-resp∞)
  open EP.ExpectationProduct lem₁ using (prodH; σq; _⊗ᵖ_)
  open Pre
  open ITest
  open QBS using (∣_∣)

  -- the pulled-back (possibly infinite) integral of a test against a pre-measure
  Jp : ∀ {X : QBS S} → Pre X → Hom S X CutQ → ∣A∣
  Jp p h = J (m p) (λ r → Hom.map h ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random h (α-random p))

  ----------------------------------------------------------------------------
  -- Tonelli for `joinPre`

  module JJ {X : QBS S} (P : Pre (TQ X)) (h : Hom S X CutQ) where
    w : Wit _≈ᵖ_ (α P ⟨$⟩_)
    w = α-random P

    g : R₁ → _
    g = Wit.g w

    Ψ : R₁ → ∣A∣
    Ψ r = Hom.map h ⟨$⟩ (α (joinPre P) ⟨$⟩ r)

    mΨ = Hom.map-random h (α-random (joinPre P))

    kp : R₁ → Pre X
    kp r = mk (sec (Wit.a w) r) (sec-random (Wit.a w) r) (g r) (Wit.g-pr w r)

    -- the section of the merged kernel at `r` integrates `h` to the `r`-th value of `α P`
    pw : ∀ r → J (P₁.pushMerge g r) Ψ mΨ ≈ Jp (α P ⟨$⟩ r) h
    pw r = trans (J-push {mergeR r} (measurable-merge₁ (lower r)) (g r) {Ψ} mΨ
                    (Meas-pre {Ψ} {mergeR r} mΨ (measurable-merge₁ (lower r))))
             (trans (J-cong (g r) _ (Hom.map-random h (sec-random (Wit.a w) r))
                      (λ s → Func.cong (Hom.map h) (Func.cong (Hom.map (Wit.a w)) (merge-evens r s , merge-odds r s))))
               (sym (J-resp∞ {p = α P ⟨$⟩ r} {q = kp r} (Wit.w-eq w r) h)))

    kg = P₁.KernelOk-pushMerge {g} (Wit.g-ok w)
    mJ = Meas-J (P₁.pushMerge g) kg {Ψ} mΨ

  J-join : ∀ {X : QBS S} (P : Pre (TQ X)) (h : Hom S X CutQ) (Φ : R₁ → ∣A∣) (mΦ : Meas Φ) →
    (∀ r → Jp (α P ⟨$⟩ r) h ≈ Φ r) → Jp (joinPre P) h ≈ J (m P) Φ mΦ
  J-join P h Φ mΦ e = trans (J-bind (m P) (P₁.pushMerge g) kg {Ψ} mΨ mJ) (J-cong (m P) mJ mΦ (λ r → trans (pw r) (e r)))
    where open JJ P h

  ----------------------------------------------------------------------------
  -- the unsigned product law

  -- the product `u(x) v(y)` of two unbounded tests
  mulX : ∀ {X Y : QBS S} → Hom S X CutQ → Hom S Y CutQ → Hom S (_×Q_ S X Y) CutQ
  mulX u v = record
    { map = record
        { to = λ { (x , y) → (Hom.map u ⟨$⟩ x) * (Hom.map v ⟨$⟩ y) }
        ; cong = λ { (ex , ey) → *-cong (Func.cong (Hom.map u) ex) (Func.cong (Hom.map v) ey) } }
    ; map-random = λ { (rx , ry) → Meas-⊗ (Hom.map-random u rx) (Hom.map-random v ry) }
    }

  -- against `σPre (x , q)` the product is `u x` times the integral of `v`
  J-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre Y) (u : Hom S X CutQ) (v : Hom S Y CutQ) →
    Jp (σPre {X} {Y} (x , q)) (mulX u v) ≈ (Hom.map u ⟨$⟩ x) * Jp q v
  J-σ x q u v = trans
    (J-cong (m q) _ (Meas-⊗ (Meas-const (Hom.map u ⟨$⟩ x)) (Hom.map-random v (α-random q))) (λ s → refl))
    (J-scale (m q) (Hom.map u ⟨$⟩ x) (Hom.map-random v (α-random q)))

  J-⊠ : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) (u : Hom S X CutQ) (v : Hom S Y CutQ) →
    Jp (p ⊗ᵖ q) (mulX u v) ≈ Jp p u * Jp q v
  J-⊠ p q u v = trans
    (J-join (mapPre (σq q) p) (mulX u v) (λ r → Jp q v * (Hom.map u ⟨$⟩ (α p ⟨$⟩ r)))
       (Meas-⊗ (Meas-const (Jp q v)) (Hom.map-random u (α-random p)))
       (λ r → trans (J-σ (α p ⟨$⟩ r) q u v) (*-comm _ _)))
    (trans (J-scale (m p) (Jp q v) (Hom.map-random u (α-random p))) (*-comm _ _))

  ----------------------------------------------------------------------------
  -- the product of integrable tests

  -- the integral of a part of the product test
  J-prodH : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) (u u′ : Hom S X CutQ) (v v′ : Hom S Y CutQ) →
    Jp (p ⊗ᵖ q) (prodH u u′ v v′) ≈ Jp p u * Jp q v + Jp p u′ * Jp q v′
  J-prodH p q u u′ v v′ = trans
    (J-cong (m (p ⊗ᵖ q)) _ (Meas-⊕ (Hom.map-random (mulX u v) (α-random (p ⊗ᵖ q)))
                                   (Hom.map-random (mulX u′ v′) (α-random (p ⊗ᵖ q)))) (λ r → refl))
    (trans (J-add (m (p ⊗ᵖ q)) (Hom.map-random (mulX u v) (α-random (p ⊗ᵖ q)))
                                (Hom.map-random (mulX u′ v′) (α-random (p ⊗ᵖ q))))
           (+-cong (J-⊠ p q u v) (J-⊠ p q u′ v′)))

  fin₄ : ∀ {a b c d : ∣A∣} → Bnd a → Bnd b → Bnd c → Bnd d → Bnd (a * b + c * d)
  fin₄ ha hb hc hd = SubSemiring.Is-+ finite (SubSemiring.Is-* finite ha hb) (SubSemiring.Is-* finite hc hd)

  infixl 7 _⊗I_
  _⊗I_ : ∀ {X Y : QBS S} {p : Pre X} {q : Pre Y} → ITest p → ITest q → ITest (p ⊗ᵖ q)
  _⊗I_ {p = p} {q} f g = record
    { pos = prodH (pos f) (neg f) (pos g) (neg g) ; neg = prodH (pos f) (neg f) (neg g) (pos g)
    ; pos-int = SubSemiring.Is-resp finite (sym (J-prodH p q (pos f) (neg f) (pos g) (neg g)))
                  (fin₄ (pos-int f) (pos-int g) (neg-int f) (neg-int g))
    ; neg-int = SubSemiring.Is-resp finite (sym (J-prodH p q (pos f) (neg f) (neg g) (pos g)))
                  (fin₄ (pos-int f) (neg-int g) (neg-int f) (pos-int g)) }

  -- independence
  E-atᴵ-⊗ : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) (f : ITest p) (g : ITest q) →
    E-atᴵ (p ⊗ᵖ q) (f ⊗I g) ≃ E-atᴵ p f *S E-atᴵ q g
  E-atᴵ-⊗ p q f g = mk≃ 0# (SubSemiring.Is-0 finite)
    (trans (+-cong (+-cong (J-prodH p q (pos f) (neg f) (pos g) (neg g)) refl) refl)
           (sym (+-cong (+-cong refl (J-prodH p q (pos f) (neg f) (neg g) (pos g))) refl)))
