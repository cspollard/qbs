{-# OPTIONS --safe --without-K #-}

-- Signed tests: pairs of [0, ∞]-valued tests standing for f⁺ − f⁻ (plan 03, "Signed layer").
--   * `SgT X = (X ⇒ WQ) × (X ⇒ WQ)`, with parts `posT`, `negT` and pointwise values `at⁺`, `at⁻`;
--   * `f ≐ g`: f⁺ + g⁻ ≈ g⁺ + f⁻ pointwise; reflexive and symmetric, and transitive through a pointwise finite middle
--     (parts may be infinite pointwise, where the cross-added equality says nothing); chains of `≐` between integrable
--     tests go through the expectation instead (`SignedExpect.Ex-cong`);
--   * pointwise operations `_+T_`, `-T_`, `scaleT` (a signed constant), `_*T_`, `constT`, `fromW` (a nonnegative
--     test), precomposition `_∘T_`, and on the real line `idT` (x⁺ − x⁻) and `sqT = idT *T idT`;
--   * the bridge between the two QBSs of [0, ∞]: `toW : (X ⇒ CutQ) → (X ⇒ WQ)` and `toCut`, both the identity pointwise.
-- Route: everything is pointwise from `FatouAux.addX`, `SFiniteReweight.mulH`, `Weights.constW` and `_∘H_`; the bridge
-- because `CutQ` and `WQ` have the same carrier and the same random elements (`Meas`).  Transitivity of `≐` through a
-- finite middle is `trans-core`: add c + d (finite, `InfAlg.cancel-bnd`) to both sides.
module QBS.Continuous.SignedTest where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.InfAlg using (module InfAlg)

module SignedTest (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg)
  open Sg
  open Weights (lemOf lem₁) using (WQ; constW)
  open SignedTests (lemOf lem₁) using (CutQ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open FatouAux lem₁ using (addX)
  open RealLine lem₁ using (RQ; copairH)
  open QBS
  open Hom
  open InfAlg lem₁ using (cancel-bnd)
  open OmegaSemiring A using (refl; sym; trans; +-cong; +-comm; commutativeSemiring)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open import Relation.Binary.Reasoning.Setoid (OmegaSemiring.setoid A)
  open Bounded A using (finite)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-+)

  -- transitivity through a finite middle: a + d ≈ c + b and c + k ≈ e + d give a + k ≈ e + b
  trans-core : ∀ a b c d e k → Bnd c → Bnd d → a + d ≈ c + b → c + k ≈ e + d → a + k ≈ e + b
  trans-core a b c d e k bc bd p q = cancel-bnd {c + d} (Is-+ {c} {d} bc bd) (begin
    (c + d) + (a + k) ≈⟨ solve 6 (λ a b c d e k → (c :+ d) :+ (a :+ k) := (a :+ d) :+ (c :+ k)) refl a b c d e k ⟩
    (a + d) + (c + k) ≈⟨ +-cong p q ⟩
    (c + b) + (e + d) ≈⟨ solve 6 (λ a b c d e k → (c :+ b) :+ (e :+ d) := (c :+ d) :+ (e :+ b)) refl a b c d e k ⟩
    (c + d) + (e + b) ∎)

  add-cong-core : ∀ a b c d a′ b′ c′ d′ → a + b′ ≈ a′ + b → c + d′ ≈ c′ + d → (a + c) + (b′ + d′) ≈ (a′ + c′) + (b + d)
  add-cong-core a b c d a′ b′ c′ d′ p q = begin
    (a + c) + (b′ + d′) ≈⟨ solve 6 (λ a b′ c d′ x y → (a :+ c) :+ (b′ :+ d′) := (a :+ b′) :+ (c :+ d′)) refl a b′ c d′ a a ⟩
    (a + b′) + (c + d′) ≈⟨ +-cong p q ⟩
    (a′ + b) + (c′ + d) ≈⟨ solve 4 (λ a′ b c′ d → (a′ :+ b) :+ (c′ :+ d) := (a′ :+ c′) :+ (b :+ d)) refl a′ b c′ d ⟩
    (a′ + c′) + (b + d) ∎

  SgT : QBS S → Set₁
  SgT X = Hom S X WQ × Hom S X WQ

  posT negT : ∀ {X : QBS S} → SgT X → Hom S X WQ
  posT = proj₁
  negT = proj₂

  at⁺ at⁻ : ∀ {X : QBS S} → SgT X → ∣ X ∣ → ∣A∣
  at⁺ f x = map (posT f) ⟨$⟩ x
  at⁻ f x = map (negT f) ⟨$⟩ x

  -- both parts finite at every point
  FinT : ∀ {X : QBS S} → SgT X → Set₁
  FinT f = ∀ x → Bnd (at⁺ f x) × Bnd (at⁻ f x)

  infix 4 _≐_
  _≐_ : ∀ {X : QBS S} → SgT X → SgT X → Set₁
  f ≐ g = ∀ x → at⁺ f x + at⁻ g x ≈ at⁺ g x + at⁻ f x

  ≐-refl : ∀ {X : QBS S} {f : SgT X} → f ≐ f
  ≐-refl x = refl

  ≐-sym : ∀ {X : QBS S} {f g : SgT X} → f ≐ g → g ≐ f
  ≐-sym e x = sym (e x)

  ≐-trans : ∀ {X : QBS S} {f g h : SgT X} → FinT g → f ≐ g → g ≐ h → f ≐ h
  ≐-trans {f = f} {g} {h} fg pg gh x =
    trans-core (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x) (at⁺ h x) (at⁻ h x) (proj₁ (fg x)) (proj₂ (fg x)) (pg x) (gh x)

  -- pointwise operations
  infixl 6 _+T_
  infixl 7 _*T_
  _+T_ : ∀ {X : QBS S} → SgT X → SgT X → SgT X
  f +T g = addX (posT f) (posT g) , addX (negT f) (negT g)

  -T_ : ∀ {X : QBS S} → SgT X → SgT X
  -T f = negT f , posT f

  -- c = c⁺ − c⁻ times f: (c⁺ f⁺ + c⁻ f⁻) − (c⁺ f⁻ + c⁻ f⁺)
  scaleT : ∀ {X : QBS S} → Sg → SgT X → SgT X
  scaleT {X} c f = addX (mulH {X} (constW {X} (pos c)) (posT f)) (mulH {X} (constW {X} (neg c)) (negT f))
                 , addX (mulH {X} (constW {X} (pos c)) (negT f)) (mulH {X} (constW {X} (neg c)) (posT f))

  _*T_ : ∀ {X : QBS S} → SgT X → SgT X → SgT X
  _*T_ {X} f g = addX (mulH {X} (posT f) (posT g)) (mulH {X} (negT f) (negT g))
               , addX (mulH {X} (posT f) (negT g)) (mulH {X} (negT f) (posT g))

  constT : ∀ {X : QBS S} → Sg → SgT X
  constT {X} c = constW {X} (pos c) , constW {X} (neg c)

  fromW : ∀ {X : QBS S} → Hom S X WQ → SgT X
  fromW {X} f = f , constW {X} 0#

  infixr 9 _∘T_
  _∘T_ : ∀ {X Y : QBS S} → SgT Y → Hom S X Y → SgT X
  f ∘T h = _∘H_ S (posT f) h , _∘H_ S (negT f) h

  -- pointwise algebra
  +T-pt⁺ : ∀ {X : QBS S} (f g : SgT X) x → at⁺ (f +T g) x ≈ at⁺ f x + at⁺ g x
  +T-pt⁺ f g x = refl

  +T-pt⁻ : ∀ {X : QBS S} (f g : SgT X) x → at⁻ (f +T g) x ≈ at⁻ f x + at⁻ g x
  +T-pt⁻ f g x = refl

  +T-cong : ∀ {X : QBS S} {f f′ g g′ : SgT X} → f ≐ f′ → g ≐ g′ → f +T g ≐ f′ +T g′
  +T-cong {f = f} {f′} {g} {g′} e e′ x =
    add-cong-core (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x) (at⁺ f′ x) (at⁻ f′ x) (at⁺ g′ x) (at⁻ g′ x) (e x) (e′ x)

  +T-inverse : ∀ {X : QBS S} (f : SgT X) → f +T (-T f) ≐ constT (Bounded.0S A)
  +T-inverse f x = solve 2 (λ p n → (p :+ n) :+ con 0 := con 0 :+ (n :+ p)) refl (at⁺ f x) (at⁻ f x)

  -- the real line: x⁺ − x⁻ (`inl x ↦ x`, `inr x ↦ −x`) and its square
  idW′ : Hom S WQ WQ
  idW′ = record { map = record { to = λ x → x ; cong = λ e → e } ; map-random = λ m → m }

  idT sqT : SgT RQ
  idT = copairH idW′ (constW {WQ} 0#) , copairH (constW {WQ} 0#) idW′
  sqT = idT *T idT

  -- `CutQ` and `WQ`
  toW : ∀ {X : QBS S} → Hom S X CutQ → Hom S X WQ
  toW f = record { map = map f ; map-random = map-random f }

  toCut : ∀ {X : QBS S} → Hom S X WQ → Hom S X CutQ
  toCut f = record { map = map f ; map-random = map-random f }

  toW-pt : ∀ {X : QBS S} (f : Hom S X CutQ) x → map (toW f) ⟨$⟩ x ≈ map f ⟨$⟩ x
  toW-pt f x = refl

  toCut-pt : ∀ {X : QBS S} (f : Hom S X WQ) x → map (toCut f) ⟨$⟩ x ≈ map f ⟨$⟩ x
  toCut-pt f x = refl
