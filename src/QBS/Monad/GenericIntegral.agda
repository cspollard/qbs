{-# OPTIONS --safe --without-K #-}

-- SKETCH: `QBS.Monad.Integral` over an arbitrary category `C` with a probe object `ℛ`, with no reference to QBS.
-- The points of a space `X` are its generalised elements `C [ ℛ , X ]`, and `V` is a setoid of values.
--   * `Tests`: a presheaf `Test` of "functions on points", given by one map `ε : Test ℛ → V` (the value of a test on
--     the generic point); `eval X : Test X → [ Pt X , V ]`, `eval t x = ε (t ∘ x)`, is its transpose, and is a mono.
--     (Equivalently `eval` is the map `Test ⇒ Ran_ℛ V` corresponding to `ε` under the Kan extension adjunction.)
--   * `Integral T`: a monad `T` on `C` presented by its integral, a natural mono `∫ : Pt ∘ T ⇒ [ Test , V ]`, such
--     that integrating against `η` is evaluation, `join` is the integral of integrals, and integrals are tests.
-- Levels: `C` has hom-sets and equality of morphisms at the same level `ℓ`, and `V : Setoid ℓ ℓ`; `Hom[-, V ]` then
-- lands in `Setoids ℓ ℓ` again, which is the category of the points `Hom[ ℛ ,-]`, so the one `V` serves for tests and
-- for integrals.
open import Categories.Category.Core using (Category)
open import Relation.Binary.Bundles using () renaming (Setoid to GenericSetoid)

module QBS.Monad.GenericIntegral
  {o ℓ} (C : Category o ℓ ℓ) (ℛ : Category.Obj C) (V : GenericSetoid ℓ ℓ)
  where

open import Level using (suc; _⊔_)
open import Function.Bundles using (Func; _⟨$⟩_)

open import Categories.Category using (_[_,_]; _[_∘_])
open import Categories.Category.Instance.Setoids using () renaming (Setoids to GenericSetoids)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom using (module Hom)
open import Categories.Functor.Presheaf using () renaming (Presheaf to GenericPresheaf)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import Categories.Morphism using (Mono)

private
  module C = Category C
  module V = GenericSetoid V
  Setoids = GenericSetoids ℓ ℓ
  Presheaf = GenericPresheaf C Setoids

open Hom C using (Hom[_,-])
open Hom Setoids using (Hom[-,_])

-- the points of `X` are the generalised elements `ℛ ⇒ X`
Pt : Functor C Setoids
Pt = Hom[ ℛ ,-]

-- `V`-valued maps out of a functor: `Dual F X = (F X ⇒ V)`
Dual : ∀ {o′ ℓ′ e′} {B : Category o′ ℓ′ e′} → Functor B Setoids → Functor (Category.op B) Setoids
Dual F = Hom[-, V ] ∘F Functor.op F

-- Tests: a presheaf `Test` with the value `ε` of a test on the generic point.  A test `t` is read as the function on
-- points `x ↦ ε (t ∘ x)`; `eval-mono`: tests are determined by their values on points.
record Tests : Set (o ⊔ suc ℓ) where
  field
    Test : Presheaf
    ε : Func (Functor.F₀ Test ℛ) V

  private module Test = Functor Test

  eval : ∀ X → Func (Test.F₀ X) (Functor.F₀ (Dual Pt) X)
  eval X = record
    { to = λ t → record
        { to = λ x → ε ⟨$⟩ (Test.F₁ x ⟨$⟩ t)
        ; cong = λ x≈y → Func.cong ε (Test.F-resp-≈ x≈y)
        }
    ; cong = λ t≈s {z} → Func.cong ε (Func.cong (Test.F₁ z) t≈s)
    }

  field
    eval-mono : ∀ {X} → Mono Setoids (eval X)

-- A monad `T` presented by its integral `∫ X : Pt (T X) ⇒ [ Test X , V ]`, natural in `X` (the push-forward equation
-- `∫ (T f μ) g = ∫ μ (g ∘ f)`), with
--   * `∫-mono`: equality of points of `T X` is equality of integrals;
--   * `∫ᶠ`: integration is itself a test on `T X`, `eval (∫ᶠ f) μ = ∫ μ f`;
--   * `∫-η`: integrating against a Dirac measure is evaluation, `∫ (η x) f = eval f x`;
--   * `∫-join`: `join` is the integral of integrals, `∫ (join p) f = ∫ p (∫ᶠ f)`.
record Integral (T : Monad C) : Set (o ⊔ suc ℓ) where
  private module T = Monad T
  field
    tests : Tests

  open Tests tests public

  field
    ∫ : NaturalTransformation (Pt ∘F T.F) (Dual Test)

  private module ∫ = NaturalTransformation ∫

  -- `∫ μ f`, and `f` at `x`
  ∫[_] : ∀ X → C [ ℛ , Functor.F₀ T.F X ] → Functor.F₀ Test X .GenericSetoid.Carrier → V.Carrier
  ∫[ X ] μ f = (∫.η X ⟨$⟩ μ) ⟨$⟩ f
  _at_ : ∀ {X} → Functor.F₀ Test X .GenericSetoid.Carrier → C [ ℛ , X ] → V.Carrier
  f at x = (eval _ ⟨$⟩ f) ⟨$⟩ x

  field
    ∫-mono : ∀ {X} → Mono Setoids (∫.η X)
    ∫ᶠ : ∀ X → Func (Functor.F₀ Test X) (Functor.F₀ Test (Functor.F₀ T.F X))
    eval-∫ᶠ : ∀ X f μ → V._≈_ ((∫ᶠ X ⟨$⟩ f) at μ) (∫[ X ] μ f)
    ∫-η : ∀ X x f → V._≈_ (∫[ X ] (C [ NaturalTransformation.η T.η X ∘ x ]) f) (f at x)
    ∫-join : ∀ X p f →
      V._≈_ (∫[ X ] (C [ NaturalTransformation.η T.μ X ∘ p ]) f) (∫[ Functor.F₀ T.F X ] p (∫ᶠ X ⟨$⟩ f))
