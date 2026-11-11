{-# OPTIONS --safe --without-K #-}

-- SKETCH: `QBS.Monad.Integral` over an arbitrary category, with no reference to QBS or to setoids.
-- Data:
--   * a category `C` and a category `𝒮` of "spaces of values" (in the intended instance `Setoids`);
--   * `Pt : C ⇒ 𝒮`, the points of a space (intended: the generalised elements `Hom[ ℛ ,-]` of a probe object `ℛ`);
--   * `D : 𝒮ᵒᵖ ⇒ 𝒮`, the functor `[ – , V ]` of maps into an object `V` of values, with the canonical map
--     `ι : X ⇒ D (D X)` into the double dual (`x ↦ (f ↦ f x)`), natural in `X`.  Together these say that `𝒮` is closed
--     enough to talk about `V`-valued functions.
-- Differences from `QBS.Monad.Integral`:
--   * tests are a presheaf `Test : Cᵒᵖ ⇒ 𝒮` with `eval : Test ⇒ D ∘ Ptᵒᵖ` a monomorphism (tests are determined by
--     their values on points);
--   * a monad `T` on `C` is presented by a natural monomorphism `∫ : Pt ∘ T ⇒ D ∘ Testᵒᵖ`, so that `T X` is
--     determined by its integrals;
--   * the equations of the integral (`∫-η`, `∫-join`, `eval-∫ᶠ`) are equations between morphisms of `𝒮`, using `ι` to
--     turn a point into the evaluation of a test at it.
-- Not yet here: `ℛ` being a generator (so that morphisms of `C` are determined by their action on points), which
-- needs `Pt` to be `Hom[ ℛ ,-]`.
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)

module QBS.Monad.GenericIntegral
  {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {𝒮 : Category o′ ℓ′ e′}
  (Pt : Functor C 𝒮) (D : Functor (Category.op 𝒮) 𝒮)
  where

open import Level using (_⊔_; suc)

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_])
open import Categories.Functor using (_∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Monad using (Monad)
open import Categories.Morphism using (Mono)

private
  module C = Category C
  module 𝒮 = Category 𝒮
  module Pt = Functor Pt
  module D = Functor D

-- the double dual `X ↦ [[ X , V ], V ]`
DD : Functor 𝒮 𝒮
DD = D ∘F Functor.op D

-- the `V`-valued maps out of a functor: `Dual F X = [ F X , V ]`.  It flips variance: a covariant `F` gives a
-- presheaf, a presheaf gives a covariant functor.
Dual : ∀ {o″ ℓ″ e″} {B : Category o″ ℓ″ e″} → Functor B 𝒮 → Functor (Category.op B) 𝒮
Dual F = D ∘F Functor.op F

-- the unit of the double dual
module _ (ι : NaturalTransformation idF DD) where

  -- Tests: a presheaf valued in `𝒮`, read as functions on points by `eval : Test ⇒ Dual Pt`, extensionally: each
  -- component of `eval` is a monomorphism.
  record Tests : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      Test : Presheaf C 𝒮
      eval : NaturalTransformation Test (Dual Pt)
      eval-mono : ∀ {X} → Mono 𝒮 (NaturalTransformation.η eval X)

  -- A monad `T` presented by its integral: a natural monomorphism `∫ : Pt ∘ T ⇒ Dual Test`, `∫ X : Pt (T X) ⇒ [ Test X , V ]`.
  --   * naturality of `∫` is the push-forward equation `∫ (T f μ) g = ∫ μ (g ∘ f)`;
  --   * `∫-mono`: the integral is a monomorphism, so equality of points of `T X` is equality of integrals;
  --   * `∫ᶠ`: integration is itself a test on `T X`, `eval (∫ᶠ f) μ = ∫ μ f`;
  --   * `∫-η`, `∫-join`: the unit is evaluation (a Dirac measure), and `join` is the integral of integrals.
  record Integral (T : Monad C) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
    field
      tests : Tests

    open Tests tests public

    private
      module T = Monad T
      module TF = Functor T.F
      module ι = NaturalTransformation ι
      module eval = NaturalTransformation eval
      module Test = Functor Test

    field
      ∫ : NaturalTransformation (Pt ∘F T.F) (Dual Test)

    private module ∫ = NaturalTransformation ∫

    field
      ∫-mono : ∀ {X} → Mono 𝒮 (∫.η X)
      ∫ᶠ : ∀ X → 𝒮 [ Test.F₀ X , Test.F₀ (TF.F₀ X) ]
      -- `eval (∫ᶠ f) μ = ∫ μ f`: both sides are maps `Test X ⇒ [ Pt (T X) , V ]`
      eval-∫ᶠ : ∀ X → 𝒮 [ 𝒮 [ eval.η (TF.F₀ X) ∘ ∫ᶠ X ] ≈ 𝒮 [ D.F₁ (∫.η X) ∘ ι.η (Test.F₀ X) ] ]
      -- `∫ (η x) f = f x`: both sides are maps `Pt X ⇒ [ Test X , V ]`
      ∫-η : ∀ X → 𝒮 [ 𝒮 [ ∫.η X ∘ Pt.F₁ (NaturalTransformation.η T.η X) ] ≈ 𝒮 [ D.F₁ (eval.η X) ∘ ι.η (Pt.F₀ X) ] ]
      -- `∫ (join p) f = ∫ p (∫ᶠ f)`: both sides are maps `Pt (T (T X)) ⇒ [ Test X , V ]`
      ∫-join : ∀ X → 𝒮 [ 𝒮 [ ∫.η X ∘ Pt.F₁ (NaturalTransformation.η T.μ X) ]
                          ≈ 𝒮 [ D.F₁ (∫ᶠ X) ∘ ∫.η (TF.F₀ X) ] ]
