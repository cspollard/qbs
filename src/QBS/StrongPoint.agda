{-# OPTIONS --safe --without-K #-}

-- `StrongPoint CC cm`: the strength of a commutative monad `cm` on a cartesian category, evaluated at global
-- elements.  Generic: nothing here mentions ℛ, measures or QBS.  Reuse it from any model that needs strength
-- at points.
--   `ψ A B`        Kock's double strength T A × T B ⇒ T (A × B), the monoidal structure of a commutative monad,
--   `σ-unit`, `τ-unit`   strengthening with the unit object,
--   `σ-point`, `τ-point` strength at a global element on one side,
--   `ψ-point`      the double strength of two global elements: bind the first, then the second.
-- `σ` is the left strength X × T Y ⇒ T (X × Y) and `τ` the right one T X × Y ⇒ T (X × Y), as in agda-categories.
module QBS.StrongPoint where

open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cartesian.Monoidal as CM
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Strong using (StrongMonad; Strength; RightStrength)
import Categories.NaturalTransformation as NT
import Categories.Morphism as Morph
import Categories.Morphism.Reasoning as MR

open import QBS.CommMonad using (ProbMonad)

module Strength-at-points {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C) (cm : ProbMonad CC) where
  open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
  open import Categories.Category.Cartesian C using (Cartesian)
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
  private cartesian = Canonical.CartesianClosed.isCartesian CC
  open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩-cong₂; project₁; project₂; ⁂∘⟨⟩)
  module T = Monad (CommutativeMonad.M cm)
  module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))
  module τ = NT.NaturalTransformation (RightStrength.strengthen (CommutativeMonad.rightStrength cm))
  private
    module Mor = Morph C
    module CMon = CM.CartesianMonoidal {𝒞 = C} cartesian
    module ρ = RightStrength (CommutativeMonad.rightStrength cm)
    module λˢ = Strength (StrongMonad.strength (CommutativeMonad.strongMonad cm))

  -- `ψ` is Kock's double strength, the monoidal structure of a commutative monad: T A × T B ⇒ T (A × B)
  ψ : ∀ A B → T.F.F₀ A × T.F.F₀ B ⇒ T.F.F₀ (A × B)
  ψ A B = T.μ.η (A × B) ∘ T.F.F₁ (σ.η (A , B)) ∘ τ.η (A , T.F.F₀ B)

  open HomReasoning
  open MR C

  -- ⟨ id , ! ⟩ and ⟨ ! , id ⟩ invert the unit projections
  ⟨id,!⟩∘π₁ : ∀ {A} → ⟨ id , ! ⟩ ∘ π₁ ≈ id {A × ⊤}
  ⟨id,!⟩∘π₁ {A} = Mor.Iso.isoˡ (Mor._≅_.iso (CMon.A×⊤≅A {A}))

  ⟨!,id⟩∘π₂ : ∀ {A} → ⟨ ! , id ⟩ ∘ π₂ ≈ id {⊤ × A}
  ⟨!,id⟩∘π₂ {A} = Mor.Iso.isoˡ (Mor._≅_.iso (CMon.⊤×A≅A {A}))

  -- strengthening with the unit object, at global elements
  τ-unit : ∀ {A} (t : ⊤ ⇒ T.F.F₀ A) → τ.η (A , ⊤) ∘ ⟨ t , id ⟩ ≈ T.F.F₁ ⟨ id , ! ⟩ ∘ t
  τ-unit {A} t = begin
    τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ introˡ inv ⟩
    (T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁) ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ assoc ⟩
    T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁ ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    T.F.F₁ ⟨ id , ! ⟩ ∘ (T.F.F₁ π₁ ∘ τ.η (A , ⊤)) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ ρ.identityˡ ⟩∘⟨refl ⟩
    T.F.F₁ ⟨ id , ! ⟩ ∘ π₁ ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ project₁ ⟩
    T.F.F₁ ⟨ id , ! ⟩ ∘ t ∎
    where
      inv : T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁ ≈ id {T.F.F₀ (A × ⊤)}
      inv = Equiv.sym T.F.homomorphism ○ T.F.F-resp-≈ ⟨id,!⟩∘π₁ ○ T.F.identity

  σ-unit : ∀ {B} (t : ⊤ ⇒ T.F.F₀ B) → σ.η (⊤ , B) ∘ ⟨ id , t ⟩ ≈ T.F.F₁ ⟨ ! , id ⟩ ∘ t
  σ-unit {B} t = begin
    σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ introˡ inv ⟩
    (T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂) ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ assoc ⟩
    T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂ ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    T.F.F₁ ⟨ ! , id ⟩ ∘ (T.F.F₁ π₂ ∘ σ.η (⊤ , B)) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ λˢ.identityˡ ⟩∘⟨refl ⟩
    T.F.F₁ ⟨ ! , id ⟩ ∘ π₂ ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ project₂ ⟩
    T.F.F₁ ⟨ ! , id ⟩ ∘ t ∎
    where
      inv : T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂ ≈ id {T.F.F₀ (⊤ × B)}
      inv = Equiv.sym T.F.homomorphism ○ T.F.F-resp-≈ ⟨!,id⟩∘π₂ ○ T.F.identity

  -- strength at global elements
  σ-point : ∀ {A B} (a : ⊤ ⇒ A) (t : ⊤ ⇒ T.F.F₀ B) → σ.η (A , B) ∘ ⟨ a , t ⟩ ≈ T.F.F₁ ⟨ a ∘ ! , id ⟩ ∘ t
  σ-point {A} {B} a t = begin
    σ.η (A , B) ∘ ⟨ a , t ⟩
      ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ (elimˡ T.F.identity)) ⟩
    σ.η (A , B) ∘ (a ⁂ T.F.F₁ id) ∘ ⟨ id , t ⟩
      ≈⟨ pullˡ (σ.commute (a , id)) ⟩
    (T.F.F₁ (a ⁂ id) ∘ σ.η (⊤ , B)) ∘ ⟨ id , t ⟩
      ≈⟨ assoc ⟩
    T.F.F₁ (a ⁂ id) ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ σ-unit t ⟩
    T.F.F₁ (a ⁂ id) ∘ T.F.F₁ ⟨ ! , id ⟩ ∘ t
      ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
    T.F.F₁ ((a ⁂ id) ∘ ⟨ ! , id ⟩) ∘ t
      ≈⟨ T.F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ Equiv.refl identityˡ) ⟩∘⟨refl ⟩
    T.F.F₁ ⟨ a ∘ ! , id ⟩ ∘ t ∎

  τ-point : ∀ {A B} (t : ⊤ ⇒ T.F.F₀ A) (b : ⊤ ⇒ B) → τ.η (A , B) ∘ ⟨ t , b ⟩ ≈ T.F.F₁ ⟨ id , b ∘ ! ⟩ ∘ t
  τ-point {A} {B} t b = begin
    τ.η (A , B) ∘ ⟨ t , b ⟩
      ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ (elimˡ T.F.identity) identityʳ) ⟩
    τ.η (A , B) ∘ (T.F.F₁ id ⁂ b) ∘ ⟨ t , id ⟩
      ≈⟨ pullˡ (τ.commute (id , b)) ⟩
    (T.F.F₁ (id ⁂ b) ∘ τ.η (A , ⊤)) ∘ ⟨ t , id ⟩
      ≈⟨ assoc ⟩
    T.F.F₁ (id ⁂ b) ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ τ-unit t ⟩
    T.F.F₁ (id ⁂ b) ∘ T.F.F₁ ⟨ id , ! ⟩ ∘ t
      ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
    T.F.F₁ ((id ⁂ b) ∘ ⟨ id , ! ⟩) ∘ t
      ≈⟨ T.F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ Equiv.refl) ⟩∘⟨refl ⟩
    T.F.F₁ ⟨ id , b ∘ ! ⟩ ∘ t ∎

  -- the double strength of two global elements: bind the first, then the second
  ψ-point : ∀ {A B} (s : ⊤ ⇒ T.F.F₀ A) (t : ⊤ ⇒ T.F.F₀ B) →
    ψ A B ∘ ⟨ s , t ⟩ ≈ T.μ.η (A × B) ∘ T.F.F₁ (σ.η (A , B)) ∘ T.F.F₁ ⟨ id , t ∘ ! ⟩ ∘ s
  ψ-point {A} {B} s t = begin
    (T.μ.η (A × B) ∘ T.F.F₁ (σ.η (A , B)) ∘ τ.η (A , T.F.F₀ B)) ∘ ⟨ s , t ⟩
      ≈⟨ assoc ⟩
    T.μ.η (A × B) ∘ (T.F.F₁ (σ.η (A , B)) ∘ τ.η (A , T.F.F₀ B)) ∘ ⟨ s , t ⟩
      ≈⟨ refl⟩∘⟨ assoc ⟩
    T.μ.η (A × B) ∘ T.F.F₁ (σ.η (A , B)) ∘ τ.η (A , T.F.F₀ B) ∘ ⟨ s , t ⟩
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ τ-point s t ⟩
    T.μ.η (A × B) ∘ T.F.F₁ (σ.η (A , B)) ∘ T.F.F₁ ⟨ id , t ∘ ! ⟩ ∘ s ∎
