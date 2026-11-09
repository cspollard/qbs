{-# OPTIONS --safe --without-K #-}

-- `StrongPoint CC cm`: the strength of a commutative monad `cm` on a cartesian category, evaluated at global
-- elements.  Generic: nothing here mentions ℛ, measures or QBS.  Reuse it from any model that needs strength
-- at points.
--   `ψ A B`        Kock's double strength T A × T B ⇒ T (A × B), the monoidal structure of a commutative monad,
--   `σ-unit`, `τ-unit`   strengthening with the unit object,
--   `σ-point`, `τ-point` strength at a global element on one side,
--   `ψ-point`      the double strength of two global elements: bind the first, then the second.
-- `σ` is the left strength X × T Y ⇒ T (X × Y) and `τ` the right one T X × Y ⇒ T (X × Y), as in agda-categories.
module QBS.Monad.StrongPoint where

open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Monad.Notation as Notation
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Strong using (StrongMonad; Strength; RightStrength)
import Categories.NaturalTransformation as NT
import Categories.Morphism as Morph
import Categories.Morphism.Reasoning as MR

open import QBS.Monad.CommMonad using (CartCommMonad)

module Strength-at-points {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C) (cm : CartCommMonad CC) where
  open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
  open import Categories.Category.Cartesian C using (Cartesian)
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
  private cartesian = Canonical.CartesianClosed.isCartesian CC
  open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩-cong₂; project₁; project₂; ⁂∘⟨⟩)
  module T = Notation (CommutativeMonad.M cm)
  module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))
  module τ = NT.NaturalTransformation (RightStrength.strengthen (CommutativeMonad.rightStrength cm))
  private
    module Mor = Morph C
    module CMon = CM.CartesianMonoidal {𝒞 = C} cartesian
    module ρ = RightStrength (CommutativeMonad.rightStrength cm)
    module λˢ = Strength (StrongMonad.strength (CommutativeMonad.strongMonad cm))

  -- `ψ` is Kock's double strength, the monoidal structure of a commutative monad: T A × T B ⇒ T (A × B)
  ψ : ∀ A B → T.₀ A × T.₀ B ⇒ T.₀ (A × B)
  ψ A B = T.μ (A × B) ∘ T.₁ (σ.η (A , B)) ∘ τ.η (A , T.₀ B)

  open HomReasoning
  open MR C

  -- ⟨ id , ! ⟩ and ⟨ ! , id ⟩ invert the unit projections
  ⟨id,!⟩∘π₁ : ∀ {A} → ⟨ id , ! ⟩ ∘ π₁ ≈ id {A × ⊤}
  ⟨id,!⟩∘π₁ {A} = Mor.Iso.isoˡ (Mor._≅_.iso (CMon.A×⊤≅A {A}))

  ⟨!,id⟩∘π₂ : ∀ {A} → ⟨ ! , id ⟩ ∘ π₂ ≈ id {⊤ × A}
  ⟨!,id⟩∘π₂ {A} = Mor.Iso.isoˡ (Mor._≅_.iso (CMon.⊤×A≅A {A}))

  -- strengthening with the unit object, at global elements
  τ-unit : ∀ {A} (t : ⊤ ⇒ T.₀ A) → τ.η (A , ⊤) ∘ ⟨ t , id ⟩ ≈ T.₁ ⟨ id , ! ⟩ ∘ t
  τ-unit {A} t = begin
    τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ introˡ inv ⟩
    (T.₁ ⟨ id , ! ⟩ ∘ T.₁ π₁) ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ assoc ⟩
    T.₁ ⟨ id , ! ⟩ ∘ T.₁ π₁ ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    T.₁ ⟨ id , ! ⟩ ∘ (T.₁ π₁ ∘ τ.η (A , ⊤)) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ ρ.identityˡ ⟩∘⟨refl ⟩
    T.₁ ⟨ id , ! ⟩ ∘ π₁ ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ project₁ ⟩
    T.₁ ⟨ id , ! ⟩ ∘ t ∎
    where
      inv : T.₁ ⟨ id , ! ⟩ ∘ T.₁ π₁ ≈ id {T.₀ (A × ⊤)}
      inv = Equiv.sym T.homomorphism ○ T.₁-resp-≈ ⟨id,!⟩∘π₁ ○ T.identity

  σ-unit : ∀ {B} (t : ⊤ ⇒ T.₀ B) → σ.η (⊤ , B) ∘ ⟨ id , t ⟩ ≈ T.₁ ⟨ ! , id ⟩ ∘ t
  σ-unit {B} t = begin
    σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ introˡ inv ⟩
    (T.₁ ⟨ ! , id ⟩ ∘ T.₁ π₂) ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ assoc ⟩
    T.₁ ⟨ ! , id ⟩ ∘ T.₁ π₂ ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    T.₁ ⟨ ! , id ⟩ ∘ (T.₁ π₂ ∘ σ.η (⊤ , B)) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ λˢ.identityˡ ⟩∘⟨refl ⟩
    T.₁ ⟨ ! , id ⟩ ∘ π₂ ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ project₂ ⟩
    T.₁ ⟨ ! , id ⟩ ∘ t ∎
    where
      inv : T.₁ ⟨ ! , id ⟩ ∘ T.₁ π₂ ≈ id {T.₀ (⊤ × B)}
      inv = Equiv.sym T.homomorphism ○ T.₁-resp-≈ ⟨!,id⟩∘π₂ ○ T.identity

  -- strength at global elements
  σ-point : ∀ {A B} (a : ⊤ ⇒ A) (t : ⊤ ⇒ T.₀ B) → σ.η (A , B) ∘ ⟨ a , t ⟩ ≈ T.₁ ⟨ a ∘ ! , id ⟩ ∘ t
  σ-point {A} {B} a t = begin
    σ.η (A , B) ∘ ⟨ a , t ⟩
      ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ (elimˡ T.identity)) ⟩
    σ.η (A , B) ∘ (a ⁂ T.₁ id) ∘ ⟨ id , t ⟩
      ≈⟨ pullˡ (σ.commute (a , id)) ⟩
    (T.₁ (a ⁂ id) ∘ σ.η (⊤ , B)) ∘ ⟨ id , t ⟩
      ≈⟨ assoc ⟩
    T.₁ (a ⁂ id) ∘ σ.η (⊤ , B) ∘ ⟨ id , t ⟩
      ≈⟨ refl⟩∘⟨ σ-unit t ⟩
    T.₁ (a ⁂ id) ∘ T.₁ ⟨ ! , id ⟩ ∘ t
      ≈⟨ pullˡ (Equiv.sym T.homomorphism) ⟩
    T.₁ ((a ⁂ id) ∘ ⟨ ! , id ⟩) ∘ t
      ≈⟨ T.₁-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ Equiv.refl identityˡ) ⟩∘⟨refl ⟩
    T.₁ ⟨ a ∘ ! , id ⟩ ∘ t ∎

  τ-point : ∀ {A B} (t : ⊤ ⇒ T.₀ A) (b : ⊤ ⇒ B) → τ.η (A , B) ∘ ⟨ t , b ⟩ ≈ T.₁ ⟨ id , b ∘ ! ⟩ ∘ t
  τ-point {A} {B} t b = begin
    τ.η (A , B) ∘ ⟨ t , b ⟩
      ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ (elimˡ T.identity) identityʳ) ⟩
    τ.η (A , B) ∘ (T.₁ id ⁂ b) ∘ ⟨ t , id ⟩
      ≈⟨ pullˡ (τ.commute (id , b)) ⟩
    (T.₁ (id ⁂ b) ∘ τ.η (A , ⊤)) ∘ ⟨ t , id ⟩
      ≈⟨ assoc ⟩
    T.₁ (id ⁂ b) ∘ τ.η (A , ⊤) ∘ ⟨ t , id ⟩
      ≈⟨ refl⟩∘⟨ τ-unit t ⟩
    T.₁ (id ⁂ b) ∘ T.₁ ⟨ id , ! ⟩ ∘ t
      ≈⟨ pullˡ (Equiv.sym T.homomorphism) ⟩
    T.₁ ((id ⁂ b) ∘ ⟨ id , ! ⟩) ∘ t
      ≈⟨ T.₁-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ Equiv.refl) ⟩∘⟨refl ⟩
    T.₁ ⟨ id , b ∘ ! ⟩ ∘ t ∎

  -- the double strength of two global elements: bind the first, then the second
  ψ-point : ∀ {A B} (s : ⊤ ⇒ T.₀ A) (t : ⊤ ⇒ T.₀ B) →
    ψ A B ∘ ⟨ s , t ⟩ ≈ T.μ (A × B) ∘ T.₁ (σ.η (A , B)) ∘ T.₁ ⟨ id , t ∘ ! ⟩ ∘ s
  ψ-point {A} {B} s t = begin
    (T.μ (A × B) ∘ T.₁ (σ.η (A , B)) ∘ τ.η (A , T.₀ B)) ∘ ⟨ s , t ⟩
      ≈⟨ assoc ⟩
    T.μ (A × B) ∘ (T.₁ (σ.η (A , B)) ∘ τ.η (A , T.₀ B)) ∘ ⟨ s , t ⟩
      ≈⟨ refl⟩∘⟨ assoc ⟩
    T.μ (A × B) ∘ T.₁ (σ.η (A , B)) ∘ τ.η (A , T.₀ B) ∘ ⟨ s , t ⟩
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ τ-point s t ⟩
    T.μ (A × B) ∘ T.₁ (σ.η (A , B)) ∘ T.₁ ⟨ id , t ∘ ! ⟩ ∘ s ∎
