{-# OPTIONS --safe --without-K #-}

-- The writer monad of a monoid object `W` in a monoidal category: `W ⊗ –`, the right-hand part of the tensor
-- bifunctor (`Monoidal._⊗-`, that is `appˡ ⊗ W`), with unit `x ↦ (1, x)` and multiplication `(w, (v, x)) ↦ (wv, x)`.
-- The monad laws are the monoid laws of `W` and the coherence of the monoidal category.
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Object.Monoid as Mon

module Categories.Monad.Writer {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (W : Mon.Monoid M) where

open import Categories.Functor using (Endofunctor; _∘F_) renaming (id to idF)
open import Categories.Monad using (Monad)
open import Categories.NaturalTransformation using (NaturalTransformation)
import Categories.Morphism.Reasoning as MR

open Category C
open Monoidal M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Utilities M using (triangle-inv; pentagon-inv; module Shorthands)
open import Categories.Category.Monoidal.Properties M using (coherence-inv₁)
open Shorthands
open MR C

private
  module W = Mon.Monoid W
  A : Obj
  A = W.Carrier

  merge₁ : ∀ {X Y Z Z′} {f : Y ⇒ Z} {g : X ⇒ Y} → f ⊗₁ id {Z′} ∘ g ⊗₁ id ≈ (f ∘ g) ⊗₁ id
  merge₁ = Equiv.sym split₁ʳ

  -- `W ⊗ f` commutes with the unit and multiplication of `W`
  mult-assoc : W.μ ∘ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {A}) ≈ W.μ ∘ id ⊗₁ W.μ
  mult-assoc = begin
    W.μ ∘ (W.μ ⊗₁ id ∘ α⇐)           ≈⟨ sym-assoc ⟩
    (W.μ ∘ W.μ ⊗₁ id) ∘ α⇐           ≈⟨ W.assoc ⟩∘⟨refl ⟩
    (W.μ ∘ id ⊗₁ W.μ ∘ α⇒) ∘ α⇐      ≈⟨ assoc ⟩
    W.μ ∘ (id ⊗₁ W.μ ∘ α⇒) ∘ α⇐      ≈⟨ refl⟩∘⟨ cancelʳ associator.isoʳ ⟩
    W.μ ∘ id ⊗₁ W.μ                  ∎

-- the functor `W ⊗ –`
Writer-F : Endofunctor C
Writer-F = A ⊗-

-- `tell w = (w, *)`: the generating operation of the writer monad.  A monad morphism out of the writer monad is
-- determined by its component at the unit object, precomposed with `tell`.
tell : A ⇒ A ⊗₀ unit
tell = ρ⇐

-- `η x = (1, x)`
Writer-η : NaturalTransformation idF Writer-F
Writer-η = record
  { η = λ X → W.η ⊗₁ id ∘ λ⇐
  ; commute = λ {X} {Y} f → begin
      (W.η ⊗₁ id ∘ λ⇐) ∘ f          ≈⟨ assoc ⟩
      W.η ⊗₁ id ∘ λ⇐ ∘ f            ≈⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
      W.η ⊗₁ id ∘ (id ⊗₁ f) ∘ λ⇐    ≈⟨ sym-assoc ⟩
      (W.η ⊗₁ id ∘ id ⊗₁ f) ∘ λ⇐    ≈⟨ parallel (identityʳ ○ ⟺ identityˡ) (identityˡ ○ ⟺ identityʳ) ⟩∘⟨refl ⟩
      (id ⊗₁ f ∘ W.η ⊗₁ id) ∘ λ⇐    ≈⟨ assoc ⟩
      id ⊗₁ f ∘ W.η ⊗₁ id ∘ λ⇐      ∎
  ; sym-commute = λ {X} {Y} f → Equiv.sym (begin
      (W.η ⊗₁ id ∘ λ⇐) ∘ f          ≈⟨ assoc ⟩
      W.η ⊗₁ id ∘ λ⇐ ∘ f            ≈⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
      W.η ⊗₁ id ∘ (id ⊗₁ f) ∘ λ⇐    ≈⟨ sym-assoc ⟩
      (W.η ⊗₁ id ∘ id ⊗₁ f) ∘ λ⇐    ≈⟨ parallel (identityʳ ○ ⟺ identityˡ) (identityˡ ○ ⟺ identityʳ) ⟩∘⟨refl ⟩
      (id ⊗₁ f ∘ W.η ⊗₁ id) ∘ λ⇐    ≈⟨ assoc ⟩
      id ⊗₁ f ∘ W.η ⊗₁ id ∘ λ⇐      ∎)
  }

-- `μ (w, (v, x)) = (wv, x)`
Writer-μ : NaturalTransformation (Writer-F ∘F Writer-F) Writer-F
Writer-μ = record
  { η = λ X → W.μ ⊗₁ id ∘ α⇐
  ; commute = λ {X} {Y} f → natural f
  ; sym-commute = λ {X} {Y} f → Equiv.sym (natural f)
  }
  where
    natural : ∀ {X Y} (f : X ⇒ Y) →
      (W.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (id ⊗₁ f) ≈ id ⊗₁ f ∘ (W.μ ⊗₁ id ∘ α⇐)
    natural f = begin
      (W.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (id ⊗₁ f)      ≈⟨ assoc ⟩
      W.μ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ (id ⊗₁ f)        ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
      W.μ ⊗₁ id ∘ ((id ⊗₁ id) ⊗₁ f) ∘ α⇐      ≈⟨ sym-assoc ⟩
      (W.μ ⊗₁ id ∘ (id ⊗₁ id) ⊗₁ f) ∘ α⇐      ≈⟨ parallel (refl⟩∘⟨ ⊗.identity ○ identityʳ ○ ⟺ identityˡ)
                                                         (identityˡ ○ ⟺ identityʳ) ⟩∘⟨refl ⟩
      (id ⊗₁ f ∘ W.μ ⊗₁ id) ∘ α⇐              ≈⟨ assoc ⟩
      id ⊗₁ f ∘ W.μ ⊗₁ id ∘ α⇐                ∎

Writer : Monad C
Writer = record
  { F = Writer-F
  ; η = Writer-η
  ; μ = Writer-μ
  ; assoc = assoc-law
  ; sym-assoc = Equiv.sym assoc-law
  ; identityˡ = identityˡ-law
  ; identityʳ = identityʳ-law
  }
  where
    -- both sides of the associativity law reduce to `((μ ∘ id ⊗ μ) ⊗ id) ∘ α⇐ ∘ id ⊗ α⇐`
    assoc-lhs : ∀ {X} → (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ id ⊗₁ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X})
                       ≈ ((W.μ ∘ id ⊗₁ W.μ) ⊗₁ id {X}) ∘ α⇐ {A} {A ⊗₀ A} {X} ∘ id ⊗₁ α⇐ {A} {A} {X}
    assoc-lhs = begin
      (W.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (W.μ ⊗₁ id ∘ α⇐)
        ≈⟨ refl⟩∘⟨ split₂ʳ ⟩
      (W.μ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ (W.μ ⊗₁ id) ∘ id ⊗₁ α⇐)
        ≈⟨ assoc ⟩
      W.μ ⊗₁ id ∘ α⇐ ∘ (id ⊗₁ (W.μ ⊗₁ id) ∘ id ⊗₁ α⇐)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (W.μ ⊗₁ id)) ∘ id ⊗₁ α⇐
        ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (((id ⊗₁ W.μ) ⊗₁ id) ∘ α⇐) ∘ id ⊗₁ α⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      W.μ ⊗₁ id ∘ ((id ⊗₁ W.μ) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ sym-assoc ⟩
      (W.μ ⊗₁ id ∘ (id ⊗₁ W.μ) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ merge₁ ⟩∘⟨refl ⟩
      ((W.μ ∘ id ⊗₁ W.μ) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐ ∎

    assoc-rhs : ∀ {X} → (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {A ⊗₀ X})
                       ≈ ((W.μ ∘ id ⊗₁ W.μ) ⊗₁ id {X}) ∘ α⇐ {A} {A ⊗₀ A} {X} ∘ id ⊗₁ α⇐ {A} {A} {X}
    assoc-rhs = begin
      (W.μ ⊗₁ id ∘ α⇐) ∘ (W.μ ⊗₁ id ∘ α⇐)
        ≈⟨ assoc ⟩
      W.μ ⊗₁ id ∘ α⇐ ∘ (W.μ ⊗₁ id ∘ α⇐)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ W.μ ⊗₁ id) ∘ α⇐
        ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ ⊗-resp-≈ʳ ⊗.identity) ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ W.μ ⊗₁ (id ⊗₁ id)) ∘ α⇐
        ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (((W.μ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ α⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      W.μ ⊗₁ id ∘ ((W.μ ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ α⇐
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ pentagon-inv ⟩
      W.μ ⊗₁ id ∘ ((W.μ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ α⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      W.μ ⊗₁ id ∘ ((W.μ ⊗₁ id) ⊗₁ id) ∘ α⇐ ⊗₁ id ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      W.μ ⊗₁ id ∘ (((W.μ ⊗₁ id) ⊗₁ id) ∘ α⇐ ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ refl⟩∘⟨ merge₁ ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (((W.μ ⊗₁ id) ∘ α⇐) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ sym-assoc ⟩
      (W.μ ⊗₁ id ∘ ((W.μ ⊗₁ id ∘ α⇐) ⊗₁ id)) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ merge₁ ⟩∘⟨refl ⟩
      ((W.μ ∘ (W.μ ⊗₁ id ∘ α⇐)) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐
        ≈⟨ ⊗-resp-≈ˡ mult-assoc ⟩∘⟨refl ⟩
      ((W.μ ∘ id ⊗₁ W.μ) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ α⇐ ∎

    assoc-law : ∀ {X} → (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ id ⊗₁ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X})
                       ≈ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ (W.μ ⊗₁ id ∘ α⇐ {A} {A} {A ⊗₀ X})
    assoc-law = assoc-lhs ○ ⟺ assoc-rhs

    identityˡ-law : ∀ {X} → (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ id ⊗₁ (W.η ⊗₁ id ∘ λ⇐ {X}) ≈ id
    identityˡ-law = begin
      (W.μ ⊗₁ id ∘ α⇐) ∘ id ⊗₁ (W.η ⊗₁ id ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ split₂ʳ ⟩
      (W.μ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ (W.η ⊗₁ id) ∘ id ⊗₁ λ⇐)
        ≈⟨ assoc ⟩
      W.μ ⊗₁ id ∘ α⇐ ∘ (id ⊗₁ (W.η ⊗₁ id) ∘ id ⊗₁ λ⇐)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ (W.η ⊗₁ id)) ∘ id ⊗₁ λ⇐
        ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (((id ⊗₁ W.η) ⊗₁ id) ∘ α⇐) ∘ id ⊗₁ λ⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      W.μ ⊗₁ id ∘ ((id ⊗₁ W.η) ⊗₁ id) ∘ α⇐ ∘ id ⊗₁ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-inv ⟩
      W.μ ⊗₁ id ∘ ((id ⊗₁ W.η) ⊗₁ id) ∘ ρ⇐ ⊗₁ id
        ≈⟨ sym-assoc ⟩
      (W.μ ⊗₁ id ∘ (id ⊗₁ W.η) ⊗₁ id) ∘ ρ⇐ ⊗₁ id
        ≈⟨ merge₁ ⟩∘⟨refl ⟩
      ((W.μ ∘ id ⊗₁ W.η) ⊗₁ id) ∘ ρ⇐ ⊗₁ id
        ≈⟨ merge₁ ⟩
      (((W.μ ∘ id ⊗₁ W.η) ∘ ρ⇐) ⊗₁ id)
        ≈˘⟨ (W.identityʳ ⟩∘⟨refl) ⟩⊗⟨refl ⟩
      ((ρ⇒ ∘ ρ⇐) ⊗₁ id)
        ≈⟨ unitorʳ.isoʳ ⟩⊗⟨refl ⟩
      id ⊗₁ id
        ≈⟨ ⊗.identity ⟩
      id ∎

    identityʳ-law : ∀ {X} → (W.μ ⊗₁ id ∘ α⇐ {A} {A} {X}) ∘ (W.η ⊗₁ id ∘ λ⇐ {A ⊗₀ X}) ≈ id
    identityʳ-law = begin
      (W.μ ⊗₁ id ∘ α⇐) ∘ (W.η ⊗₁ id ∘ λ⇐)
        ≈⟨ assoc ⟩
      W.μ ⊗₁ id ∘ α⇐ ∘ (W.η ⊗₁ id ∘ λ⇐)
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ W.η ⊗₁ id) ∘ λ⇐
        ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ ⊗-resp-≈ʳ ⊗.identity) ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (α⇐ ∘ W.η ⊗₁ (id ⊗₁ id)) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩∘⟨refl ⟩
      W.μ ⊗₁ id ∘ (((W.η ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ assoc ⟩
      W.μ ⊗₁ id ∘ ((W.η ⊗₁ id) ⊗₁ id) ∘ α⇐ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₁ ⟩
      W.μ ⊗₁ id ∘ ((W.η ⊗₁ id) ⊗₁ id) ∘ λ⇐ ⊗₁ id
        ≈⟨ sym-assoc ⟩
      (W.μ ⊗₁ id ∘ (W.η ⊗₁ id) ⊗₁ id) ∘ λ⇐ ⊗₁ id
        ≈⟨ merge₁ ⟩∘⟨refl ⟩
      ((W.μ ∘ W.η ⊗₁ id) ⊗₁ id) ∘ λ⇐ ⊗₁ id
        ≈⟨ merge₁ ⟩
      (((W.μ ∘ W.η ⊗₁ id) ∘ λ⇐) ⊗₁ id)
        ≈˘⟨ (W.identityˡ ⟩∘⟨refl) ⟩⊗⟨refl ⟩
      ((λ⇒ ∘ λ⇐) ⊗₁ id)
        ≈⟨ unitorˡ.isoʳ ⟩⊗⟨refl ⟩
      id ⊗₁ id
        ≈⟨ ⊗.identity ⟩
      id ∎
