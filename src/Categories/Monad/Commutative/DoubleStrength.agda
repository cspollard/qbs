{-# OPTIONS --safe --without-K #-}

-- The strength calculus of a commutative monad `cm` on a cartesian closed category.  Generic: nothing here mentions ℛ,
-- measures or QBS.
--   `ψ A B`, `ψ′ A B`   Kock's double strength T A × T B ⇒ T (A × B), the monoidal structure of a commutative monad: run
--                       the first factor, then the second (`ψ`), or the second, then the first (`ψ′`); `ψ≈ψ′` is commutativity,
--   `σ-nat`, `σ-bind`, `σ-diag`, `τ-ctx`   the strength in a context `Z`: naturality, compatibility with bind, strength twice,
--                       and the right strength of a pair of kernels,
--   `σ-unit`, `τ-unit`  strengthening with the unit object,
--   `σ-point`, `τ-point`, `ψ-point`   the same at global elements (the context `⊤`).
-- `σ` is the left strength X × T Y ⇒ T (X × Y) and `τ` the right one T X × Y ⇒ T (X × Y), as in agda-categories.
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

open import Categories.Monad.Commutative.Cartesian using (CartCommMonad)

module Categories.Monad.Commutative.DoubleStrength
  {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C) (cm : CartCommMonad CC) where
open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
open import Categories.Category.Cartesian C using (Cartesian)
open Category C
open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
private cartesian = Canonical.CartesianClosed.isCartesian CC
open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩∘; ⟨⟩-cong₂; ⁂-cong₂; project₁; project₂; ⁂∘⟨⟩; π₁∘⁂; π₂∘⁂; assocˡ; assocˡ∘⟨⟩; η)
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

-- the same with the order of the effects exchanged; the two agree by commutativity of the monad
ψ′ : ∀ A B → T.₀ A × T.₀ B ⇒ T.₀ (A × B)
ψ′ A B = T.μ (A × B) ∘ T.₁ (τ.η (A , B)) ∘ σ.η (T.₀ A , B)

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

ψ≈ψ′ : ∀ {A B} → ψ A B ≈ ψ′ A B
ψ≈ψ′ = sym-assoc ○ ⟺ (CommutativeMonad.commutes cm) ○ assoc

-- the strength in a context `Z`

-- naturality of `σ` in the first factor, with the second factor an identity
σ-nat : ∀ {A A′ B} (g : A ⇒ A′) → σ.η (A′ , B) ∘ (g ⁂ id) ≈ T.₁ (g ⁂ id) ∘ σ.η (A , B)
σ-nat g = refl⟩∘⟨ ⁂-cong₂ Equiv.refl (⟺ T.identity) ○ σ.commute (g , id)

⟨⟩-⁂ : ∀ {A B C} (h : B ⇒ C) (u : A ⇒ B) → ⟨ id , h ∘ u ⟩ ≈ (id ⁂ h) ∘ ⟨ id , u ⟩
⟨⟩-⁂ h u = ⟺ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identity² Equiv.refl)

-- the strength commutes with bind: `σ ∘ (id ⁂ μ) ≈ μ ∘ T σ ∘ σ`, and naturality of `σ` in the second factor
σ-bind : ∀ {Z A B} (h : A ⇒ T.₀ B) (u : Z ⇒ T.₀ A)
  → σ.η (Z , B) ∘ ⟨ id , T.μ B ∘ T.₁ h ∘ u ⟩
    ≈ T.μ (Z × B) ∘ T.₁ (σ.η (Z , B)) ∘ T.₁ (id ⁂ h) ∘ σ.η (Z , A) ∘ ⟨ id , u ⟩
σ-bind {Z} {A} {B} h u = begin
  σ.η (Z , B) ∘ ⟨ id , T.μ B ∘ T.₁ h ∘ u ⟩
    ≈⟨ refl⟩∘⟨ (⟨⟩-⁂ _ _ ○ refl⟩∘⟨ ⟨⟩-⁂ _ _) ⟩
  σ.η (Z , B) ∘ (id ⁂ T.μ B) ∘ (id ⁂ T.₁ h) ∘ ⟨ id , u ⟩
    ≈⟨ pullˡ (⟺ λˢ.μ-η-comm) ⟩
  (T.μ (Z × B) ∘ T.₁ (σ.η (Z , B)) ∘ σ.η (Z , T.₀ B)) ∘ (id ⁂ T.₁ h) ∘ ⟨ id , u ⟩
    ≈⟨ assoc ○ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ (sym-assoc ○ σ.commute (id , h) ⟩∘⟨refl ○ assoc)) ⟩
  T.μ (Z × B) ∘ T.₁ (σ.η (Z , B)) ∘ T.₁ (id ⁂ h) ∘ σ.η (Z , A) ∘ ⟨ id , u ⟩
    ∎

-- strengthening twice: `strength-assoc` at the diagonal of the context
σ-diag : ∀ {Z A} (f : Z ⇒ T.₀ A)
  → σ.η (Z , Z × A) ∘ ⟨ id , σ.η (Z , A) ∘ ⟨ id , f ⟩ ⟩ ≈ T.₁ ⟨ π₁ , id ⟩ ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
σ-diag {Z} {A} f = begin
  σ.η (Z , Z × A) ∘ ⟨ id , σ.η (Z , A) ∘ ⟨ id , f ⟩ ⟩
    ≈⟨ refl⟩∘⟨ (⟨⟩-⁂ _ _ ○ refl⟩∘⟨ ⟺ assocˡ∘⟨⟩) ⟩
  σ.η (Z , Z × A) ∘ (id ⁂ σ.η (Z , A)) ∘ assocˡ ∘ ⟨ ⟨ id , id ⟩ , f ⟩
    ≈⟨ (refl⟩∘⟨ sym-assoc ○ sym-assoc) ○ (⟺ λˢ.strength-assoc ⟩∘⟨refl ○ assoc) ⟩
  T.₁ assocˡ ∘ σ.η (Z × Z , A) ∘ ⟨ ⟨ id , id ⟩ , f ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ identityˡ) ⟩
  T.₁ assocˡ ∘ σ.η (Z × Z , A) ∘ (⟨ id , id ⟩ ⁂ id) ∘ ⟨ id , f ⟩
    ≈⟨ refl⟩∘⟨ (sym-assoc ○ σ-nat {Z} {Z × Z} {A} ⟨ id , id ⟩ ⟩∘⟨refl ○ assoc) ⟩
  T.₁ assocˡ ∘ T.₁ (⟨ id , id ⟩ ⁂ id) ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ≈⟨ pullˡ (⟺ T.homomorphism) ⟩
  T.₁ (assocˡ ∘ (⟨ id , id ⟩ ⁂ id)) ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ≈⟨ T.₁-resp-≈ diag ⟩∘⟨refl ⟩
  T.₁ ⟨ π₁ , id ⟩ ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ∎
  where
    diag : assocˡ ∘ (⟨ id , id ⟩ ⁂ id) ≈ ⟨ π₁ , id ⟩
    diag = ∘-resp-≈ʳ (⟨⟩-cong₂ (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ identityˡ) identityˡ) ○ assocˡ∘⟨⟩ ○ ⟨⟩-cong₂ Equiv.refl η

-- the right strength at a pair of kernels `⟨ f , g ⟩`: run `f` in the context, then pair with `g`
τ-ctx : ∀ {Z A B} (f : Z ⇒ T.₀ A) (g : Z ⇒ T.₀ B)
  → τ.η (A , T.₀ B) ∘ ⟨ f , g ⟩ ≈ T.₁ ⟨ π₂ , g ∘ π₁ ⟩ ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
τ-ctx {Z} {A} {B} f g = begin
  τ.η (A , T.₀ B) ∘ ⟨ f , g ⟩
    ≈⟨ assoc ○ refl⟩∘⟨ assoc ⟩
  T.₁ ⟨ π₂ , π₁ ⟩ ∘ σ.η (T.₀ B , A) ∘ ⟨ π₂ , π₁ ⟩ ∘ ⟨ f , g ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (⟨⟩∘ ○ ⟨⟩-cong₂ project₂ project₁ ○ ⟺ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ identityˡ)) ⟩
  T.₁ ⟨ π₂ , π₁ ⟩ ∘ σ.η (T.₀ B , A) ∘ (g ⁂ id) ∘ ⟨ id , f ⟩
    ≈⟨ refl⟩∘⟨ (sym-assoc ○ σ-nat g ⟩∘⟨refl ○ assoc) ⟩
  T.₁ ⟨ π₂ , π₁ ⟩ ∘ T.₁ (g ⁂ id) ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ≈⟨ pullˡ (⟺ T.homomorphism) ⟩
  T.₁ (⟨ π₂ , π₁ ⟩ ∘ (g ⁂ id)) ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ≈⟨ T.₁-resp-≈ (⟨⟩∘ ○ ⟨⟩-cong₂ (π₂∘⁂ ○ identityˡ) π₁∘⁂) ⟩∘⟨refl ⟩
  T.₁ ⟨ π₂ , g ∘ π₁ ⟩ ∘ σ.η (Z , A) ∘ ⟨ id , f ⟩
    ∎
