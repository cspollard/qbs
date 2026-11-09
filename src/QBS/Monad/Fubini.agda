{-# OPTIONS --safe --without-K #-}

-- `IsFubini cm`: a splitting ℛ ≅ ℛ × ℛ of the probe object, with the bind (Fubini) axioms of a commutative monad `cm`.
--   * `split : ℛ ≅ ℛ × ℛ`, and the product measure `tensor μ ν`, the monad's product `ψ ∘ ⟨μ, ν⟩` of two global
--     elements transported along `split`, with `measure-tensor` saying that `T split.from` takes it back to `ψ ∘ ⟨μ, ν⟩`;
--   * `kernel γ ν`, the kernel `r ↦ T γ(r, –) ν` of a two-variable probe `γ : ℛ × ℛ ⇒ X`, with `kernel-image` evaluating it
--     at a point and `join-tensor`: the join of the images of `ν` along the kernel is the image of `tensor μ ν` along `γ ∘ from`.
-- A property of the commutative monad and the splitting only: it uses neither the probability-monad axioms nor
-- `pushforward` (`QBS.Monad.Measure`), so images of measures are written `T a ∘ μ` for a global element `μ : ⊤ ⇒ T ℛ`.
-- Route: `ψ-point` and `σ-point` (`StrongPoint`) turn the strength at points into the kernel; `bind-nat` (`Bind`) commutes
-- `T γ` past the join.
module QBS.Monad.Fubini where

open import Level using (_⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Monad.Commutative using (CommutativeMonad)
import Categories.Morphism as Morph
import Categories.Morphism.Reasoning as MR

open import QBS.Monad.CommMonad using (CartCommMonad)
import QBS.Monad.StrongPoint as SP
open import QBS.Monad.Bind using (module Bind)

module _ {o h e} {C : Category o h e} (ℛ : Category.Obj C) (CC : Canonical.CartesianClosed C) where
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
  open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
  open import Categories.Category.Cartesian C using (Cartesian)
  open import Categories.Object.Terminal C using (Terminal)

  -- bind (Fubini): ℛ splits as ℛ × ℛ, and the product measure is the monad's product of the two measures
  record IsFubini (cm : CartCommMonad CC) : Set (o ⊔ h ⊔ e) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
    open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩∘; ⟨⟩-cong₂; project₁; project₂; ⁂∘⟨⟩; η)
    open Terminal (Cartesian.terminal cartesian) using (!-unique; !-unique₂)
    private module Mor = Morph C
    -- `σ`, `τ`, `ψ` and the strength-at-a-point lemmas `σ-point`, `τ-point`, `ψ-point` are generic: see `StrongPoint`
    open SP.Strength-at-points CC cm
    open Bind (CommutativeMonad.M cm) using (bind-nat)

    field
      split : ℛ Mor.≅ (ℛ × ℛ)

    open HomReasoning
    open MR C

    -- the product measure: the monad's product of the two measures, transported along the splitting
    tensor : (⊤ ⇒ T.F.F₀ ℛ) → (⊤ ⇒ T.F.F₀ ℛ) → (⊤ ⇒ T.F.F₀ ℛ)
    tensor μ ν = T.F.F₁ (Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩

    measure-tensor : ∀ μ ν → T.F.F₁ (Mor._≅_.from split) ∘ tensor μ ν ≈ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
    measure-tensor μ ν = begin
      T.F.F₁ (Mor._≅_.from split) ∘ T.F.F₁ (Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (Mor._≅_.from split ∘ Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ T.F.F-resp-≈ (Mor.Iso.isoʳ (Mor._≅_.iso split)) ⟩∘⟨refl ⟩
      T.F.F₁ id ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ elimˡ T.F.identity ⟩
      ψ ℛ ℛ ∘ ⟨ μ , ν ⟩ ∎

    -- the kernel r ↦ T γ(r, –) ν of a two-variable probe is a morphism ℛ ⇒ T X
    kernel : ∀ {X} → (ℛ × ℛ ⇒ X) → (⊤ ⇒ T.F.F₀ ℛ) → ℛ ⇒ T.F.F₀ X
    kernel γ ν = T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩

    kernel-image : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (r : ⊤ ⇒ ℛ) →
      kernel γ ν ∘ r ≈ T.F.F₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ ν
    kernel-image γ ν r = begin
      (T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩) ∘ r
        ≈⟨ assoc ⟩
      T.F.F₁ γ ∘ (σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩) ∘ r
        ≈⟨ refl⟩∘⟨ assoc ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩ ∘ r
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id ∘ r , (ν ∘ !) ∘ r ⟩
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (assoc ○ (Equiv.refl ⟩∘⟨ !-unique₂) ○ identityʳ) ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ r , ν ⟩
        ≈⟨ refl⟩∘⟨ σ-point r ν ⟩
      T.F.F₁ γ ∘ T.F.F₁ ⟨ r ∘ ! , id ⟩ ∘ ν
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ ν ∎

    -- Tγ commutes past the join (`bind-nat`), and the kernel assembles from the strength
    join-kernel : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (s : ⊤ ⇒ T.F.F₀ ℛ) →
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (σ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , ν ∘ ! ⟩ ∘ s
        ≈ T.μ.η X ∘ T.F.F₁ (kernel γ ν) ∘ s
    join-kernel γ ν s =
      (refl⟩∘⟨ refl⟩∘⟨ pullˡ (Equiv.sym T.F.homomorphism)) ○ bind-nat γ (σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩) s

    join-tensor : ∀ {X} (γ : ℛ × ℛ ⇒ X) μ ν →
      T.μ.η X ∘ T.F.F₁ (kernel γ ν) ∘ μ ≈ T.F.F₁ (γ ∘ Mor._≅_.from split) ∘ tensor μ ν
    join-tensor γ μ ν = Equiv.sym (begin
      T.F.F₁ (γ ∘ Mor._≅_.from split) ∘ tensor μ ν
        ≈⟨ T.F.homomorphism ⟩∘⟨refl ⟩
      (T.F.F₁ γ ∘ T.F.F₁ (Mor._≅_.from split)) ∘ tensor μ ν
        ≈⟨ assoc ⟩
      T.F.F₁ γ ∘ T.F.F₁ (Mor._≅_.from split) ∘ tensor μ ν
        ≈⟨ refl⟩∘⟨ measure-tensor μ ν ⟩
      T.F.F₁ γ ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ refl⟩∘⟨ ψ-point μ ν ⟩
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (σ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , ν ∘ ! ⟩ ∘ μ
        ≈⟨ join-kernel γ ν μ ⟩
      T.μ.η _ ∘ T.F.F₁ (kernel γ ν) ∘ μ ∎)
