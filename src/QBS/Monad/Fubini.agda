{-# OPTIONS --safe --without-K #-}

-- `IsFubini cm`: a splitting ℛ ≅ ℛ × ℛ of the probe object, with the bind (Fubini) axioms of a commutative monad `cm`.
--   * `split : ℛ ≅ ℛ × ℛ`, and the product measure `tensor μ ν`, the monad's product `ψ ∘ ⟨μ, ν⟩` of two global
--     elements transported along `split`, with `measure-tensor` saying that `T split.from` takes it back to `ψ ∘ ⟨μ, ν⟩`;
--   * `kernel γ ν`, the kernel `r ↦ T γ(r, –) ν` of a two-variable probe `γ : ℛ × ℛ ⇒ X`, with `kernel-image` evaluating it
--     at a point and `join-tensor`: the join of the images of `ν` along the kernel is the image of `tensor μ ν` along `γ ∘ from`.
-- A property of the commutative monad and the splitting only: it uses neither the probability-monad axioms nor
-- `pushforward` (`QBS.Monad.Measure`), so images of measures are written `T a ∘ μ` for a global element `μ : ⊤ ⇒ T ℛ`.
-- Route: `ψ-point` and `σ-point` (`StrongPoint`) turn the strength at points into the kernel; naturality of `μ` commutes
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

    field
      split : ℛ Mor.≅ (ℛ × ℛ)

    open HomReasoning
    open MR C

    -- the product measure: the monad's product of the two measures, transported along the splitting
    tensor : (⊤ ⇒ T.₀ ℛ) → (⊤ ⇒ T.₀ ℛ) → (⊤ ⇒ T.₀ ℛ)
    tensor μ ν = T.₁ (Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩

    measure-tensor : ∀ μ ν → T.₁ (Mor._≅_.from split) ∘ tensor μ ν ≈ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
    measure-tensor μ ν = begin
      T.₁ (Mor._≅_.from split) ∘ T.₁ (Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ pullˡ (Equiv.sym T.homomorphism) ⟩
      T.₁ (Mor._≅_.from split ∘ Mor._≅_.to split) ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ T.₁-resp-≈ (Mor.Iso.isoʳ (Mor._≅_.iso split)) ⟩∘⟨refl ⟩
      T.₁ id ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ elimˡ T.identity ⟩
      ψ ℛ ℛ ∘ ⟨ μ , ν ⟩ ∎

    -- the kernel r ↦ T γ(r, –) ν of a two-variable probe is a morphism ℛ ⇒ T X
    kernel : ∀ {X} → (ℛ × ℛ ⇒ X) → (⊤ ⇒ T.₀ ℛ) → ℛ ⇒ T.₀ X
    kernel γ ν = T.₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩

    kernel-image : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (r : ⊤ ⇒ ℛ) →
      kernel γ ν ∘ r ≈ T.₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ ν
    kernel-image γ ν r = begin
      (T.₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩) ∘ r
        ≈⟨ assoc ⟩
      T.₁ γ ∘ (σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩) ∘ r
        ≈⟨ refl⟩∘⟨ assoc ⟩
      T.₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , ν ∘ ! ⟩ ∘ r
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
      T.₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id ∘ r , (ν ∘ !) ∘ r ⟩
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (assoc ○ (Equiv.refl ⟩∘⟨ !-unique₂) ○ identityʳ) ⟩
      T.₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ r , ν ⟩
        ≈⟨ refl⟩∘⟨ σ-point r ν ⟩
      T.₁ γ ∘ T.₁ ⟨ r ∘ ! , id ⟩ ∘ ν
        ≈⟨ pullˡ (Equiv.sym T.homomorphism) ⟩
      T.₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ ν ∎

    -- Tγ commutes past the join (naturality of `μ`), and the kernel assembles from the strength
    join-kernel : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (s : ⊤ ⇒ T.₀ ℛ) →
      T.₁ γ ∘ T.μ (ℛ × ℛ) ∘ T.₁ (σ.η (ℛ , ℛ)) ∘ T.₁ ⟨ id , ν ∘ ! ⟩ ∘ s
        ≈ T.μ X ∘ T.₁ (kernel γ ν) ∘ s
    join-kernel γ ν s =
      (refl⟩∘⟨ refl⟩∘⟨ pullˡ (Equiv.sym T.homomorphism)) ○ extendʳ (T.μ-sym-commute γ)
        ○ (refl⟩∘⟨ pullˡ (Equiv.sym T.homomorphism))

    join-tensor : ∀ {X} (γ : ℛ × ℛ ⇒ X) μ ν →
      T.μ X ∘ T.₁ (kernel γ ν) ∘ μ ≈ T.₁ (γ ∘ Mor._≅_.from split) ∘ tensor μ ν
    join-tensor γ μ ν = Equiv.sym (begin
      T.₁ (γ ∘ Mor._≅_.from split) ∘ tensor μ ν
        ≈⟨ T.homomorphism ⟩∘⟨refl ⟩
      (T.₁ γ ∘ T.₁ (Mor._≅_.from split)) ∘ tensor μ ν
        ≈⟨ assoc ⟩
      T.₁ γ ∘ T.₁ (Mor._≅_.from split) ∘ tensor μ ν
        ≈⟨ refl⟩∘⟨ measure-tensor μ ν ⟩
      T.₁ γ ∘ ψ ℛ ℛ ∘ ⟨ μ , ν ⟩
        ≈⟨ refl⟩∘⟨ ψ-point μ ν ⟩
      T.₁ γ ∘ T.μ (ℛ × ℛ) ∘ T.₁ (σ.η (ℛ , ℛ)) ∘ T.₁ ⟨ id , ν ∘ ! ⟩ ∘ μ
        ≈⟨ join-kernel γ ν μ ⟩
      T.μ _ ∘ T.₁ (kernel γ ν) ∘ μ ∎)
