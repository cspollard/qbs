{-# OPTIONS --safe --without-K #-}

-- `ProbabilityInterface`: an abstract probability monad over a cartesian closed category with a probe object ℛ.
-- A commutative strong monad of probability measures, `law a μ` (the distribution of a probe) with its axioms,
-- and the bind (Fubini) axioms over a splitting ℛ ≅ ℛ × ℛ.  A hypothesis until a concrete model supplies it.
module QBS.Probability where

open import Level using (Level; suc; _⊔_)
open import Data.Product.Base using (Σ; _,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Strong using (StrongMonad; Strength; RightStrength)
import Categories.NaturalTransformation as NT
import Categories.Morphism as Morph
import Categories.Morphism.Reasoning as MR

-- a commutative monad on a cartesian closed category, for the symmetric monoidal structure of its products
ProbMonad : ∀ {o h e} {C : Category o h e} → Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
ProbMonad {C = C} CC = CommutativeMonad (Symmetric.braided (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC)))

-- An abstract probability monad on a cartesian closed category with an object
-- ℛ of probes (random sources), in the style of Heunen–Kammar–Staton–Vákár.
-- `law a μ` is the distribution of the probe `a : ℛ ⇒ X` under the probability
-- measure μ on ℛ, a global element of the monad.  Elements of the monad are
-- exactly the laws, and `bind` is Fubini over a splitting ℛ ≅ ℛ × ℛ.
--
-- It is assembled from three pieces, all re-exported by `ProbabilityInterface`:
--   the commutative monad itself,
--   `ProbLaws`  : measures on ℛ and their laws, which are natural, reparametrisable, and exhaust the monad,
--   `Fubini`    : the splitting ℛ ≅ ℛ × ℛ, product measures, and the bind (Fubini) axioms.
module _ {o h e} ℓ {C : Category o h e} (ℛ : Category.Obj C) (CC : Canonical.CartesianClosed C) where
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
    braided = Symmetric.braided (CSM.symmetric C cartesian)
  open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
  open import Categories.Category.Cartesian C using (Cartesian)
  open import Categories.Object.Terminal C using (Terminal)

  record ProbLaws (cm : CommutativeMonad braided) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; !)
    private module T = Monad (CommutativeMonad.M cm)
    field
      Measure : Set ℓ
      pushforward : (ℛ ⇒ ℛ) → Measure → Measure
      -- a measure is a global element of the monad on ℛ; the law of a probe is its image
      measure : Measure → ⊤ ⇒ T.F.F₀ ℛ
      -- reparametrising the source pushes the measure forward
      measure-push : ∀ (m : ℛ ⇒ ℛ) μ → T.F.F₁ m ∘ measure μ ≈ measure (pushforward m μ)
      -- measures are probability measures: total mass one
      measure-total : ∀ μ → T.F.F₁ ! ∘ measure μ ≈ T.η.η ⊤
      -- every global element of the monad is the law of a probe
      law-surjective : ∀ {X} (t : ⊤ ⇒ T.F.F₀ X) → Σ (ℛ ⇒ X) λ a → Σ Measure λ μ → T.F.F₁ a ∘ measure μ ≈ t

    -- the law `a μ` of a probe `a : ℛ ⇒ X` is the image of the measure under `T a`
    law : ∀ {X} → (ℛ ⇒ X) → Measure → ⊤ ⇒ T.F.F₀ X
    law a μ = T.F.F₁ a ∘ measure μ

    open HomReasoning
    open MR C

    law-resp : ∀ {X} {a b : ℛ ⇒ X} → a ≈ b → ∀ μ → law a μ ≈ law b μ
    law-resp a≈b μ = T.F.F-resp-≈ a≈b ⟩∘⟨refl

    -- laws are natural: functoriality is pushforward of laws
    law-map : ∀ {X Y} (f : X ⇒ Y) (a : ℛ ⇒ X) μ → T.F.F₁ f ∘ law a μ ≈ law (f ∘ a) μ
    law-map f a μ = pullˡ (Equiv.sym T.F.homomorphism)

    law-pre : ∀ {X} (a : ℛ ⇒ X) (m : ℛ ⇒ ℛ) μ → law (a ∘ m) μ ≈ law a (pushforward m μ)
    law-pre a m μ = begin
      T.F.F₁ (a ∘ m) ∘ measure μ           ≈⟨ T.F.homomorphism ⟩∘⟨refl ⟩
      (T.F.F₁ a ∘ T.F.F₁ m) ∘ measure μ    ≈⟨ assoc ⟩
      T.F.F₁ a ∘ T.F.F₁ m ∘ measure μ      ≈⟨ refl⟩∘⟨ measure-push m μ ⟩
      T.F.F₁ a ∘ measure (pushforward m μ) ∎

    -- return is the law of a constant probe
    law-return : ∀ {X} (x : ⊤ ⇒ X) μ → T.η.η X ∘ x ≈ law (x ∘ !) μ
    law-return x μ = begin
      T.η.η _ ∘ x                          ≈⟨ Equiv.sym (T.η.sym-commute x) ⟩
      T.F.F₁ x ∘ T.η.η ⊤                   ≈⟨ refl⟩∘⟨ Equiv.sym (measure-total μ) ⟩
      T.F.F₁ x ∘ T.F.F₁ ! ∘ measure μ      ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (x ∘ !) ∘ measure μ           ∎

  -- bind (Fubini): ℛ splits as ℛ × ℛ, and the product measure is the monad's product of the two measures
  record Fubini (cm : CommutativeMonad braided) (L : ProbLaws cm) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
    open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩∘; ⟨⟩-cong₂; project₁; project₂; ⁂∘⟨⟩; η)
    open Terminal (Cartesian.terminal cartesian) using (!-unique; !-unique₂)
    open ProbLaws L
    private
      module Mor = Morph C
      module T = Monad (CommutativeMonad.M cm)
      module τ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))
      module σ = NT.NaturalTransformation (RightStrength.strengthen (CommutativeMonad.rightStrength cm))
      module ρ = RightStrength (CommutativeMonad.rightStrength cm)
      module λˢ = Strength (StrongMonad.strength (CommutativeMonad.strongMonad cm))

    -- the monoidal structure of a commutative monad: T A × T B ⇒ T (A × B)
    ψ : ∀ A B → T.F.F₀ A × T.F.F₀ B ⇒ T.F.F₀ (A × B)
    ψ A B = T.μ.η (A × B) ∘ T.F.F₁ (τ.η (A , B)) ∘ σ.η (A , T.F.F₀ B)

    field
      split : ℛ Mor.≅ (ℛ × ℛ)
      tensor : Measure → Measure → Measure
      measure-tensor : ∀ μ ν →
        T.F.F₁ (Mor._≅_.from split) ∘ measure (tensor μ ν) ≈ ψ ℛ ℛ ∘ ⟨ measure μ , measure ν ⟩

    open HomReasoning
    open MR C

    -- ⟨ id , ! ⟩ and ⟨ ! , id ⟩ invert the unit projections
    ⟨id,!⟩∘π₁ : ∀ {A} → ⟨ id , ! ⟩ ∘ π₁ ≈ id {A × ⊤}
    ⟨id,!⟩∘π₁ = ⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ !-unique₂ ○ η

    ⟨!,id⟩∘π₂ : ∀ {A} → ⟨ ! , id ⟩ ∘ π₂ ≈ id {⊤ × A}
    ⟨!,id⟩∘π₂ = ⟨⟩∘ ○ ⟨⟩-cong₂ !-unique₂ identityˡ ○ η

    -- strengthening with the unit object, at global elements
    σ-unit : ∀ {A} (t : ⊤ ⇒ T.F.F₀ A) → σ.η (A , ⊤) ∘ ⟨ t , id ⟩ ≈ T.F.F₁ ⟨ id , ! ⟩ ∘ t
    σ-unit {A} t = begin
      σ.η (A , ⊤) ∘ ⟨ t , id ⟩
        ≈⟨ introˡ inv ⟩
      (T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁) ∘ σ.η (A , ⊤) ∘ ⟨ t , id ⟩
        ≈⟨ assoc ⟩
      T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁ ∘ σ.η (A , ⊤) ∘ ⟨ t , id ⟩
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      T.F.F₁ ⟨ id , ! ⟩ ∘ (T.F.F₁ π₁ ∘ σ.η (A , ⊤)) ∘ ⟨ t , id ⟩
        ≈⟨ refl⟩∘⟨ ρ.identityˡ ⟩∘⟨refl ⟩
      T.F.F₁ ⟨ id , ! ⟩ ∘ π₁ ∘ ⟨ t , id ⟩
        ≈⟨ refl⟩∘⟨ project₁ ⟩
      T.F.F₁ ⟨ id , ! ⟩ ∘ t ∎
      where
        inv : T.F.F₁ ⟨ id , ! ⟩ ∘ T.F.F₁ π₁ ≈ id {T.F.F₀ (A × ⊤)}
        inv = Equiv.sym T.F.homomorphism ○ T.F.F-resp-≈ ⟨id,!⟩∘π₁ ○ T.F.identity

    τ-unit : ∀ {B} (t : ⊤ ⇒ T.F.F₀ B) → τ.η (⊤ , B) ∘ ⟨ id , t ⟩ ≈ T.F.F₁ ⟨ ! , id ⟩ ∘ t
    τ-unit {B} t = begin
      τ.η (⊤ , B) ∘ ⟨ id , t ⟩
        ≈⟨ introˡ inv ⟩
      (T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂) ∘ τ.η (⊤ , B) ∘ ⟨ id , t ⟩
        ≈⟨ assoc ⟩
      T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂ ∘ τ.η (⊤ , B) ∘ ⟨ id , t ⟩
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      T.F.F₁ ⟨ ! , id ⟩ ∘ (T.F.F₁ π₂ ∘ τ.η (⊤ , B)) ∘ ⟨ id , t ⟩
        ≈⟨ refl⟩∘⟨ λˢ.identityˡ ⟩∘⟨refl ⟩
      T.F.F₁ ⟨ ! , id ⟩ ∘ π₂ ∘ ⟨ id , t ⟩
        ≈⟨ refl⟩∘⟨ project₂ ⟩
      T.F.F₁ ⟨ ! , id ⟩ ∘ t ∎
      where
        inv : T.F.F₁ ⟨ ! , id ⟩ ∘ T.F.F₁ π₂ ≈ id {T.F.F₀ (⊤ × B)}
        inv = Equiv.sym T.F.homomorphism ○ T.F.F-resp-≈ ⟨!,id⟩∘π₂ ○ T.F.identity

    -- strength at global elements
    τ-point : ∀ {A B} (a : ⊤ ⇒ A) (t : ⊤ ⇒ T.F.F₀ B) → τ.η (A , B) ∘ ⟨ a , t ⟩ ≈ T.F.F₁ ⟨ a ∘ ! , id ⟩ ∘ t
    τ-point {A} {B} a t = begin
      τ.η (A , B) ∘ ⟨ a , t ⟩
        ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ (elimˡ T.F.identity)) ⟩
      τ.η (A , B) ∘ (a ⁂ T.F.F₁ id) ∘ ⟨ id , t ⟩
        ≈⟨ pullˡ (τ.commute (a , id)) ⟩
      (T.F.F₁ (a ⁂ id) ∘ τ.η (⊤ , B)) ∘ ⟨ id , t ⟩
        ≈⟨ assoc ⟩
      T.F.F₁ (a ⁂ id) ∘ τ.η (⊤ , B) ∘ ⟨ id , t ⟩
        ≈⟨ refl⟩∘⟨ τ-unit t ⟩
      T.F.F₁ (a ⁂ id) ∘ T.F.F₁ ⟨ ! , id ⟩ ∘ t
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ ((a ⁂ id) ∘ ⟨ ! , id ⟩) ∘ t
        ≈⟨ T.F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ Equiv.refl identityˡ) ⟩∘⟨refl ⟩
      T.F.F₁ ⟨ a ∘ ! , id ⟩ ∘ t ∎

    σ-point : ∀ {A B} (t : ⊤ ⇒ T.F.F₀ A) (b : ⊤ ⇒ B) → σ.η (A , B) ∘ ⟨ t , b ⟩ ≈ T.F.F₁ ⟨ id , b ∘ ! ⟩ ∘ t
    σ-point {A} {B} t b = begin
      σ.η (A , B) ∘ ⟨ t , b ⟩
        ≈⟨ refl⟩∘⟨ Equiv.sym (⁂∘⟨⟩ ○ ⟨⟩-cong₂ (elimˡ T.F.identity) identityʳ) ⟩
      σ.η (A , B) ∘ (T.F.F₁ id ⁂ b) ∘ ⟨ t , id ⟩
        ≈⟨ pullˡ (σ.commute (id , b)) ⟩
      (T.F.F₁ (id ⁂ b) ∘ σ.η (A , ⊤)) ∘ ⟨ t , id ⟩
        ≈⟨ assoc ⟩
      T.F.F₁ (id ⁂ b) ∘ σ.η (A , ⊤) ∘ ⟨ t , id ⟩
        ≈⟨ refl⟩∘⟨ σ-unit t ⟩
      T.F.F₁ (id ⁂ b) ∘ T.F.F₁ ⟨ id , ! ⟩ ∘ t
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ ((id ⁂ b) ∘ ⟨ id , ! ⟩) ∘ t
        ≈⟨ T.F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ Equiv.refl) ⟩∘⟨refl ⟩
      T.F.F₁ ⟨ id , b ∘ ! ⟩ ∘ t ∎

    -- the kernel r ↦ law (γ(r, –)) ν of a two-variable probe is again a probe
    kernel : ∀ {X} → (ℛ × ℛ ⇒ X) → Measure → ℛ ⇒ T.F.F₀ X
    kernel γ ν = T.F.F₁ γ ∘ τ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩

    kernel-law : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (r : ⊤ ⇒ ℛ) →
      kernel γ ν ∘ r ≈ law (γ ∘ ⟨ r ∘ ! , id ⟩) ν
    kernel-law γ ν r = begin
      (T.F.F₁ γ ∘ τ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩) ∘ r
        ≈⟨ assoc ⟩
      T.F.F₁ γ ∘ (τ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩) ∘ r
        ≈⟨ refl⟩∘⟨ assoc ⟩
      T.F.F₁ γ ∘ τ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩ ∘ r
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
      T.F.F₁ γ ∘ τ.η (ℛ , ℛ) ∘ ⟨ id ∘ r , (measure ν ∘ !) ∘ r ⟩
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (assoc ○ (Equiv.refl ⟩∘⟨ !-unique₂) ○ identityʳ) ⟩
      T.F.F₁ γ ∘ τ.η (ℛ , ℛ) ∘ ⟨ r , measure ν ⟩
        ≈⟨ refl⟩∘⟨ τ-point r (measure ν) ⟩
      T.F.F₁ γ ∘ T.F.F₁ ⟨ r ∘ ! , id ⟩ ∘ measure ν
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ measure ν ∎

    -- the monoidal product of two global elements: bind the first, then the second
    ψ-point : ∀ (s t : ⊤ ⇒ T.F.F₀ ℛ) →
      ψ ℛ ℛ ∘ ⟨ s , t ⟩ ≈ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , t ∘ ! ⟩ ∘ s
    ψ-point s t = begin
      (T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ σ.η (ℛ , T.F.F₀ ℛ)) ∘ ⟨ s , t ⟩
        ≈⟨ assoc ⟩
      T.μ.η (ℛ × ℛ) ∘ (T.F.F₁ (τ.η (ℛ , ℛ)) ∘ σ.η (ℛ , T.F.F₀ ℛ)) ∘ ⟨ s , t ⟩
        ≈⟨ refl⟩∘⟨ assoc ⟩
      T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ σ.η (ℛ , T.F.F₀ ℛ) ∘ ⟨ s , t ⟩
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ σ-point s t ⟩
      T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , t ∘ ! ⟩ ∘ s ∎

    -- Tγ commutes past the join, and the kernel assembles from the strength
    join-kernel : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (s : ⊤ ⇒ T.F.F₀ ℛ) →
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈ T.μ.η X ∘ T.F.F₁ (kernel γ ν) ∘ s
    join-kernel γ ν s = begin
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈⟨ pullˡ (T.μ.sym-commute γ) ⟩
      (T.μ.η _ ∘ T.F.F₁ (T.F.F₁ γ)) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈⟨ assoc ⟩
      T.μ.η _ ∘ T.F.F₁ (T.F.F₁ γ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.μ.η _ ∘ T.F.F₁ (T.F.F₁ γ ∘ τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.μ.η _ ∘ T.F.F₁ ((T.F.F₁ γ ∘ τ.η (ℛ , ℛ)) ∘ ⟨ id , measure ν ∘ ! ⟩) ∘ s
        ≈⟨ refl⟩∘⟨ T.F.F-resp-≈ assoc ⟩∘⟨refl ⟩
      T.μ.η _ ∘ T.F.F₁ (kernel γ ν) ∘ s ∎

    law-join : ∀ {X} (γ : ℛ × ℛ ⇒ X) μ ν →
      T.μ.η X ∘ law (kernel γ ν) μ ≈ law (γ ∘ Mor._≅_.from split) (tensor μ ν)
    law-join γ μ ν = Equiv.sym (begin
      law (γ ∘ Mor._≅_.from split) (tensor μ ν)
        ≈⟨ T.F.homomorphism ⟩∘⟨refl ⟩
      (T.F.F₁ γ ∘ T.F.F₁ (Mor._≅_.from split)) ∘ measure (tensor μ ν)
        ≈⟨ assoc ⟩
      T.F.F₁ γ ∘ T.F.F₁ (Mor._≅_.from split) ∘ measure (tensor μ ν)
        ≈⟨ refl⟩∘⟨ measure-tensor μ ν ⟩
      T.F.F₁ γ ∘ ψ ℛ ℛ ∘ ⟨ measure μ , measure ν ⟩
        ≈⟨ refl⟩∘⟨ ψ-point (measure μ) (measure ν) ⟩
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (τ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ measure μ
        ≈⟨ join-kernel γ ν (measure μ) ⟩
      T.μ.η _ ∘ T.F.F₁ (kernel γ ν) ∘ measure μ ∎)

  record ProbabilityInterface : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    field
      commutativeMonad : CommutativeMonad braided
      laws : ProbLaws commutativeMonad
    open ProbLaws laws public
    field
      fubini : Fubini commutativeMonad laws
    open Fubini fubini public
