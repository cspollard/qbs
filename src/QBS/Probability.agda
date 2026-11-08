{-# OPTIONS --safe --without-K #-}

-- `ProbabilityInterface`: an abstract probability monad over a cartesian closed category with a probe object ℛ.
-- A commutative strong monad of probability measures, `law a μ` (the distribution of a probe) with its axioms,
-- and the bind (Fubini) axioms over a splitting ℛ ≅ ℛ × ℛ.
-- A hypothesis of the abstract layer, supplied by the discrete and continuous models.
-- The generic strong-monad calculation (`ψ`, strength at points) is in `StrongPoint`; `ProbMonad` is in `CommMonad`.
module QBS.Probability where

open import Level using (suc; _⊔_)
open import Data.Product.Base using (Σ; _,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cartesian.Monoidal as CM
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
import Categories.NaturalTransformation as NT
import Categories.Morphism as Morph
import Categories.Morphism.Reasoning as MR

open import QBS.CommMonad using (ProbMonad)
import QBS.StrongPoint as SP
open import QBS.Bind using (module Bind)

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
  open import Categories.Category.BinaryProducts C using (BinaryProducts; module BinaryProducts)
  open import Categories.Category.Cartesian C using (Cartesian)
  open import Categories.Object.Terminal C using (Terminal)

  record ProbLaws (cm : ProbMonad CC) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
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
  record Fubini (cm : ProbMonad CC) (L : ProbLaws cm) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
    open BinaryProducts (Cartesian.products cartesian) using (_⁂_; ⟨⟩∘; ⟨⟩-cong₂; project₁; project₂; ⁂∘⟨⟩; η)
    open Terminal (Cartesian.terminal cartesian) using (!-unique; !-unique₂)
    open ProbLaws L
    private module Mor = Morph C
    -- `σ`, `τ`, `ψ` and the strength-at-a-point lemmas `σ-point`, `τ-point`, `ψ-point` are generic: see `StrongPoint`
    open SP.Strength-at-points CC cm
    open Bind (CommutativeMonad.M cm) using (bind-nat)

    field
      split : ℛ Mor.≅ (ℛ × ℛ)
      tensor : Measure → Measure → Measure
      measure-tensor : ∀ μ ν →
        T.F.F₁ (Mor._≅_.from split) ∘ measure (tensor μ ν) ≈ ψ ℛ ℛ ∘ ⟨ measure μ , measure ν ⟩

    open HomReasoning
    open MR C

    -- the kernel r ↦ law (γ(r, –)) ν of a two-variable probe is again a probe
    kernel : ∀ {X} → (ℛ × ℛ ⇒ X) → Measure → ℛ ⇒ T.F.F₀ X
    kernel γ ν = T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩

    kernel-law : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (r : ⊤ ⇒ ℛ) →
      kernel γ ν ∘ r ≈ law (γ ∘ ⟨ r ∘ ! , id ⟩) ν
    kernel-law γ ν r = begin
      (T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩) ∘ r
        ≈⟨ assoc ⟩
      T.F.F₁ γ ∘ (σ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩) ∘ r
        ≈⟨ refl⟩∘⟨ assoc ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩ ∘ r
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ id ∘ r , (measure ν ∘ !) ∘ r ⟩
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (assoc ○ (Equiv.refl ⟩∘⟨ !-unique₂) ○ identityʳ) ⟩
      T.F.F₁ γ ∘ σ.η (ℛ , ℛ) ∘ ⟨ r , measure ν ⟩
        ≈⟨ refl⟩∘⟨ σ-point r (measure ν) ⟩
      T.F.F₁ γ ∘ T.F.F₁ ⟨ r ∘ ! , id ⟩ ∘ measure ν
        ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (γ ∘ ⟨ r ∘ ! , id ⟩) ∘ measure ν ∎

    -- Tγ commutes past the join (`bind-nat`), and the kernel assembles from the strength
    join-kernel : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (s : ⊤ ⇒ T.F.F₀ ℛ) →
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (σ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ s
        ≈ T.μ.η X ∘ T.F.F₁ (kernel γ ν) ∘ s
    join-kernel γ ν s =
      (refl⟩∘⟨ refl⟩∘⟨ pullˡ (Equiv.sym T.F.homomorphism)) ○ bind-nat γ (σ.η (ℛ , ℛ) ∘ ⟨ id , measure ν ∘ ! ⟩) s

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
      T.F.F₁ γ ∘ T.μ.η (ℛ × ℛ) ∘ T.F.F₁ (σ.η (ℛ , ℛ)) ∘ T.F.F₁ ⟨ id , measure ν ∘ ! ⟩ ∘ measure μ
        ≈⟨ join-kernel γ ν (measure μ) ⟩
      T.μ.η _ ∘ T.F.F₁ (kernel γ ν) ∘ measure μ ∎)

  record ProbabilityInterface : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    field
      commutativeMonad : ProbMonad CC
      laws : ProbLaws commutativeMonad
    open ProbLaws laws public
    field
      fubini : Fubini commutativeMonad laws
    open Fubini fubini public
