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
import Categories.Morphism as Morph

-- a commutative monad on a cartesian closed category, for the symmetric monoidal structure of its products
ProbMonad : ∀ {o h e} (C : Category o h e) → Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
ProbMonad C CC = CommutativeMonad (Symmetric.braided (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC)))

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
module _ {o h e} ℓ (C : Category o h e) (ℛ : Category.Obj C) (CC : Canonical.CartesianClosed C) where
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
    braided = Symmetric.braided (CSM.symmetric C cartesian)

  record ProbLaws (cm : CommutativeMonad braided) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; !)
    private module T = Monad (CommutativeMonad.M cm)
    field
      Measure : Set ℓ
      pushforward : (ℛ ⇒ ℛ) → Measure → Measure
      law : ∀ {X} → (ℛ ⇒ X) → Measure → ⊤ ⇒ T.F.F₀ X
      law-resp : ∀ {X} {a b : ℛ ⇒ X} → a ≈ b → ∀ μ → law a μ ≈ law b μ
      -- laws are natural: functoriality is pushforward of laws
      law-map : ∀ {X Y} (f : X ⇒ Y) (a : ℛ ⇒ X) μ → T.F.F₁ f ∘ law a μ ≈ law (f ∘ a) μ
      -- reparametrising the source pushes the measure forward
      law-pre : ∀ {X} (a : ℛ ⇒ X) (m : ℛ ⇒ ℛ) μ → law (a ∘ m) μ ≈ law a (pushforward m μ)
      -- return is the law of a constant probe
      law-return : ∀ {X} (x : ⊤ ⇒ X) μ → T.η.η X ∘ x ≈ law (x ∘ !) μ
      -- every global element of the monad is a law
      law-surjective : ∀ {X} (t : ⊤ ⇒ T.F.F₀ X) → Σ (ℛ ⇒ X) λ a → Σ Measure λ μ → law a μ ≈ t

  -- bind (Fubini): ℛ splits as ℛ × ℛ, and measures multiply
  record Fubini (cm : CommutativeMonad braided) (L : ProbLaws cm) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩)
    open ProbLaws L
    private
      module Mor = Morph C
      module T = Monad (CommutativeMonad.M cm)
    field
      split : ℛ Mor.≅ (ℛ × ℛ)
      tensor : Measure → Measure → Measure
      -- the kernel r ↦ law (γ(r, –)) ν of a two-variable probe is again a probe
      kernel : ∀ {X} → (ℛ × ℛ ⇒ X) → Measure → ℛ ⇒ T.F.F₀ X
      kernel-law : ∀ {X} (γ : ℛ × ℛ ⇒ X) ν (r : ⊤ ⇒ ℛ) →
        kernel γ ν ∘ r ≈ law (γ ∘ ⟨ r ∘ ! , id ⟩) ν
      law-join : ∀ {X} (γ : ℛ × ℛ ⇒ X) μ ν →
        T.μ.η X ∘ law (kernel γ ν) μ ≈ law (γ ∘ Mor._≅_.from split) (tensor μ ν)

  record ProbabilityInterface : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
    field
      commutativeMonad : CommutativeMonad braided
      laws : ProbLaws commutativeMonad
    open ProbLaws laws public
    field
      fubini : Fubini commutativeMonad laws
    open Fubini fubini public
