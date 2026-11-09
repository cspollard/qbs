{-# OPTIONS --safe --without-K #-}

-- `ProbMonad`: an abstract probability monad over a cartesian closed category with a probe object ℛ.
-- A measure monad (`IsMeasureMonad`, `QBS.Monad.Measure`) that is affine (`IsProbMonad`): every measure has total mass one.
-- The splitting ℛ ≅ ℛ × ℛ with the bind (Fubini) axioms is a separate property of a commutative monad: `QBS.Monad.Fubini`.
-- A hypothesis of the abstract layer, supplied by the discrete and continuous models.
-- The generic strong-monad calculation (`ψ`, strength at points) is in `StrongPoint`; `CartCommMonad` is in `CommMonad`.
--
-- Source: affine monads are Fritz, *A synthetic approach to Markov kernels* (arXiv:1908.07021), §3 (`T I ≅ I`);
-- Prop. 22.4 of Heunen–Kammar–Staton–Yang (arXiv:1701.02547) (`P X ≅ G X` for standard Borel X) identifies probability
-- measures on R with global elements of `P R`.  Divergences from the literature: see `QBS.Monad.Measure`; and the
-- monoidal structure is that of a commutative monad (`CartCommMonad`) rather than a symmetric monoidal one.
module QBS.Monad.Probability where

open import Level using (_⊔_)
open import Data.Product.Base using (_,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad.Strong using (StrongMonad; Strength)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation as NT

open import QBS.Monad.CommMonad using (CartCommMonad)
open import QBS.Monad.Measure using (IsMeasureMonad; MeasureMonad)

-- `ProbMonad` is a commutative monad together with `IsProbMonad`, its property of being a measure monad that is affine.
module _ {o h e} {C : Category o h e} (ℛ : Category.Obj C) (CC : Canonical.CartesianClosed C) where
  open import Categories.Object.Terminal C using (IsTerminal)

  record IsProbMonad (cm : CartCommMonad CC) : Set (o ⊔ h ⊔ e) where
    open Category C
    open Canonical.CartesianClosed CC using (⊤; !)
    private module T = Monad (CommutativeMonad.M cm)
    field
      isMeasure : IsMeasureMonad ℛ CC cm
      -- T 1 ≅ 1 (Fritz §3): the monad is affine
      affine : IsTerminal (T.F.F₀ ⊤)

    open IsMeasureMonad isMeasure public

    open HomReasoning
    open MR C

    -- every measure has total mass one
    measure-total : ∀ (μ : Measure) → T.F.F₁ ! ∘ μ ≈ T.η.η ⊤
    measure-total μ = Equiv.trans (Equiv.sym (IsTerminal.!-unique affine _)) (IsTerminal.!-unique affine _)

    -- return is the push-forward along a constant probe (HKSY Eq. 4: `η x = [λr.x, μ]`)
    pushforward-const : ∀ {X} (x : ⊤ ⇒ X) μ → T.η.η X ∘ x ≈ pushforward (x ∘ !) μ
    pushforward-const x μ = begin
      T.η.η _ ∘ x                          ≈⟨ Equiv.sym (T.η.sym-commute x) ⟩
      T.F.F₁ x ∘ T.η.η ⊤                   ≈⟨ refl⟩∘⟨ Equiv.sym (measure-total μ) ⟩
      T.F.F₁ x ∘ T.F.F₁ ! ∘ μ              ≈⟨ pullˡ (Equiv.sym T.F.homomorphism) ⟩
      T.F.F₁ (x ∘ !) ∘ μ                   ∎

  -- a probability monad: a commutative monad with the property `IsProbMonad` (as `Monoid` and `IsMonoid`)
  record ProbMonad : Set (o ⊔ h ⊔ e) where
    field
      commutativeMonad : CartCommMonad CC
      isProb : IsProbMonad commutativeMonad
    open IsProbMonad isProb public

  -- the probability monad `P` is a sub-monad of the measure monad `M`: a monad morphism `P ⇒ M` (probability measures
  -- are measures) that also respects the strength
  record Inclusion (P : ProbMonad) (M : MeasureMonad ℛ CC) : Set (o ⊔ h ⊔ e) where
    open Category C
    open Canonical.CartesianClosed CC using (_×_; ⟨_,_⟩; π₁; π₂)
    private
      module τM = NT.NaturalTransformation
        (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad (MeasureMonad.commutativeMonad M))))
      module τP = NT.NaturalTransformation
        (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad (ProbMonad.commutativeMonad P))))
    field
      inclusion : Monad⇒-id (CommutativeMonad.M (MeasureMonad.commutativeMonad M))
                            (CommutativeMonad.M (ProbMonad.commutativeMonad P))
      inclusion-strong : ∀ A B →
        Monad⇒-id.α.η inclusion (A × B) ∘ τP.η (A , B) ≈ τM.η (A , B) ∘ ⟨ π₁ , Monad⇒-id.α.η inclusion B ∘ π₂ ⟩
