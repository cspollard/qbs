{-# OPTIONS --safe --without-K #-}

-- Abstract soft conditioning on top of a measure monad, and normalization, as small independent structures, each with the laws it
-- needs and the operations derivable from it:
--   `Weights`               weights W: a commutative monoid object with an absorbing zero (`Monoidal.Symmetric.Algebra`);
--                           `SemiringWeights` also have addition
--   `IsAdditive`            the Kleisli category of a monad is enriched over commutative monoids (`Monad.Additive`)
--   `Global`                the semiring of global weights `1 ⇒ W` of `SemiringWeights`
--   `SoftConditioning`      `score : W ⇒ M 1`, a semiring homomorphism from the internal semiring `W` to the scalars of the
--                           Kleisli category (the laws are universal, with a strength); derives `score-hom`, its restriction
--                           to global weights (an object of `const! (Global SW) ↓ Scalars 1`), and `zero`, `scale`, `zero-bind`
--   `Normalization`         optional, for inference, tying `score` to the normalized inclusion `QBS.Monad.Normalized`: `normalize : M X ⇒ Prob X + 1`
-- `zero⇒` (the weight 0) is an absorbing element of the multiplication, not a zero object.
open import Level using (_⊔_)
open import Data.Product.Base using (Σ; _,_)
open import Algebra.Bundles using (Semiring)
open import Algebra.Morphism.Structures using (IsSemiringHomomorphism)

open import Categories.Category.Core using (Category)

module QBS.Statistical {o h e} {C : Category o h e} where

open import Categories.Category using (_[_,_]; _[_∘_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
import Categories.Category.Monoidal.Symmetric.Algebra as Algebra
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
import Categories.Category.Cartesian.GlobalElements as GlobalElements
open import Categories.Monad using (Monad)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation as NT

import Categories.Monad.Notation as Notation
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import Categories.Monad.Additive using (IsAdditive)
open import Categories.Monad.Strong using (StrongMonad; Strength)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import QBS.Monad.CommMonad using (CartCommMonad)
open import QBS.Monad.Probability using (ProbMonad)

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

-- The weights are the scalars `M ⊤` of a commutative additive monad `M`: the terminal semiring object over `M ⊤` (any
-- internal semiring `W` with a homomorphism `score : W → M ⊤` maps to it by `score`), so they are not further data.
-- `ScalarsAt Z` is the semiring `Z ⇒ M ⊤` of the measures on the one-point space depending on `Z`: the sum is `⊕`, `0` is
-- `𝟘`, `1` the Dirac mass, and the product `f ⋆ g` runs `f`, then `g` in the same context (the strength of `M`).  Because
-- `⊕` is available in every context, `M ⊤` is an internal semiring (apply it at `Z = M ⊤ × M ⊤` to the projections).
-- At `Z = ⊤` this is `kleisli-semiring ⊤`.
module Scalars (cm : CartCommMonad CC) (AK : IsAdditive (CommutativeMonad.M cm)) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; !; _×_; π₁; ⟨_,_⟩)
  open IsAdditive AK using (𝟘; _⊕_)
  private
    module M = Notation (CommutativeMonad.M cm)
    module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))
    K = Kleisli (CommutativeMonad.M cm)
    module K = Category K

  infixr 7 _⋆_
  _⋆_ : ∀ {Z} → Z ⇒ M.₀ ⊤ → Z ⇒ M.₀ ⊤ → Z ⇒ M.₀ ⊤
  _⋆_ {Z} f g = M.μ ⊤ ∘ M.₁ (g ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , f ⟩

  ScalarsAt : Obj → Semiring h e
  ScalarsAt Z = record
    { Carrier = Z ⇒ M.₀ ⊤
    ; _≈_ = _≈_
    ; _+_ = _⊕_
    ; _*_ = _⋆_
    ; 0# = 𝟘 {Z} {⊤}
    ; 1# = M.η ⊤ ∘ !
    ; isSemiring = {!!}
    }

  -- the zero measure, absorbing for bind
  zero : K [ ⊤ , ⊤ ]
  zero = 𝟘

  zero-bind : ∀ {Y} (k : K [ ⊤ , Y ]) → k K.∘ zero K.≈ 𝟘
  zero-bind k = {!!}

  -- scaling a measure by a weight
  scale : (⊤ ⇒ M.₀ ⊤) → ∀ {X} → K [ ⊤ , X ] → K [ ⊤ , X ]
  scale w m = K [ m ∘ w ]

-- Normalisation, an optional extension for inference: `normalize : M X ⇒ Prob X + 1` divides a measure by its mass.  It
-- is a left inverse of scaling a probability measure by an invertible weight (`normalize-scale`), and fails on the zero
-- measure (`normalize-zero`); the degenerate infinite-mass case is left unspecified.
record Normalization
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC}
  (AK : IsAdditive (MeasureMonad.monad MM))
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; !; ⟨_,_⟩)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open Scalars (MeasureMonad.commutativeMonad MM) AK using (_⋆_; zero; scale)
  private
    module M = Notation (MeasureMonad.monad MM)
    module Pr = Notation (ProbMonad.monad P)
    module inc = StrongMonad⇒ inc

  -- the component `ι X : Prob X ⇒ M X` of the inclusion
  open NT.NaturalTransformation inc.α using () renaming (η to ι)

  -- a weight with a multiplicative inverse
  Invertible : (⊤ ⇒ M.₀ ⊤) → Set (h ⊔ e)
  Invertible w = Σ (⊤ ⇒ M.₀ ⊤) λ w⁻¹ → w ⋆ w⁻¹ ≈ M.η ⊤ ∘ !

  field
    normalize : ∀ X → M.₀ X ⇒ Pr.₀ X + ⊤
    -- normalizing a probability measure scaled by an invertible weight gives it back
    normalize-scale : ∀ {X} (w : ⊤ ⇒ M.₀ ⊤) → Invertible w → (p : ⊤ ⇒ Pr.₀ X) →
      normalize X ∘ scale w (ι X ∘ p) ≈ i₁ ∘ p
    -- the zero measure cannot be normalized
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.₁ x ∘ zero ≈ i₂
