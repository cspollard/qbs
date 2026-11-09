{-# OPTIONS --safe --without-K #-}

-- Abstract soft conditioning and measures on top of a `ProbMonad`, as small independent structures, each with the laws it
-- needs and the operations derivable from it:
--   `Weights`               weights W: a commutative monoid object with an absorbing zero (`Monoidal.Symmetric.Algebra`);
--                           `SemiringWeights` also have addition
--   `AdditiveKernels`       the Kleisli category of a monad is enriched over commutative monoids: kernels can be added
--   `SoftConditioning`      `score : W ⇒ M 1`, a semiring homomorphism from the global weights to the scalars `1 ⇒ M 1` of
--                           the Kleisli category; derives `zero`, `scale`, `zero-bind`
--   `IsNormalizedInclusion` Prob is the normalized (mass one) part of a measure monad M: `ι : Prob ⇒ M` is an equalizer
--                           of mass and 1
--   `Normalization`         optional, for inference: `normalize : M X ⇒ Prob X + 1`
-- `zero⇒` (the weight 0) is an absorbing element of the multiplication, not a zero object.
open import Level using (_⊔_)
open import Data.Product.Base using (Σ)
open import Algebra.Structures using (IsCommutativeMonoid)

open import Categories.Category.Core using (Category)

module QBS.Statistical {o h e} {C : Category o h e} where

open import Categories.Morphism C using (Mono)
open import Categories.Diagram.Equalizer C using (IsEqualizer; IsEqualizer⇒Mono)
open import Categories.Category using (_[_,_]; _[_∘_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
import Categories.Category.Monoidal.Symmetric.Algebra as Algebra
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Monad using (Monad)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation as NT

import Categories.Monad.Notation as Notation
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import QBS.Monad.Probability using (ProbMonad)

-- Weights: a commutative monoid object with an absorbing zero (`Categories.Category.Monoidal.Symmetric.Algebra`) for
-- the symmetric monoidal structure of the products of `CC`.  `Mul` is the multiplication, whose unit is the weight 1;
-- `zero⇒` is the weight 0, absorbing for `Mul` (`zeroʳ`).
Weights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
Weights CC = Algebra.CommutativeMonoidWithZero (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- Weights that can also be added (e.g. `[0,∞]`): a commutative semiring; `commutativeMonoidWithZero` forgets to `Weights`.
SemiringWeights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
SemiringWeights CC = Algebra.CommutativeSemiring (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

-- Additive kernels: the Kleisli category `K` of `M` is enriched over commutative monoids (the laws of agda-categories'
-- `CM-Category`).  Every hom-set of kernels `X ⇒ M Y` is a commutative monoid, with zero `𝟘` and sum `⊕`, and composition
-- (bind) is bilinear.  For a measure monad, `⊕` is the sum of measures and `𝟘` the zero measure.
record AdditiveKernels (M : Monad C) : Set (o ⊔ h ⊔ e) where

  private
    K = Kleisli M
    module K = Category K

  infixl 6 _⊕_
  field
    𝟘 : ∀ {X Y} → K [ X , Y ]
    _⊕_ : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ]
    isCommutativeMonoid : ∀ {X Y} → IsCommutativeMonoid (K._≈_ {X} {Y}) _⊕_ 𝟘
    -- bind is linear in the kernel run before, the kernel run after, and the continuation
    ⊕-resp-∘ : ∀ {A B C D} (k : K [ C , D ]) (f g : K [ B , C ]) (h : K [ A , B ]) →
      k K.∘ (f ⊕ g) K.∘ h K.≈ (k K.∘ f K.∘ h) ⊕ (k K.∘ g K.∘ h)
    𝟘-resp-∘ : ∀ {A B C D} (k : K [ C , D ]) (h : K [ A , B ]) → k K.∘ 𝟘 {B} {C} K.∘ h K.≈ 𝟘

-- Soft conditioning on a monad `M` with additive kernels.  The weights `W` are a semiring in `C`; the scalars of the
-- Kleisli category `K` of `M` are the kernels `1 ⇒ M 1`, a semiring under `⊕` and Kleisli composition.  `score : W ⇒ M 1`
-- is the measure of mass `w`, and the laws say that it is a semiring homomorphism from the global weights `1 ⇒ W` to the
-- scalars.  Everything is stated at global elements, so no strength is needed and `M` is any monad: nothing here uses
-- probability or measures.  Scaling a measure `m : 1 ⇒ M X` by a weight `w` is the Kleisli composite `K [ m ∘ score ∘ w ]`.
record SoftConditioning {CC : Canonical.CartesianClosed C} (SW : SemiringWeights CC) {M : Monad C}
  (AK : AdditiveKernels M) : Set (o ⊔ h ⊔ e) where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; ⟨_,_⟩)
  open Algebra.CommutativeMonoidWithZero (Algebra.CommutativeSemiring.commutativeMonoidWithZero SW)
    renaming (Carrier to W) public
  open Algebra.CommutativeSemiring SW using (μ⁺)
  open AdditiveKernels AK
  private
    module M = Notation M
    K = Kleisli M
    module K = Category K

  field
    -- the weight `w` as a measure on the one-point space with total mass `w`
    score : W ⇒ M.₀ ⊤
    -- the weight 1 is the Dirac mass
    score-one : score ∘ η* ≈ M.η ⊤
    -- the weight 0 is the zero measure
    score-zero : score ∘ zero⇒ ≈ 𝟘 {⊤} {⊤}
    -- a product of weights is the composite of the scores: run `score w`, then `score w′`
    score-mul : ∀ (w w′ : ⊤ ⇒ W) → score ∘ μ* ∘ ⟨ w , w′ ⟩ ≈ K [ (score ∘ w′) ∘ (score ∘ w) ]
    -- a sum of weights is the sum of the scores
    score-add : ∀ (w w′ : ⊤ ⇒ W) → score ∘ μ⁺ ∘ ⟨ w , w′ ⟩ ≈ (score ∘ w) ⊕ (score ∘ w′)

  -- the zero measure
  zero : K [ ⊤ , ⊤ ]
  zero = score ∘ zero⇒

  -- scaling a measure by a weight
  scale : (⊤ ⇒ W) → ∀ {X} → K [ ⊤ , X ] → K [ ⊤ , X ]
  scale w m = K [ m ∘ (score ∘ w) ]

  -- the zero measure is absorbing for bind: any kernel run after it gives the zero measure
  zero-bind : ∀ {Y} (k : K [ ⊤ , Y ]) → k K.∘ zero K.≈ 𝟘
  zero-bind k = K.Equiv.trans (K.∘-resp-≈ʳ score-zero)
    (K.Equiv.trans (K.∘-resp-≈ʳ (K.Equiv.sym K.identityʳ)) (𝟘-resp-∘ k K.id))

-- The probability monad is the affine part of the measure monad: `Prob X` is the equalizer, inside `M X`, of the mass
-- `M ! : M X ⇒ M ⊤` (pushforward to the point) and the constant unit measure `η ⊤ ∘ !`.  So `ι : Prob ⇒ Meas` is monic,
-- and every kernel `Z ⇒ M X` of total mass one factors uniquely through `Prob X`.  This says what a probability measure
-- is, without any division; `normalize` (below) is the separate operation of dividing by mass.
record IsNormalizedInclusion
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC}
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open HomReasoning
  open MR C
  open Canonical.CartesianClosed CC using (⊤; !)
  private
    module M = Notation (MeasureMonad.monad MM)
    module inc = StrongMonad⇒ inc

  -- the component `ι X : Prob X ⇒ M X` of the inclusion: a probability measure on `X`, regarded as a measure
  open NT.NaturalTransformation inc.α public using () renaming (η to ι)

  field
    -- `Prob X` is the measures of mass one: `ι X` equalizes the mass `M !` with the unit measure `η ⊤ ∘ !`
    ι-equalizer : ∀ X → IsEqualizer (ι X) (M.₁ (! {X})) (M.η ⊤ ∘ !)

  -- a probability measure is determined by the measure it gives
  ι-mono : ∀ X → Mono (ι X)
  ι-mono X = IsEqualizer⇒Mono (ι-equalizer X)

-- Normalisation, an optional extension for inference: `normalize : M X ⇒ Prob X + 1` divides a measure by its mass.  It
-- is a left inverse of scaling a probability measure by an invertible weight (`normalize-scale`), and fails on the zero
-- measure (`normalize-zero`); the degenerate infinite-mass case is left unspecified.
record Normalization
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC} {SW : SemiringWeights CC}
  {AK : AdditiveKernels (MeasureMonad.monad MM)}
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM))
  (SC : SoftConditioning SW AK) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; !; ⟨_,_⟩)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open SoftConditioning SC
  private
    module M = Notation (MeasureMonad.monad MM)
    module Pr = Notation (ProbMonad.monad P)
    module inc = StrongMonad⇒ inc

  -- the component `ι X : Prob X ⇒ M X` of the inclusion
  open NT.NaturalTransformation inc.α using () renaming (η to ι)

  -- a weight with a multiplicative inverse
  Invertible : (⊤ ⇒ W) → Set (h ⊔ e)
  Invertible w = Σ (⊤ ⇒ W) λ w⁻¹ → μ* ∘ ⟨ w , w⁻¹ ⟩ ≈ η*

  field
    normalize : ∀ X → M.₀ X ⇒ Pr.₀ X + ⊤
    -- normalizing a probability measure scaled by an invertible weight gives it back
    normalize-scale : ∀ {X} (w : ⊤ ⇒ W) → Invertible w → (p : ⊤ ⇒ Pr.₀ X) →
      normalize X ∘ scale w (ι X ∘ p) ≈ i₁ ∘ p
    -- the zero measure cannot be normalized
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.₁ x ∘ zero ≈ i₂
