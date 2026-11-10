{-# OPTIONS --safe --without-K #-}

-- Abstract soft conditioning and measures on top of a `ProbMonad`, as small independent structures, each with the laws it
-- needs and the operations derivable from it:
--   `Weights`               weights W: a commutative monoid object with an absorbing zero (`Monoidal.Symmetric.Algebra`);
--                           `SemiringWeights` also have addition
--   `IsAdditive`            the Kleisli category of a monad is enriched over commutative monoids (`Monad.Additive`)
--   `Global`                the semiring of global weights `1 ⇒ W` of `SemiringWeights`
--   `SoftConditioning`      `score : W ⇒ M 1`, a semiring homomorphism from the internal semiring `W` to the scalars of the
--                           Kleisli category (the laws are universal, with a strength); derives `score-hom`, its restriction
--                           to global weights (an object of `const! (Global SW) ↓ Scalars 1`), and `zero`, `scale`, `zero-bind`
--   `IsNormalizedInclusion` Prob is the normalized (mass one) part of a measure monad M: `ι : Prob ⇒ M` is an equalizer
--                           of mass and 1
--   `Normalization`         optional, for inference: `normalize : M X ⇒ Prob X + 1`
-- `zero⇒` (the weight 0) is an absorbing element of the multiplication, not a zero object.
open import Level using (_⊔_)
open import Data.Product.Base using (Σ; _,_)
open import Algebra.Bundles using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)

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
import Categories.Category.Cartesian.GlobalElements as GlobalElements
open import Categories.Monad using (Monad)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation as NT

import Categories.Monad.Notation as Notation
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import Categories.Monad.Additive using (IsAdditive)
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

-- The global weights `⊤ ⇒ W`, a semiring under the pointwise sum and product (`μ⁺ ∘ ⟨ w , w′ ⟩`, `μ* ∘ ⟨ w , w′ ⟩`).
Global : ∀ {CC} → SemiringWeights CC → Semiring h e
Global {CC} = GlobalElements.globalSemiring (Canonical.CartesianClosed.isCartesian CC)

-- Soft conditioning on a monad `M` with additive kernels: a semiring homomorphism from the global weights `⊤ ⇒ W` to the
-- scalars `kleisli-semiring ⊤` of the Kleisli category `K` of `M` (the kernels `⊤ ⇒ M ⊤` under `⊕` and Kleisli
-- composition), i.e. an object of the comma category `const! (Global SW) ↓ Scalars ⊤`.  `score w` is the measure of
-- mass `w` on the one-point space, and the homomorphism laws say that `score` sends sums of weights to sums of measures,
-- products to Kleisli composites, `0` to the zero measure and `1` to the Dirac mass.  `M` is any additive monad:
-- nothing here uses probability or measures.  Scaling a measure `m : ⊤ ⇒ M X` by a weight `w` is `K [ m ∘ score w ]`.
record SoftConditioning {CC : Canonical.CartesianClosed C} (SW : SemiringWeights CC) {M : Monad C}
  (AK : IsAdditive M) : Set (o ⊔ h ⊔ e) where

  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  open Algebra.CommutativeMonoidWithZero (Algebra.CommutativeSemiring.commutativeMonoidWithZero SW)
    renaming (Carrier to W) public
  open IsAdditive AK
  private
    K = Kleisli M
    module K = Category K

  field
    score-hom : SemiringHomomorphism
      (Semiring.rawSemiring (Global SW)) (Semiring.rawSemiring (kleisli-semiring ⊤))

  open SemiringHomomorphism score-hom
    public
    using ()
    renaming (⟦_⟧ to score; 0#-homo to score-zero; 1#-homo to score-one)

  -- the zero measure
  zero : K [ ⊤ , ⊤ ]
  zero = score zero⇒

  -- scaling a measure by a weight
  scale : (⊤ ⇒ W) → ∀ {X} → K [ ⊤ , X ] → K [ ⊤ , X ]
  scale w m = K [ m ∘ score w ]

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
  {AK : IsAdditive (MeasureMonad.monad MM)}
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
