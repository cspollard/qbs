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

-- The weights in a context `Z`: the morphisms `Z ⇒ W`, a semiring under the pointwise sum and product (`μ⁺ ∘ ⟨ a , b ⟩`,
-- `μ* ∘ ⟨ a , b ⟩`) with the constants `0` and `1` precomposed with `! : Z ⇒ ⊤`.  At `Z = ⊤` this is `Global`.
WeightsAt : ∀ {CC} → SemiringWeights CC → Category.Obj C → Semiring h e
WeightsAt {CC} SW Z = record
  { Carrier = Z ⇒ W
  ; _≈_ = _≈_
  ; _+_ = λ a b → μ⁺ ∘ ⟨ a , b ⟩
  ; _*_ = λ a b → μ* ∘ ⟨ a , b ⟩
  ; 0# = η⁺ ∘ !
  ; 1# = η* ∘ !
  ; isSemiring = {!!}
  }
  where
    open Category C
    open Canonical.CartesianClosed CC using (!; ⟨_,_⟩)
    open Algebra.CommutativeSemiring SW renaming (Carrier to W)

-- The scalars in a context `Z` of a commutative additive monad `M`: the kernels `K [ Z , ⊤ ]`, i.e. the measures on the
-- one-point space depending on `Z`.  The sum is `⊕`, `0` is `𝟘` and `1` the Dirac mass.  The product `f ⋆ g` runs `f`,
-- then `g` in the same context (the strength of `M`); at `Z = ⊤` it is Kleisli composition (`kleisli-semiring ⊤`).
module Scalars (cm : CartCommMonad CC) (AK : IsAdditive (CommutativeMonad.M cm)) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; !; _×_; π₁; ⟨_,_⟩)
  open IsAdditive AK using (𝟘; _⊕_)
  private
    module M = Notation (CommutativeMonad.M cm)
    module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))

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

-- Soft conditioning on a commutative monad `M` with additive kernels: a morphism `score : W ⇒ M ⊤`, the measure of mass
-- `w` on the one-point space, which is a semiring homomorphism from the weights to the scalars in every context `Z`
-- (`WeightsAt Z → ScalarsAt Z`, `a ↦ score ∘ a`).  Stated for all `Z`, it applies to weights depending on a context, and
-- the laws (`score` sends `1` to the Dirac mass, `0` to the zero measure, sums to `⊕` and products to `⋆`) are equations
-- of morphisms of `C`.  `M` is any such monad: nothing here uses probability or measures.
record SoftConditioning {CC : Canonical.CartesianClosed C} (SW : SemiringWeights CC)
  (cm : CartCommMonad CC) (AK : IsAdditive (CommutativeMonad.M cm)) : Set (o ⊔ h ⊔ e) where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; !)
  open Algebra.CommutativeMonoidWithZero (Algebra.CommutativeSemiring.commutativeMonoidWithZero SW)
    renaming (Carrier to W) public
  open IsAdditive AK using (𝟘)
  open Scalars cm AK using (ScalarsAt)
  private
    module M = Notation (CommutativeMonad.M cm)
    K = Kleisli (CommutativeMonad.M cm)
    module K = Category K

  field
    -- the measure `score w` of mass `w` on the one-point space
    score : W ⇒ M.₀ ⊤
    -- precomposition with `score` is a semiring homomorphism in every context
    score-hom : ∀ Z → IsSemiringHomomorphism
      (Semiring.rawSemiring (WeightsAt SW Z)) (Semiring.rawSemiring (ScalarsAt Z)) (λ a → score ∘ a)

  -- the zero measure
  zero : K [ ⊤ , ⊤ ]
  zero = score ∘ zero⇒

  -- scaling a measure by a weight
  scale : (⊤ ⇒ W) → ∀ {X} → K [ ⊤ , X ] → K [ ⊤ , X ]
  scale w m = K [ m ∘ (score ∘ w) ]

  -- the zero measure is absorbing for bind: any kernel run after it gives the zero measure
  zero-bind : ∀ {Y} (k : K [ ⊤ , Y ]) → k K.∘ zero K.≈ 𝟘
  zero-bind k = {!!}

-- Normalisation, an optional extension for inference: `normalize : M X ⇒ Prob X + 1` divides a measure by its mass.  It
-- is a left inverse of scaling a probability measure by an invertible weight (`normalize-scale`), and fails on the zero
-- measure (`normalize-zero`); the degenerate infinite-mass case is left unspecified.
record Normalization
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC} {SW : SemiringWeights CC}
  {AK : IsAdditive (MeasureMonad.monad MM)}
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM))
  (SC : SoftConditioning SW (MeasureMonad.commutativeMonad MM) AK) : Set (o ⊔ h ⊔ e)
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
