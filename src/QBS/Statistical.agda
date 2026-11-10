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
open import Data.Product.Base using (Σ; _,_)
open import Algebra.Bundles using (Semiring)
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
open import Categories.Monad.Strong using (Strength)
import Categories.Category.Cartesian.Monoidal as CMon
open import QBS.Monad.Probability using (ProbMonad)

-- Weights: a commutative monoid object with an absorbing zero (`Categories.Category.Monoidal.Symmetric.Algebra`) for
-- the symmetric monoidal structure of the products of `CC`.  `Mul` is the multiplication, whose unit is the weight 1;
-- `zero⇒` is the weight 0, absorbing for `Mul` (`zeroʳ`).
Weights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
Weights CC = Algebra.CommutativeMonoidWithZero (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- Weights that can also be added (e.g. `[0,∞]`): a commutative semiring; `commutativeMonoidWithZero` forgets to `Weights`.
SemiringWeights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
SemiringWeights CC = Algebra.CommutativeSemiring (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- a (left) strength of a monad for the cartesian product of `CC`
CartStrength : Canonical.CartesianClosed C → Monad C → Set (o ⊔ h ⊔ e)
CartStrength CC = Strength (CMon.CartesianMonoidal.monoidal (Canonical.CartesianClosed.isCartesian CC))

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

-- Additive kernels: the Kleisli category `K` of `M` is enriched over commutative monoids.  Equivalently, on the hom
-- functor `Kᵒᵖ × K → Setoids`, `⊕ : Hom × Hom ⇒ Hom` and `𝟘 : 1 ⇒ Hom` are natural transformations making each
-- hom-setoid a commutative monoid.  `isCommutativeMonoid` is the monoid laws on each `K [ X , Y ]`; `⊕-resp-∘` and
-- `𝟘-resp-∘` are the naturality of `⊕` and `𝟘`, i.e. composition (bind) commutes with them in each argument.
record AdditiveKernels (M : Monad C) : Set (o ⊔ h ⊔ e) where

  private
    K = Kleisli M
    module K = Category K

  infixl 6 _⊕_
  field
    -- A zero morphism in the kleisli category that is the unit of ⊕
    𝟘 : ∀ {X Y} → K [ X , Y ]
    _⊕_ : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ]
    isCommutativeMonoid : ∀ {X Y} → IsCommutativeMonoid (K._≈_ {X} {Y}) _⊕_ 𝟘

    -- bind (Kleisli _∘_) is linear in the kernel run before,
    -- the kernel run after, and the continuation
    ⊕-resp-∘
      : ∀ {A B C D}
      → (k : K [ C , D ]) (f g : K [ B , C ]) (h : K [ A , B ])
      → k K.∘ (f ⊕ g) K.∘ h K.≈ (k K.∘ f K.∘ h) ⊕ (k K.∘ g K.∘ h)

    𝟘-resp-∘
      : ∀ {A B C D}
      → (k : K [ C , D ]) (h : K [ A , B ])
      → k K.∘ 𝟘 {B} {C} K.∘ h K.≈ 𝟘

  open K.HomReasoning

  ⊕-cong : ∀ {X Y} {a b c d : K [ X , Y ]} → a K.≈ b → c K.≈ d → (a ⊕ c) K.≈ (b ⊕ d)
  ⊕-cong = IsCommutativeMonoid.∙-cong isCommutativeMonoid

  -- composition on one side distributes over `⊕` (`⊕-resp-∘` with the other kernel the identity)
  ⊕-distribˡ
    : ∀ {A B D} (k : K [ B , D ]) (f g : K [ A , B ])
    → k K.∘ (f ⊕ g) K.≈ (k K.∘ f) ⊕ (k K.∘ g)
  ⊕-distribˡ k f g = begin
    k K.∘ (f ⊕ g)              ≈⟨ K.∘-resp-≈ʳ (⟺ K.identityʳ) ⟩
    k K.∘ (f ⊕ g) K.∘ K.id     ≈⟨ ⊕-resp-∘ k f g K.id ⟩
    (k K.∘ f K.∘ K.id) ⊕ (k K.∘ g K.∘ K.id)
                               ≈⟨ ⊕-cong (K.∘-resp-≈ʳ K.identityʳ) (K.∘-resp-≈ʳ K.identityʳ) ⟩
    (k K.∘ f) ⊕ (k K.∘ g)      ∎

  ⊕-distribʳ
    : ∀ {A C D} (f g : K [ C , D ]) (h : K [ A , C ])
    → (f ⊕ g) K.∘ h K.≈ (f K.∘ h) ⊕ (g K.∘ h)
  ⊕-distribʳ f g h = begin
    (f ⊕ g) K.∘ h              ≈⟨ ⟺ K.identityˡ ⟩
    K.id K.∘ (f ⊕ g) K.∘ h     ≈⟨ ⊕-resp-∘ K.id f g h ⟩
    (K.id K.∘ f K.∘ h) ⊕ (K.id K.∘ g K.∘ h) ≈⟨ ⊕-cong K.identityˡ K.identityˡ ⟩
    (f K.∘ h) ⊕ (g K.∘ h)      ∎

  -- The endomorphism semiring of an object `X` of the Kleisli category: `(⊕, 𝟘)` and `(K.∘, K.id)`, distributing by
  -- `⊕-resp-∘` and annihilating by `𝟘-resp-∘`.  At `X = ⊤` these are the scalars of `SoftConditioning`.
  End : Category.Obj C → Semiring h e
  End X = record
    { Carrier = K [ X , X ] ; _≈_ = K._≈_ ; _+_ = _⊕_ ; _*_ = K._∘_ ; 0# = 𝟘 ; 1# = K.id
    ; isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = isCommutativeMonoid
        ; *-cong = K.∘-resp-≈
        ; *-assoc = λ _ _ _ → K.assoc
        ; *-identity = (λ _ → K.identityˡ) , (λ _ → K.identityʳ)
        ; distrib = ⊕-distribˡ , (λ h f g → ⊕-distribʳ f g h)
        }
      ; zero = (λ x → K.Equiv.trans (K.Equiv.sym K.identityˡ) (𝟘-resp-∘ K.id x))
             , (λ x → K.Equiv.trans (K.∘-resp-≈ʳ (K.Equiv.sym K.identityʳ)) (𝟘-resp-∘ x K.id))
      }
    }

-- Soft conditioning on a monad `M` with additive kernels.  The weights `W` are a semiring in `C`; the scalars of the
-- Kleisli category `K` of `M` are the kernels `1 ⇒ M 1`, a semiring under `⊕` and Kleisli composition.  `score : W ⇒ M 1`
-- is the measure of mass `w`, and the laws say that it is a semiring homomorphism from the global weights `1 ⇒ W` to the
-- scalars.  The laws are stated at global elements (`score-add` as one equation of kernels `W × W ⇒ M 1`), so no strength is
-- needed yet and `M` is any monad: nothing here uses
-- probability or measures.  Scaling a measure `m : 1 ⇒ M X` by a weight `w` is the Kleisli composite `K [ m ∘ score ∘ w ]`.
record SoftConditioning {CC : Canonical.CartesianClosed C} (SW : SemiringWeights CC) {M : Monad C}
  (S : CartStrength CC M) (AK : AdditiveKernels M) : Set (o ⊔ h ⊔ e) where

  open Category C
  open HomReasoning
  open MR C using (pullʳ; cancelˡ)
  open Canonical.CartesianClosed CC using (⊤; _×_; π₁; π₂; ⟨_,_⟩; π₁-comp; π₂-comp)
  open Algebra.CommutativeMonoidWithZero (Algebra.CommutativeSemiring.commutativeMonoidWithZero SW)
    renaming (Carrier to W) public
  open Algebra.CommutativeSemiring SW using (μ⁺)
  open AdditiveKernels AK
  private
    module M = Notation M
    module S = Strength S
    K = Kleisli M
    module K = Category K

  field
    -- the weight `w` as a measure on the one-point space with total mass `w`
    score : W ⇒ M.₀ ⊤
    -- the weight 1 is the Dirac mass
    score-one : score ∘ η* ≈ M.η ⊤
    -- the weight 0 is the zero measure
    score-zero : score ∘ zero⇒ ≈ 𝟘 {⊤} {⊤}
    -- the product of weights is the composite of the scores, as one equation of kernels `W × W ⇒ M 1`: run
    -- `score w`, then `score w′` in the context `(w , w′)`, which the strength carries along
    score-mul
      : score ∘ μ* ≈ M.μ ⊤ ∘ M.₁ (score ∘ π₂ ∘ π₁) ∘ S.strengthen.η (W × W , ⊤) ∘ ⟨ id , score ∘ π₁ ⟩
    -- the sum of weights is the sum of the scores, as one equation of kernels `W × W ⇒ M 1`; at global elements
    -- `w w′ : 1 ⇒ W` it is `score-add-global`
    score-add : score ∘ μ⁺ ≈ (score ∘ π₁) ⊕ (score ∘ π₂)

  -- running a pure kernel `η ∘ g` first is precomposing with `g`
  ∘-pure : ∀ {A B Z} (f : K [ B , Z ]) (g : A ⇒ B) → f K.∘ (M.η B ∘ g) K.≈ f ∘ g
  ∘-pure {B = B} {Z} f g = begin
    (M.μ Z ∘ M.₁ f) ∘ (M.η B ∘ g)  ≈⟨ assoc ⟩
    M.μ Z ∘ (M.₁ f ∘ (M.η B ∘ g))  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    M.μ Z ∘ ((M.₁ f ∘ M.η B) ∘ g)  ≈⟨ refl⟩∘⟨ M.η-sym-commute f ⟩∘⟨refl ⟩
    M.μ Z ∘ ((M.η (M.₀ Z) ∘ f) ∘ g) ≈⟨ refl⟩∘⟨ assoc ⟩
    M.μ Z ∘ (M.η (M.₀ Z) ∘ (f ∘ g)) ≈⟨ cancelˡ (Monad.identityʳ M) ⟩
    f ∘ g                          ∎

  -- a sum of weights is the sum of the scores, at global elements
  score-add-global : ∀ (w w′ : ⊤ ⇒ W) → score ∘ μ⁺ ∘ ⟨ w , w′ ⟩ ≈ (score ∘ w) ⊕ (score ∘ w′)
  score-add-global w w′ = begin
    score ∘ μ⁺ ∘ ⟨ w , w′ ⟩                  ≈⟨ sym-assoc ⟩
    (score ∘ μ⁺) ∘ ⟨ w , w′ ⟩                ≈⟨ ⟺ (∘-pure (score ∘ μ⁺) ⟨ w , w′ ⟩) ⟩
    (score ∘ μ⁺) K.∘ p                       ≈⟨ K.∘-resp-≈ˡ score-add ⟩
    ((score ∘ π₁) ⊕ (score ∘ π₂)) K.∘ p      ≈⟨ ⊕-distribʳ _ _ _ ⟩
    ((score ∘ π₁) K.∘ p) ⊕ ((score ∘ π₂) K.∘ p) ≈⟨ ⊕-cong (∘-pure _ _) (∘-pure _ _) ⟩
    ((score ∘ π₁) ∘ ⟨ w , w′ ⟩) ⊕ ((score ∘ π₂) ∘ ⟨ w , w′ ⟩)
                                             ≈⟨ ⊕-cong (pullʳ π₁-comp) (pullʳ π₂-comp) ⟩
    (score ∘ w) ⊕ (score ∘ w′)               ∎
    where
    p : K [ ⊤ , W × W ]
    p = M.η (W × W) ∘ ⟨ w , w′ ⟩

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
  {S : CartStrength CC (MeasureMonad.monad MM)}
  {AK : AdditiveKernels (MeasureMonad.monad MM)}
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM))
  (SC : SoftConditioning SW S AK) : Set (o ⊔ h ⊔ e)
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
