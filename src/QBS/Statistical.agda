{-# OPTIONS --safe --without-K #-}

-- `StatisticalInterface`: abstract soft conditioning on top of a `ProbMonad`, assembled from
-- small structures, each with the laws it needs and the operations derivable from it:
--   `Weights`        weights W: a commutative monoid object with an absorbing zero (`Monoidal.Symmetric.Algebra`)
--   `SubMonad`       a commutative strong monad M of measures containing Prob as a sub-monad
--   `Score`          the zero measure and `score : W ⇒ M 1`, multiplicative; it defines `scaleM`, scaling of a
--                    global measure by a weight (a bind through `score`), and proves its laws
--   `CountableSums`         countable sums `sumK` of kernels (s-finiteness); `sumM` is the case of global measures
--   `Normalization` `normalize : M X ⇒ Prob X + 1`, homogeneous under invertible weights
-- The interface adds that every measure is a countable sum of scaled laws (`scaled-laws`, the only field outside
-- the five sub-records, and the place where s-finiteness lives).
-- `zero⇒` (the weight 0) is an absorbing element of the multiplication, not a zero object.
-- Linearity: `bind-sumK` is linear in the kernel; `sum-nat`/`sum-join` are linear in the measure.  They are separate
-- axioms, not derivable from one another without a unit measure.
-- Bind vocabulary: a bind is `μ ∘ M k ∘ t` for a global measure `t` and kernel `k`.  It is named once, in `QBS.Monad.Bind`
-- (`bind k t`, Kleisli composition, unit/associativity laws); later modules should use that, not spell out
-- `μ ∘ M k ∘ t` (`scaleM a t` is `bind t (score ∘ a)`, and its laws are instances of the `Bind` laws).
-- Instances: `Model/StatInstance` (discrete), `Continuous/SFiniteStat`.
open import Level using (suc; _⊔_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_)

open import Categories.Category.Core using (Category)

module QBS.Statistical {o h e} {C : Category o h e} where

import Categories.Category.Monoidal.Symmetric.Algebra as Algebra
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Morphism using (Monad⇒-id)
import Categories.Morphism.Reasoning as MR
import Categories.Category.Monoidal.Properties as MonProps
import Categories.Category.Monoidal.Reasoning as MonReasoning
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Monad.Writer using (Writer)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
import Categories.NaturalTransformation as NT

open import QBS.Monad.Bind using (module Bind)
open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Probability using (ProbMonad; Inclusion)

-- Weights: a commutative monoid object with an absorbing zero (`Categories.Category.Monoidal.Symmetric.Algebra`) for
-- the symmetric monoidal structure of the products of `CC`.  `Mul` is the multiplication, whose unit is the weight 1;
-- `zero⇒` is the weight 0, absorbing for `Mul` (`zeroʳ`).  Soft conditioning needs no addition of weights.
Weights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
Weights CC = Algebra.CommutativeMonoidWithZero (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- Weights that can also be added (e.g. `[0,∞]`): a commutative semiring; `commutativeMonoidWithZero` forgets to `Weights`.
SemiringWeights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
SemiringWeights CC = Algebra.CommutativeSemiring (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- Soft conditioning: a monad morphism from the writer monad of the weights, `W × – ⇒ M` (`Categories.Monad.Writer`).
-- Its component at `X` scales a measure by a weight; at `1` it is `score : W ⇒ M 1`, the measure of mass `w`.  The unit
-- and multiplication laws of the morphism are `score 1 = η` and `score (ab) = score a >>= score b` (`score-one`,
-- `score-mul`).  The zero measure is the score of the weight 0, and absorbing for bind.
-- Scaling a global measure by a weight is derived: `scaleM a t` is `t` bound through `score a`.
record Score
  {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
  (WM : Weights CC) (MM : MeasureMonad ℛ CC)
  : Set (o ⊔ h ⊔ e) where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; !-unique)
  open Algebra.CommutativeMonoidWithZero WM renaming (Carrier to W)
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
    monoidal = CM.CartesianMonoidal.monoidal cartesian
    module Mon = Monoidal monoidal
    open Mon using (_⊗₁_)
    module Props = MonProps monoidal
    module M = Monad (CommutativeMonad.M (MeasureMonad.commutativeMonad MM))
  open Bind (CommutativeMonad.M (MeasureMonad.commutativeMonad MM))
  private
    -- the measure monad, and the writer monad of the weights
    Meas = CommutativeMonad.M (MeasureMonad.commutativeMonad MM)
    W×- = Writer Mul.monoid

  field
    -- the monad morphism `W×- ⇒ Meas` (`Monad⇒-id` names its target first)
    reweight : Monad⇒-id Meas W×-

  private module α = Monad⇒-id reweight

  score : W ⇒ M.F.F₀ ⊤
  score = α.α.η ⊤ ∘ Mon.unitorʳ.to

  zero : ⊤ ⇒ M.F.F₀ ⊤
  zero = score ∘ zero⇒

  field
    -- the zero measure is absorbing for bind
    zero-bind : ∀ (k : ⊤ ⇒ M.F.F₀ ⊤) → M.μ.η ⊤ ∘ M.F.F₁ k ∘ zero ≈ zero

  private
    open HomReasoning
    open MR C
    ∘!≈ : ∀ {A} (b : ⊤ ⇒ A) → b ∘ ! ≈ b
    ∘!≈ b = (refl⟩∘⟨ !-unique id) ○ identityʳ

  score-one : score ∘ Mul.η ≈ M.η.η ⊤
  score-one = begin
    (α.α.η ⊤ ∘ Mon.unitorʳ.to) ∘ Mul.η        ≈⟨ assoc ⟩
    α.α.η ⊤ ∘ Mon.unitorʳ.to ∘ Mul.η          ≈⟨ refl⟩∘⟨ Mon.unitorʳ-commute-to ⟩
    α.α.η ⊤ ∘ (Mul.η Mon.⊗₁ id) ∘ Mon.unitorʳ.to
                                              ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ Props.coherence-inv₃ ⟩
    α.α.η ⊤ ∘ (Mul.η Mon.⊗₁ id) ∘ Mon.unitorˡ.to
                                              ≈⟨ α.unit-comp ⟩
    M.η.η ⊤                                   ∎

  private
    module P = BinaryProducts (Cartesian.products cartesian)

    -- `score` at a global weight is the component at `1` applied to the pair `(a, *)`
    score-pt : ∀ (a : ⊤ ⇒ W) → score ∘ a ≈ α.α.η ⊤ ∘ ⟨ a , ! ⟩
    score-pt a = assoc ○ refl⟩∘⟨ (P.⟨⟩∘ ○ P.⟨⟩-cong₂ identityˡ (⟺ (!-unique (! ∘ a))))

  -- naturality of the morphism at a global element `t`: `α_{M 1} (a, t) = M t (score a)`
  α-pair : ∀ (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ ⊤) →
    α.α.η (M.F.F₀ ⊤) ∘ ⟨ a , t ⟩ ≈ M.F.F₁ t ∘ score ∘ a
  α-pair a t = begin
    α.α.η (M.F.F₀ ⊤) ∘ ⟨ a , t ⟩                ≈˘⟨ refl⟩∘⟨ (P.⁂∘⟨⟩ ○ P.⟨⟩-cong₂ identityˡ (∘!≈ t)) ⟩
    α.α.η (M.F.F₀ ⊤) ∘ (id ⊗₁ t) ∘ ⟨ a , ! ⟩    ≈⟨ pullˡ (α.α.commute t) ⟩
    (M.F.F₁ t ∘ α.α.η ⊤) ∘ ⟨ a , ! ⟩            ≈⟨ assoc ⟩
    M.F.F₁ t ∘ α.α.η ⊤ ∘ ⟨ a , ! ⟩              ≈˘⟨ refl⟩∘⟨ score-pt a ⟩
    M.F.F₁ t ∘ score ∘ a                        ∎

  -- the multiplication law of the morphism, at the point `(a, (b, *))`
  score-mul : ∀ (a b : ⊤ ⇒ W) →
    score ∘ Mul.μ ∘ ⟨ a , b ⟩ ≈ M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
  score-mul a b = begin
    score ∘ Mul.μ ∘ ⟨ a , b ⟩
      ≈⟨ score-pt _ ⟩
    α.α.η ⊤ ∘ ⟨ Mul.μ ∘ ⟨ a , b ⟩ , ! ⟩
      ≈˘⟨ refl⟩∘⟨ (P.⁂∘⟨⟩ ○ P.⟨⟩-cong₂ Equiv.refl identityˡ) ⟩
    α.α.η ⊤ ∘ (Mul.μ ⊗₁ id) ∘ ⟨ ⟨ a , b ⟩ , ! ⟩
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ P.assocʳ∘⟨⟩ ⟩
    α.α.η ⊤ ∘ (Mul.μ ⊗₁ id) ∘ Mon.associator.to ∘ ⟨ a , ⟨ b , ! ⟩ ⟩
      ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
    (α.α.η ⊤ ∘ (Mul.μ ⊗₁ id) ∘ Mon.associator.to) ∘ ⟨ a , ⟨ b , ! ⟩ ⟩
      ≈⟨ α.mult-comp ⟩∘⟨refl ⟩
    (M.μ.η ⊤ ∘ α.α.η (M.F.F₀ ⊤) ∘ id ⊗₁ α.α.η ⊤) ∘ ⟨ a , ⟨ b , ! ⟩ ⟩
      ≈⟨ assoc ○ refl⟩∘⟨ assoc ⟩
    M.μ.η ⊤ ∘ α.α.η (M.F.F₀ ⊤) ∘ (id ⊗₁ α.α.η ⊤) ∘ ⟨ a , ⟨ b , ! ⟩ ⟩
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (P.⁂∘⟨⟩ ○ P.⟨⟩-cong₂ identityˡ (⟺ (score-pt b))) ⟩
    M.μ.η ⊤ ∘ α.α.η (M.F.F₀ ⊤) ∘ ⟨ a , score ∘ b ⟩
      ≈⟨ refl⟩∘⟨ α-pair a (score ∘ b) ⟩
    M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b) ∘ score ∘ a
      ≈˘⟨ refl⟩∘⟨ M.F.F-resp-≈ (refl⟩∘⟨ ∘!≈ b) ⟩∘⟨refl ⟩
    M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a ∎

  -- scaling a global measure by a global weight
  scaleM : ∀ {X} → (⊤ ⇒ W) → (⊤ ⇒ M.F.F₀ X) → ⊤ ⇒ M.F.F₀ X
  scaleM {X} a t = M.μ.η X ∘ M.F.F₁ t ∘ score ∘ a

  scale-one : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) → scaleM Mul.η t ≈ t
  scale-one t = bind-cong Equiv.refl (score-one ○ ⟺ identityʳ) ○ bind-η t id ○ identityʳ

  scale-mul : ∀ {X} (a b : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
    scaleM (Mul.μ ∘ ⟨ a , b ⟩) t ≈ scaleM a (scaleM b t)
  scale-mul a b t =
    bind-cong Equiv.refl (score-mul a b) ○ bind-assoc t (score ∘ b ∘ !) (score ∘ a)
      ○ bind-cong (bind-cong Equiv.refl (refl⟩∘⟨ ∘!≈ b)) Equiv.refl

  scale-return : ∀ {X} (a : ⊤ ⇒ W) (x : ⊤ ⇒ X) →
    scaleM a (M.η.η X ∘ x) ≈ M.F.F₁ (x ∘ !) ∘ score ∘ a
  scale-return a x = bind-η-∘ x (score ∘ a) ○ M.F.F-resp-≈ (⟺ (∘!≈ x)) ⟩∘⟨refl

  scale-nat : ∀ {X Y} (f : X ⇒ Y) (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
    M.F.F₁ f ∘ scaleM a t ≈ scaleM a (M.F.F₁ f ∘ t)
  scale-nat f a t = bind-nat f t (score ∘ a)

  scale-join : ∀ {X} (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ (M.F.F₀ X)) →
    M.μ.η X ∘ scaleM a t ≈ scaleM a (M.μ.η X ∘ t)
  scale-join a t = bind-join t (score ∘ a)

-- Countable sums of kernels X ⇒ M Y (pointwise sums of measures), compatible with the monad: sums are
-- natural in the target, commute with join, and bind is linear in the kernel.  The sum of global measures
-- `sumM` is the case of kernels out of 1.
record CountableSums {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    (MM : MeasureMonad ℛ CC) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  private module M = Monad (CommutativeMonad.M (MeasureMonad.commutativeMonad MM))
  field
    sumK : ∀ {X Y} → (ℕ → X ⇒ M.F.F₀ Y) → X ⇒ M.F.F₀ Y
    sumK-point : ∀ {X Y} (ks : ℕ → X ⇒ M.F.F₀ Y) (x : ⊤ ⇒ X) →
      sumK ks ∘ x ≈ sumK (λ n → ks n ∘ x)
    bind-sumK : ∀ {X Y} (ks : ℕ → X ⇒ M.F.F₀ Y) (t : ⊤ ⇒ M.F.F₀ X) →
      M.μ.η Y ∘ M.F.F₁ (sumK ks) ∘ t ≈ sumK (λ n → M.μ.η Y ∘ M.F.F₁ (ks n) ∘ t)
    sum-nat : ∀ {X Y} (f : X ⇒ Y) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
      M.F.F₁ f ∘ sumK ts ≈ sumK (λ n → M.F.F₁ f ∘ ts n)
    sum-join : ∀ {X} (ts : ℕ → ⊤ ⇒ M.F.F₀ (M.F.F₀ X)) →
      M.μ.η X ∘ sumK ts ≈ sumK (λ n → M.μ.η X ∘ ts n)

  sumM : ∀ {X} → (ℕ → ⊤ ⇒ M.F.F₀ X) → ⊤ ⇒ M.F.F₀ X
  sumM = sumK

-- Normalisation M X ⇒ Prob X + 1: probabilities are fixed, the zero measure fails, and scaling by an
-- invertible weight does not change the result; the degenerate infinite-mass case is left unspecified.
record Normalization {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC} (I : Inclusion ℛ CC P MM) (CP : Cocartesian.BinaryCoproducts C)
    {WM : Weights CC} (Sc : Score WM MM) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; ⟨_,_⟩)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open Algebra.CommutativeMonoidWithZero WM renaming (Carrier to W)
  open Score Sc
  private
    module M = Monad (CommutativeMonad.M (MeasureMonad.commutativeMonad MM))
    module Pr = Monad (CommutativeMonad.M (ProbMonad.commutativeMonad P))
  field
    normalize : ∀ X → M.F.F₀ X ⇒ Pr.F.F₀ X + ⊤
    normalize-prob : ∀ X → normalize X ∘ Monad⇒-id.α.η (Inclusion.inclusion I) X ≈ i₁
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.F.F₁ x ∘ zero ≈ i₂
    normalize-scale : ∀ {X} (a b : ⊤ ⇒ W) → Mul.μ ∘ ⟨ a , b ⟩ ≈ Mul.η →
      ∀ (t : ⊤ ⇒ M.F.F₀ X) → normalize X ∘ scaleM a t ≈ normalize X ∘ t

-- Soft conditioning, abstractly.  On top of a `ProbMonad`: weights, a measure monad containing
-- Prob, `score`, countable sums, under which every measure is a countable sum of scaled laws
-- (s-finiteness), and normalisation.  The fields of the parts are re-exported.
record StatisticalInterface (ℛ : Category.Obj C)
    (CC : Canonical.CartesianClosed C) (P : ProbMonad ℛ CC)
    (CP : Cocartesian.BinaryCoproducts C) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  field
    weights : Weights CC
    measures : MeasureMonad ℛ CC
    probInclusion : Inclusion ℛ CC P measures
    conditioning : Score weights measures
    sums : CountableSums measures
  open Algebra.CommutativeMonoidWithZero weights renaming (Carrier to W) public
  open MeasureMonad measures public
  open Inclusion probInclusion public
  open Score conditioning public
  open CountableSums sums public
  private module M = Monad (CommutativeMonad.M (MeasureMonad.commutativeMonad measures))
  field
    -- every measure is a countable sum of scaled laws
    scaled-laws : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) →
      Σ (ℕ → ℛ ⇒ X) λ a → Σ (ℕ → ⊤ ⇒ W) λ w → Σ (ℕ → ProbMonad.Measure P) λ μ →
        t ≈ sumM (λ n → scaleM (w n)
              (Monad⇒-id.α.η inclusion X ∘ ProbMonad.pushforward P (a n) (μ n)))
    normalization : Normalization probInclusion CP conditioning
  open Normalization normalization public

  -- scaling is linear in the measure: it commutes with countable sums (bind is linear in the kernel)
  scale-sum : ∀ {X} (a : ⊤ ⇒ W) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
    scaleM a (sumM ts) ≈ sumM (λ n → scaleM a (ts n))
  scale-sum a ts = bind-sumK ts (score ∘ a)
