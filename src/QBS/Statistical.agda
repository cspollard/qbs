{-# OPTIONS --safe --without-K #-}

-- `StatisticalInterface`: abstract soft conditioning on top of a `ProbabilityInterface`, assembled from
-- small structures, each with the laws it needs and the operations derivable from it:
--   `CommutativeMonoidWithZero`   weights W: a commutative monoid object with an absorbing zero
--   `SubMonad`       a commutative strong monad M of measures containing Prob as a sub-monad
--   `Score`          the zero measure and `score : W ⇒ M 1`, multiplicative; it defines `scaleM`, scaling of a
--                    global measure by a weight (a bind through `score`), and proves its laws
--   `CountableSums`         countable sums `sumK` of kernels (s-finiteness); `sumM` is the case of global measures
--   `Normalization` `normalize : M X ⇒ Prob X + 1`, homogeneous under invertible weights
-- The interface adds that every measure is a countable sum of scaled laws.
-- Instances: `Model/StatInstance` (discrete), `Continuous/SFiniteStat`.
module QBS.Statistical where

open import Level using (Level; suc; _⊔_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.Cartesian.Monoidal as CM
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import Categories.Monad.Strong using (StrongMonad; Strength)
import Categories.Morphism.Reasoning as MR
import Categories.NaturalTransformation as NT

open import QBS.Probability using (ProbabilityInterface)

-- A commutative monoid object of weights, with an absorbing zero (`zero⇒ : ⊤ ⇒ W`, an absorbing element
-- of the multiplication, not a zero object of the category).
record CommutativeMonoidWithZero {o h e} (C : Category o h e) (CC : Canonical.CartesianClosed C) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩)
  field
    W : Obj
    mulW : W × W ⇒ W
    oneW zeroâ : ⊤ ⇒ W
    mul-assoc : ∀ {Z} (a b c : Z ⇒ W) →
      mulW ∘ ⟨ mulW ∘ ⟨ a , b ⟩ , c ⟩ ≈ mulW ∘ ⟨ a , mulW ∘ ⟨ b , c ⟩ ⟩
    mul-comm : ∀ {Z} (a b : Z ⇒ W) → mulW ∘ ⟨ a , b ⟩ ≈ mulW ∘ ⟨ b , a ⟩
    mul-one : ∀ {Z} (a : Z ⇒ W) → mulW ∘ ⟨ a , oneW ∘ ! ⟩ ≈ a
    mul-zero : ∀ {Z} (a : Z ⇒ W) → mulW ∘ ⟨ a , zeroâ ∘ ! ⟩ ≈ zeroâ ∘ !

-- A commutative strong monad M of measures containing the probability monad as a sub-monad.
record SubMonad {o h e ℓ} {C : Category o h e} {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    (P : ProbabilityInterface ℓ C ℛ CC) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (_×_; ⟨_,_⟩; π₁; π₂)
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
    braided = Symmetric.braided (CSM.symmetric C cartesian)
  field
    commutativeMonad : CommutativeMonad braided
  private
    module τM = NT.NaturalTransformation
      (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad commutativeMonad)))
    module τP = NT.NaturalTransformation
      (Strength.strengthen (StrongMonad.strength
        (CommutativeMonad.strongMonad (ProbabilityInterface.commutativeMonad P))))
  field
    inclusion : Monad⇒-id (CommutativeMonad.M commutativeMonad)
                          (CommutativeMonad.M (ProbabilityInterface.commutativeMonad P))
    -- Prob is a sub-monad of M: the inclusion also respects strength
    inclusion-strong : ∀ A B →
      Monad⇒-id.α.η inclusion (A × B) ∘ τP.η (A , B) ≈ τM.η (A , B) ∘ ⟨ π₁ , Monad⇒-id.α.η inclusion B ∘ π₂ ⟩

-- The zero measure on 1 (there is none on an empty space, so it is not asked for at every X) and soft
-- conditioning `score : W ⇒ M 1`, multiplicative, with weight 0 the zero measure and weight 1 the unit.
-- Scaling a global measure by a weight is derived: `scaleM a t` is `t` bound through `score a`.
record Score {o h e ℓ} {C : Category o h e} {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    {P : ProbabilityInterface ℓ C ℛ CC} (WM : CommutativeMonoidWithZero C CC) (SM : SubMonad P) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; !-unique)
  open CommutativeMonoidWithZero WM
  private module M = Monad (CommutativeMonad.M (SubMonad.commutativeMonad SM))
  field
    -- the zero measure is absorbing for bind
    zero : ⊤ ⇒ M.F.F₀ ⊤
    zero-bind : ∀ (k : ⊤ ⇒ M.F.F₀ ⊤) → M.μ.η ⊤ ∘ M.F.F₁ k ∘ zero ≈ zero
    score : W ⇒ M.F.F₀ ⊤
    score-zero : score ∘ zeroâ ≈ zero
    score-one : score ∘ oneW ≈ M.η.η ⊤
    score-mul : ∀ (a b : ⊤ ⇒ W) →
      score ∘ mulW ∘ ⟨ a , b ⟩ ≈ M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a

  -- scaling a global measure by a global weight
  scaleM : ∀ {X} → (⊤ ⇒ W) → (⊤ ⇒ M.F.F₀ X) → ⊤ ⇒ M.F.F₀ X
  scaleM {X} a t = M.μ.η X ∘ M.F.F₁ t ∘ score ∘ a

  private
    open HomReasoning
    open MR C
    -- rewrite the front of a composite
    rw : ∀ {A B D E} {f : B ⇒ D} {g : A ⇒ B} {f′ : E ⇒ D} {g′ : A ⇒ E} {A′} {r : A′ ⇒ A} →
      f ∘ g ≈ f′ ∘ g′ → f ∘ g ∘ r ≈ f′ ∘ g′ ∘ r
    rw eq = sym-assoc ○ (eq ⟩∘⟨refl) ○ assoc
    ∘!≈ : ∀ {A} (b : ⊤ ⇒ A) → b ∘ ! ≈ b
    ∘!≈ b = (refl⟩∘⟨ !-unique id) ○ identityʳ

  scale-one : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) → scaleM oneW t ≈ t
  scale-one {X} t = begin
    M.μ.η X ∘ M.F.F₁ t ∘ score ∘ oneW  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ score-one ⟩
    M.μ.η X ∘ M.F.F₁ t ∘ M.η.η ⊤       ≈⟨ refl⟩∘⟨ M.η.sym-commute t ⟩
    M.μ.η X ∘ M.η.η (M.F.F₀ X) ∘ t     ≈⟨ cancelˡ M.identityʳ ⟩
    t                                  ∎

  scale-mul : ∀ {X} (a b : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
    scaleM (mulW ∘ ⟨ a , b ⟩) t ≈ scaleM a (scaleM b t)
  scale-mul {X} a b t = begin
    M.μ.η X ∘ M.F.F₁ t ∘ score ∘ mulW ∘ ⟨ a , b ⟩
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ score-mul a b ⟩
    M.μ.η X ∘ M.F.F₁ t ∘ M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ refl⟩∘⟨ rw (M.μ.sym-commute t) ⟩
    M.μ.η X ∘ M.μ.η (M.F.F₀ X) ∘ M.F.F₁ (M.F.F₁ t) ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ sym-assoc ⟩
    (M.μ.η X ∘ M.μ.η (M.F.F₀ X)) ∘ M.F.F₁ (M.F.F₁ t) ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ M.sym-assoc ⟩∘⟨refl ⟩
    (M.μ.η X ∘ M.F.F₁ (M.μ.η X)) ∘ M.F.F₁ (M.F.F₁ t) ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ assoc ⟩
    M.μ.η X ∘ M.F.F₁ (M.μ.η X) ∘ M.F.F₁ (M.F.F₁ t) ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.F.homomorphism) ⟩
    M.μ.η X ∘ M.F.F₁ (M.μ.η X ∘ M.F.F₁ t) ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.F.homomorphism) ⟩
    M.μ.η X ∘ M.F.F₁ ((M.μ.η X ∘ M.F.F₁ t) ∘ score ∘ b ∘ !) ∘ score ∘ a
      ≈⟨ refl⟩∘⟨ M.F.F-resp-≈ (refl⟩∘⟨ refl⟩∘⟨ ∘!≈ _) ⟩∘⟨refl ⟩
    M.μ.η X ∘ M.F.F₁ ((M.μ.η X ∘ M.F.F₁ t) ∘ score ∘ b) ∘ score ∘ a
      ≈⟨ refl⟩∘⟨ M.F.F-resp-≈ assoc ⟩∘⟨refl ⟩
    M.μ.η X ∘ M.F.F₁ (M.μ.η X ∘ M.F.F₁ t ∘ score ∘ b) ∘ score ∘ a ∎

  scale-return : ∀ {X} (a : ⊤ ⇒ W) (x : ⊤ ⇒ X) →
    scaleM a (M.η.η X ∘ x) ≈ M.F.F₁ (x ∘ !) ∘ score ∘ a
  scale-return {X} a x = begin
    M.μ.η X ∘ M.F.F₁ (M.η.η X ∘ x) ∘ score ∘ a  ≈⟨ refl⟩∘⟨ M.F.homomorphism ⟩∘⟨refl ⟩
    M.μ.η X ∘ (M.F.F₁ (M.η.η X) ∘ M.F.F₁ x) ∘ score ∘ a  ≈⟨ refl⟩∘⟨ assoc ⟩
    M.μ.η X ∘ M.F.F₁ (M.η.η X) ∘ M.F.F₁ x ∘ score ∘ a  ≈⟨ cancelˡ M.identityˡ ⟩
    M.F.F₁ x ∘ score ∘ a  ≈⟨ M.F.F-resp-≈ (⟺ (∘!≈ x)) ⟩∘⟨refl ⟩
    M.F.F₁ (x ∘ !) ∘ score ∘ a  ∎

  scale-nat : ∀ {X Y} (f : X ⇒ Y) (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
    M.F.F₁ f ∘ scaleM a t ≈ scaleM a (M.F.F₁ f ∘ t)
  scale-nat {X} {Y} f a t = begin
    M.F.F₁ f ∘ M.μ.η X ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ rw (M.μ.sym-commute f) ⟩
    M.μ.η Y ∘ M.F.F₁ (M.F.F₁ f) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.F.homomorphism) ⟩
    M.μ.η Y ∘ M.F.F₁ (M.F.F₁ f ∘ t) ∘ score ∘ a  ∎

  scale-join : ∀ {X} (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ (M.F.F₀ X)) →
    M.μ.η X ∘ scaleM a t ≈ scaleM a (M.μ.η X ∘ t)
  scale-join {X} a t = begin
    M.μ.η X ∘ M.μ.η (M.F.F₀ X) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ sym-assoc ⟩
    (M.μ.η X ∘ M.μ.η (M.F.F₀ X)) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ ⟺ M.assoc ⟩∘⟨refl ⟩
    (M.μ.η X ∘ M.F.F₁ (M.μ.η X)) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ assoc ⟩
    M.μ.η X ∘ M.F.F₁ (M.μ.η X) ∘ M.F.F₁ t ∘ score ∘ a  ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.F.homomorphism) ⟩
    M.μ.η X ∘ M.F.F₁ (M.μ.η X ∘ t) ∘ score ∘ a  ∎

-- Countable sums of kernels X ⇒ M Y (pointwise sums of measures), compatible with the monad: sums are
-- natural in the target, commute with join, and bind is linear in the kernel.  The sum of global measures
-- `sumM` is the case of kernels out of 1.
record CountableSums {o h e ℓ} {C : Category o h e} {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    {P : ProbabilityInterface ℓ C ℛ CC} (SM : SubMonad P) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  private module M = Monad (CommutativeMonad.M (SubMonad.commutativeMonad SM))
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
record Normalization {o h e ℓ} {C : Category o h e} {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    {P : ProbabilityInterface ℓ C ℛ CC} (CP : Cocartesian.BinaryCoproducts C)
    {WM : CommutativeMonoidWithZero C CC} {SM : SubMonad P} (Sc : Score WM SM) : Set (o ⊔ h ⊔ e) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; ⟨_,_⟩)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open CommutativeMonoidWithZero WM
  open Score Sc
  private
    module M = Monad (CommutativeMonad.M (SubMonad.commutativeMonad SM))
    module Pr = Monad (CommutativeMonad.M (ProbabilityInterface.commutativeMonad P))
  field
    normalize : ∀ X → M.F.F₀ X ⇒ Pr.F.F₀ X + ⊤
    normalize-prob : ∀ X → normalize X ∘ Monad⇒-id.α.η (SubMonad.inclusion SM) X ≈ i₁
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.F.F₁ x ∘ zero ≈ i₂
    normalize-scale : ∀ {X} (a b : ⊤ ⇒ W) → mulW ∘ ⟨ a , b ⟩ ≈ oneW →
      ∀ (t : ⊤ ⇒ M.F.F₀ X) → normalize X ∘ scaleM a t ≈ normalize X ∘ t

-- Soft conditioning, abstractly.  On top of a `ProbabilityInterface`: weights, a measure monad containing
-- Prob, `score`, countable sums, under which every measure is a countable sum of scaled laws
-- (s-finiteness), and normalisation.  The fields of the parts are re-exported.
record StatisticalInterface {o h e} ℓ (C : Category o h e) (ℛ : Category.Obj C)
    (CC : Canonical.CartesianClosed C) (P : ProbabilityInterface ℓ C ℛ CC)
    (CP : Cocartesian.BinaryCoproducts C) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  field
    weights : CommutativeMonoidWithZero C CC
    measures : SubMonad P
    scoring : Score weights measures
    sums : CountableSums measures
  open CommutativeMonoidWithZero weights public
  open SubMonad measures public
  open Score scoring public
  open CountableSums sums public
  private module M = Monad (CommutativeMonad.M (SubMonad.commutativeMonad measures))
  field
    -- every measure is a countable sum of scaled laws
    scaled-laws : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) →
      Σ (ℕ → ℛ ⇒ X) λ a → Σ (ℕ → ⊤ ⇒ W) λ w → Σ (ℕ → ProbabilityInterface.Measure P) λ μ →
        t ≈ sumM (λ n → scaleM (w n)
              (Monad⇒-id.α.η inclusion X ∘ ProbabilityInterface.law P (a n) (μ n)))
    normalization : Normalization CP scoring
  open Normalization normalization public

  -- scaling is linear in the measure: it commutes with countable sums (bind is linear in the kernel)
  scale-sum : ∀ {X} (a : ⊤ ⇒ W) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
    scaleM a (sumM ts) ≈ sumM (λ n → scaleM a (ts n))
  scale-sum a ts = bind-sumK ts (score ∘ a)
