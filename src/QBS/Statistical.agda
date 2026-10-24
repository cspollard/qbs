{-# OPTIONS --safe --without-K #-}

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
import Categories.NaturalTransformation as NT

open import QBS.Probability using (ProbabilityInterface)

-- Soft conditioning, abstractly.  On top of a `ProbabilityInterface` we ask for
--   * a commutative monoid object W of weights (with absorbing zero),
--   * a commutative strong monad M of measures, containing Prob,
--   * `score : W ⇒ M 1`, multiplicative, with weight 0 the zero measure,
--   * countable sums and scaling on global elements of M, under which every
--     measure is a countable sum of scaled laws (s-finiteness), and countable
--     sums of kernels, in which bind is linear,
--   * normalisation M X ⇒ Prob X + 1, homogeneous under invertible weights.
record StatisticalInterface {o h e} ℓ (C : Category o h e) (ℛ : Category.Obj C)
    (CC : Canonical.CartesianClosed C) (P : ProbabilityInterface ℓ C ℛ CC)
    (CP : Cocartesian.BinaryCoproducts C) : Set (o ⊔ h ⊔ e ⊔ suc ℓ) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  private
    cartesian = Canonical.CartesianClosed.isCartesian CC
    monoidal = CM.CartesianMonoidal.monoidal cartesian
    braided = Symmetric.braided (CSM.symmetric C cartesian)
    module Pr = Monad (CommutativeMonad.M (ProbabilityInterface.commutativeMonad P))
  field
    -- weights
    W : Obj
    mulW : W × W ⇒ W
    oneW zeroW : ⊤ ⇒ W
    mul-assoc : ∀ {Z} (a b c : Z ⇒ W) →
      mulW ∘ ⟨ mulW ∘ ⟨ a , b ⟩ , c ⟩ ≈ mulW ∘ ⟨ a , mulW ∘ ⟨ b , c ⟩ ⟩
    mul-comm : ∀ {Z} (a b : Z ⇒ W) → mulW ∘ ⟨ a , b ⟩ ≈ mulW ∘ ⟨ b , a ⟩
    mul-one : ∀ {Z} (a : Z ⇒ W) → mulW ∘ ⟨ a , oneW ∘ ! ⟩ ≈ a
    mul-zero : ∀ {Z} (a : Z ⇒ W) → mulW ∘ ⟨ a , zeroW ∘ ! ⟩ ≈ zeroW ∘ !
    -- measures
    commutativeMonad : CommutativeMonad braided
  private
    module M = Monad (CommutativeMonad.M commutativeMonad)
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
    -- the zero measure on 1 (there is none on an empty space, so it is not asked for
    -- at every X); it is absorbing for bind
    zero : ⊤ ⇒ M.F.F₀ ⊤
    zero-bind : ∀ (k : ⊤ ⇒ M.F.F₀ ⊤) → M.μ.η ⊤ ∘ M.F.F₁ k ∘ zero ≈ zero
    -- soft conditioning
    score : W ⇒ M.F.F₀ ⊤
    score-zero : score ∘ zeroW ≈ zero
    score-mul : ∀ (a b : ⊤ ⇒ W) →
      score ∘ mulW ∘ ⟨ a , b ⟩ ≈ M.μ.η ⊤ ∘ M.F.F₁ (score ∘ b ∘ !) ∘ score ∘ a
    -- s-finiteness: countable sums and scaling of global elements
    sumM : ∀ {X} → (ℕ → ⊤ ⇒ M.F.F₀ X) → ⊤ ⇒ M.F.F₀ X
    scaleM : ∀ {X} → (⊤ ⇒ W) → (⊤ ⇒ M.F.F₀ X) → ⊤ ⇒ M.F.F₀ X
    scale-one : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) → scaleM oneW t ≈ t
    scale-mul : ∀ {X} (a b : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
      scaleM (mulW ∘ ⟨ a , b ⟩) t ≈ scaleM a (scaleM b t)
    scale-return : ∀ {X} (a : ⊤ ⇒ W) (x : ⊤ ⇒ X) →
      scaleM a (M.η.η X ∘ x) ≈ M.F.F₁ (x ∘ !) ∘ score ∘ a
    scale-sum : ∀ {X} (a : ⊤ ⇒ W) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
      scaleM a (sumM ts) ≈ sumM (λ n → scaleM a (ts n))
    sum-nat : ∀ {X Y} (f : X ⇒ Y) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
      M.F.F₁ f ∘ sumM ts ≈ sumM (λ n → M.F.F₁ f ∘ ts n)
    sum-join : ∀ {X} (ts : ℕ → ⊤ ⇒ M.F.F₀ (M.F.F₀ X)) →
      M.μ.η X ∘ sumM ts ≈ sumM (λ n → M.μ.η X ∘ ts n)
    scale-nat : ∀ {X Y} (f : X ⇒ Y) (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
      M.F.F₁ f ∘ scaleM a t ≈ scaleM a (M.F.F₁ f ∘ t)
    scale-join : ∀ {X} (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ (M.F.F₀ X)) →
      M.μ.η X ∘ scaleM a t ≈ scaleM a (M.μ.η X ∘ t)
    -- countable sums of kernels X ⇒ M Y (pointwise sums of measures); bind is linear in the kernel
    sumK : ∀ {X Y} → (ℕ → X ⇒ M.F.F₀ Y) → X ⇒ M.F.F₀ Y
    sumK-point : ∀ {X Y} (ks : ℕ → X ⇒ M.F.F₀ Y) (x : ⊤ ⇒ X) →
      sumK ks ∘ x ≈ sumM (λ n → ks n ∘ x)
    bind-sumK : ∀ {X Y} (ks : ℕ → X ⇒ M.F.F₀ Y) (t : ⊤ ⇒ M.F.F₀ X) →
      M.μ.η Y ∘ M.F.F₁ (sumK ks) ∘ t ≈ sumM (λ n → M.μ.η Y ∘ M.F.F₁ (ks n) ∘ t)
    -- every measure is a countable sum of scaled laws
    scaled-laws : ∀ {X} (t : ⊤ ⇒ M.F.F₀ X) →
      Σ (ℕ → ℛ ⇒ X) λ a → Σ (ℕ → ⊤ ⇒ W) λ w → Σ (ℕ → ProbabilityInterface.Measure P) λ μ →
        t ≈ sumM (λ n → scaleM (w n)
              (Monad⇒-id.α.η inclusion X ∘ ProbabilityInterface.law P (a n) (μ n)))
    -- normalisation: probabilities are fixed, the zero measure fails; the
    -- degenerate infinite-mass case is left unspecified
    normalize : ∀ X → M.F.F₀ X ⇒ Pr.F.F₀ X + ⊤
    normalize-prob : ∀ X → normalize X ∘ Monad⇒-id.α.η inclusion X ≈ i₁
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.F.F₁ x ∘ zero ≈ i₂
    normalize-scale : ∀ {X} (a b : ⊤ ⇒ W) → mulW ∘ ⟨ a , b ⟩ ≈ oneW →
      ∀ (t : ⊤ ⇒ M.F.F₀ X) → normalize X ∘ scaleM a t ≈ normalize X ∘ t
