{-# OPTIONS --safe --without-K #-}

-- Linearity of bind (in the measure argument): the Kleisli extension of a kernel preserves
-- countable sums and scaling of measures.  Both follow from naturality and join-compatibility.
module QBS.StatisticalLemmas where

open import Data.Nat.Base using (ℕ)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
import Categories.Morphism.Reasoning as MR

open import QBS.Probability using (ProbabilityInterface)
open import QBS.Statistical

module _ {o h e ℓ} {C : Category o h e} {ℛ : Category.Obj C} {CC : Canonical.CartesianClosed C}
    {P : ProbabilityInterface ℓ ℛ CC} {CP : Cocartesian.BinaryCoproducts C}
    (St : StatisticalInterface ℓ C ℛ CC P CP) where
  open Category C
  open Canonical.CartesianClosed CC using (⊤)
  open StatisticalInterface St
  private
    module M = Monad (CommutativeMonad.M commutativeMonad)
    open HomReasoning

  -- bind k t = μ ∘ M k ∘ t
  bind-sum : ∀ {X Y} (k : X ⇒ M.F.F₀ Y) (ts : ℕ → ⊤ ⇒ M.F.F₀ X) →
    M.μ.η Y ∘ M.F.F₁ k ∘ sumM ts ≈ sumM (λ n → M.μ.η Y ∘ M.F.F₁ k ∘ ts n)
  bind-sum {Y = Y} k ts = begin
    M.μ.η Y ∘ M.F.F₁ k ∘ sumM ts            ≈⟨ refl⟩∘⟨ sum-nat k ts ⟩
    M.μ.η Y ∘ sumM (λ n → M.F.F₁ k ∘ ts n)  ≈⟨ sum-join (λ n → M.F.F₁ k ∘ ts n) ⟩
    sumM (λ n → M.μ.η Y ∘ M.F.F₁ k ∘ ts n)  ∎

  bind-scale : ∀ {X Y} (k : X ⇒ M.F.F₀ Y) (a : ⊤ ⇒ W) (t : ⊤ ⇒ M.F.F₀ X) →
    M.μ.η Y ∘ M.F.F₁ k ∘ scaleM a t ≈ scaleM a (M.μ.η Y ∘ M.F.F₁ k ∘ t)
  bind-scale {Y = Y} k a t = begin
    M.μ.η Y ∘ M.F.F₁ k ∘ scaleM a t         ≈⟨ refl⟩∘⟨ scale-nat k a t ⟩
    M.μ.η Y ∘ scaleM a (M.F.F₁ k ∘ t)       ≈⟨ scale-join a (M.F.F₁ k ∘ t) ⟩
    scaleM a (M.μ.η Y ∘ M.F.F₁ k ∘ t)       ∎
