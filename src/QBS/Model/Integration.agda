{-# OPTIONS --safe --without-K #-}

-- The discrete weights are an `Integration` (`QBS.Integration`): admissible weight functions `μ : R → A` with
-- pushforward, integrated by `⟦ μ ⟧ h = ∑ r, μ r * h r`.  The only fact needed is the projection formula `push-∑`
-- (`∫ h d(f_* μ) = ∫ h∘f dμ`); the functor laws of the measures come from `fromRaw`.
module QBS.Model.Integration where

open import Level using (Lift)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Construction.SubCategory using (Sub)
import Categories.Category.SubCategory.SubHom as SH

open import QBS.Core using (RandomSource)
open import QBS.Integration using (Integration; RawIntegration; fromRaw)
open import QBS.Model.DiscreteSource
open import QBS.Model.Monad using (WeightClass)
open import QBS.Model.Semiring
open import QBS.Model.Sums

module DiscreteIntegration {ℓ} (A : CompleteSemiring ℓ) (K : WeightClass A) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open WeightClass K
  open DS ℓ using (S)
  open RandomSource S using (subcat)

  -- test functions: all functions on the sample space, acted on by precomposition
  Test = SH.homPresheaf (Setoids ℓ ℓ) (Sub (Setoids ℓ ℓ) subcat) Aˢ

  weightsIntegration : Integration Test Aˢ
  weightsIntegration = fromRaw Test Aˢ record
    { Raw = λ _ → Σ (Lift ℓ ℕ → ∣A∣) Ok
    ; push = λ f (μ , ok) → push (proj₁ f ⟨$⟩_) μ , ok-push (proj₁ f ⟨$⟩_) ok
    ; ⟦_⟧ = λ (μ , _) → record
        { to = λ h → ∑ (λ r → μ r * (h ⟨$⟩ r))
        ; cong = λ e → ∑-cong (λ r → *-cong (Setoid.refl Aˢ) e)
        }
    ; ⟦⟧-push = λ f (μ , _) {h} → push-∑ (proj₁ f ⟨$⟩_) μ (h ⟨$⟩_)
    }
