{-# OPTIONS --safe --without-K #-}

-- Complete commutative semirings (Golan, *Semirings and their Applications*, §1):
-- semirings with sums over arbitrary index sets, associative over partitions and
-- distributing over multiplication.  The extended non-negative reals [0, ∞] are
-- the motivating example; measures in this development take values in an
-- arbitrary one, so the discrete model does not depend on a construction of ℝ.
module QBS.Model.Semiring where

open import Level using (Level; suc; _⊔_)
open import Function.Base using (_∘_)
open import Function.Bundles using (Inverse; _↔_)
open import Algebra.Bundles using (CommutativeSemiring)
import Algebra.Definitions as Defs
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

record CompleteSemiring (ℓ : Level) : Set (suc ℓ) where
  field
    commutativeSemiring : CommutativeSemiring ℓ ℓ
  open CommutativeSemiring commutativeSemiring public
  field
    ∑ : {I : Set ℓ} → (I → Carrier) → Carrier
    ∑-cong : ∀ {I} {f g : I → Carrier} → (∀ i → f i ≈ g i) → ∑ f ≈ ∑ g
    ∑-empty : ∀ (f : ⊥ {ℓ} → Carrier) → ∑ f ≈ 0#
    ∑-unit : ∀ (f : ⊤ {ℓ} → Carrier) → ∑ f ≈ f tt
    ∑-⊎ : ∀ {I J : Set ℓ} (f : I ⊎ J → Carrier) → ∑ f ≈ ∑ (f ∘ inj₁) + ∑ (f ∘ inj₂)
    -- partition associativity
    ∑-Σ : ∀ {I : Set ℓ} {J : I → Set ℓ} (f : Σ I J → Carrier) →
      ∑ f ≈ ∑ (λ i → ∑ (λ j → f (i , j)))
    ∑-reindex : ∀ {I J : Set ℓ} (e : I ↔ J) (f : J → Carrier) → ∑ (λ i → f (Inverse.to e i)) ≈ ∑ f
    ∑-distribˡ : ∀ {I : Set ℓ} x (f : I → Carrier) → x * ∑ f ≈ ∑ (λ i → x * f i)

  -- the decision "is m invertible?" (classical, so a hypothesis in `NormalizableSemiring`)
  InvDec : Carrier → Set ℓ
  InvDec m = Defs.RightInvertible _≈_ 1# _*_ m ⊎ (∀ n → m * n ≈ 1# → ⊥ {ℓ})

-- Normalisation needs to decide whether a total mass is invertible (i.e. neither 0
-- nor ∞, in [0, ∞]).  That is a classical decision, so it is a hypothesis.
record NormalizableSemiring (ℓ : Level) : Set (suc ℓ) where
  field
    complete : CompleteSemiring ℓ
  open CompleteSemiring complete public
  field
    invertible? : ∀ m → InvDec m
    nontrivial : 0# ≈ 1# → ⊥ {ℓ}
