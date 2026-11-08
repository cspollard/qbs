{-# OPTIONS --safe --without-K #-}

-- The classical decision toolkit: with `lem : LEM ℓ`, every proposition in `Set ℓ` has a Boolean truth value
-- `dec P` that is `true` exactly when `P` holds.  It is how sums over `Set`-indexed families are resized into a
-- smaller universe (`Model/BoolSemiring`, `Model/ViterbiSemiring`, `Analysis/CutSum`, `Analysis/CoinIntegral`).
-- `open Decide lem` brings `dec`, `dec-true`, `dec-false`, `from-true` and `dec-iff` into scope.
-- `LEM₁` (refutation into the monomorphic `⊥`) is turned into `LEM 1` by `fromLEM₁`.
module QBS.Classical.Decide where

open import Level using (Level; suc; zero; lift)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base using (inj₁; inj₂; map)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import QBS.Classical using (LEM; LEM₁)

-- `Set₁` excluded middle in the form `LEM 1` (the monomorphic `⊥` lifted)
fromLEM₁ : LEM₁ → LEM (suc zero)
fromLEM₁ lem₁ P = map id (λ n p → lift (n p)) (lem₁ P)

module Decide {ℓ : Level} (lem : LEM ℓ) where

  private
    exfalso : ∀ {a} {A : Set a} → ⊥ {ℓ} → A
    exfalso ()

  -- classical truth value of a proposition
  dec : (P : Set ℓ) → Bool
  dec P with lem P
  ... | inj₁ _ = true
  ... | inj₂ _ = false

  dec-true : ∀ {P} → P → dec P ≡ true
  dec-true {P} p with lem P
  ... | inj₁ _ = refl
  ... | inj₂ np = exfalso (np p)

  dec-false : ∀ {P} → (P → ⊥ {ℓ}) → dec P ≡ false
  dec-false {P} np with lem P
  ... | inj₁ p = exfalso (np p)
  ... | inj₂ _ = refl

  from-true : ∀ {P} → dec P ≡ true → P
  from-true {P} e with lem P
  ... | inj₁ p = p

  dec-iff : ∀ {P Q : Set ℓ} → (P → Q) → (Q → P) → dec P ≡ dec Q
  dec-iff {P} {Q} f g with lem P | lem Q
  ... | inj₁ _ | inj₁ _ = refl
  ... | inj₂ _ | inj₂ _ = refl
  ... | inj₁ p | inj₂ nq = exfalso (nq (f p))
  ... | inj₂ np | inj₁ q = exfalso (np (g q))
