{-# OPTIONS --safe --without-K #-}

-- Excluded middle, named once.  Every module that needs classical logic takes `lem : LEM₀` (or `LEM₁`, `LEM ℓ`) as a
-- parameter; `docs/Classical.md` lists which modules do and why.
module QBS.Classical where

open import Level using (Level; zero; suc)
open import Data.Empty using (⊥)
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥′)
open import Data.Sum.Base using (_⊎_)

-- every proposition in `Set ℓ` is decided, refutation landing in `⊥` at the same level
LEM : ∀ ℓ → Set (suc ℓ)
LEM ℓ = ∀ (A : Set ℓ) → A ⊎ (A → ⊥′ {ℓ})

-- the commonest form: propositions in `Set`
LEM₀ : Set₁
LEM₀ = ∀ (P : Set) → P ⊎ (P → ⊥)

-- propositions in `Set₁`, refutation into `⊥ : Set` (the form `Analysis/CoinIntegral.lemOf` and `Analysis/Riesz` consume)
LEM₁ : Set₂
LEM₁ = ∀ (P : Set₁) → P ⊎ (P → ⊥)
