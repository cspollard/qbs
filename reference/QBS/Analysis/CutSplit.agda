{-# OPTIONS --safe --without-K #-}

-- Totality of a lower real against the constant 1 (by excluded middle): `x ≤ 1` or `1 ≤ x`.  Either some member of x
-- is at least 1 (then every `q < 1` is in x), or none is (then every member of x is below 1).  This is what lets the
-- first-order exponential facts `1 ≤ e^{−u} + u` (proved for u ≤ 1) hold for all u.
module QBS.Analysis.CutSplit where

open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Unnormalised.Base using (ℚᵘ; _≤_; _<_; 1ℚᵘ)

open import QBS.Classical using (LEM₀)
open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_

split1 : LEM₀ → ∀ x → x ⊑ oneC ⊎ oneC ⊑ x
split1 lem x with lem (Σ ℚᵘ (λ r → mem x r × 1ℚᵘ ≤ r))
... | inj₁ (r , mr , 1≤r) = inj₂ (mk⊑ (λ q q<1 → down x (<-≤ (<-≤-trans q<1 1≤r)) mr))
... | inj₂ no = inj₁ (mk⊑ (λ q mq → bound q mq))
  where
  bound : ∀ q → mem x q → q < 1ℚᵘ
  bound q mq with ≤-or-> 1ℚᵘ q
  ... | inj₁ 1≤q = ⊥-elim (no (q , mq , 1≤q))
  ... | inj₂ q<1 = q<1
