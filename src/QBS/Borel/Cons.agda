{-# OPTIONS --safe --without-K #-}

-- Prepending a bit to a sequence is a measurable map of Cantor space.
module QBS.Borel.Cons where

open import Level using (lift; lower)
open import Function.Base using (const)
open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (zero; suc)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down)
open import QBS.Analysis.Clopen using (cons)

consR : Bool → R₁ → R₁
consR b r = lift (cons b (lower r))

measurable-cons : ∀ b → Measurable (down (consR b))
measurable-cons b zero b′ = measurable-const (λ _ → b) zero b′
measurable-cons b (suc n) b′ = gen n b′
