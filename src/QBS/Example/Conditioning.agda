{-# OPTIONS --safe --without-K #-}

-- Rejection-style conditioning with `do`-notation: the programs of `Example/Program.agda` over the
-- sub-probability measures of `Model/SubProb.agda`, where `guard` discards runs and the missing
-- mass is the probability of rejection.  `∫ p g` is then the *unnormalised* expectation.
module QBS.Example.Conditioning where

import Level as L
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵖ)
open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core using (constₛ)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.SubProb
open import QBS.Example.Program

module Conditioning (A : CompleteSemiring L.zero) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open SetoidReasoning Aˢ
  open Programs A (subClass A) (λ p → 0# , trans (+-identityʳ _) p)
  open Pre

  -- discard the run
  reject : Prog ⊤
  reject = mk (constₛ tt) ttᵖ (λ _ → 0#)
    (1# , trans (+-cong (∑-zero (λ _ → 0#) (λ _ → refl)) refl) (+-identityˡ 1#))

  guard : Bool → Prog ⊤
  guard true = pure tt
  guard false = reject

  -- E[guard c >> k] is E[k] if c holds and 0 otherwise
  ∫-guard : ∀ {U} (c : Bool) (k : Prog U) (g : U → ∣A∣) →
    ∫ (guard c >> k) (test g) ≈ (if c then ∫ k (test g) else 0#)
  ∫-guard true k g = trans (∫-bind (pure tt) (λ _ → k) g) (∫-pure-bind k g)
    where
      ∫-pure-bind : ∀ {U} (k : Prog U) (g : U → ∣A∣) →
        ∑ (λ r → μ (pure tt) r * ∫ k (test g)) ≈ ∫ k (test g)
      ∫-pure-bind k g = dirac-∑ (L.lift 0) (λ _ → ∫ k (test g))
  ∫-guard false k g = trans (∫-bind reject (λ _ → k) g)
    (trans (∑-cong (λ r → zeroˡ _)) (∑-zero (λ _ → 0#) (λ _ → refl)))

  -- the guarded `pure`
  ∫-guard-pure : ∀ {T : Set} (c : Bool) (a : T) (g : T → ∣A∣) →
    ∫ (guard c >> pure a) (test g) ≈ (if c then g a else 0#)
  ∫-guard-pure true a g = trans (∫-guard true (pure a) g) (∫-pure a g)
  ∫-guard-pure false a g = ∫-guard false (pure a) g

  module Rejection (half : ∣A∣) (half+half : half + half ≈ 1#) where
    open Flip half half+half Bool true false _∧_

    -- two fair coins, conditioned on at least one being true; returns the first
    atLeastOne : Prog Bool
    atLeastOne = do
      a ← flip
      b ← flip
      guard (a ∨ b)
      pure a

    -- unnormalised expectation: the rejected run (false, false) contributes 0
    ∫-atLeastOne : ∀ (g : Bool → ∣A∣) → ∫ atLeastOne (test g) ≈
      half * (half * g true + half * g true) + half * (half * g false + half * 0#)
    ∫-atLeastOne g = trans (∫-flip->>= (λ a → flip >>= λ b → guard (a ∨ b) >> pure a) g)
      (+-cong
        (*-cong refl (trans (∫-flip->>= (λ b → guard (true ∨ b) >> pure true) g)
          (+-cong (*-cong refl (∫-guard-pure true true g))
                  (*-cong refl (∫-guard-pure true true g)))))
        (*-cong refl (trans (∫-flip->>= (λ b → guard (false ∨ b) >> pure false) g)
          (+-cong (*-cong refl (∫-guard-pure true false g))
                  (*-cong refl (∫-guard-pure false false g))))))
