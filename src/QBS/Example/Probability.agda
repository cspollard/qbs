{-# OPTIONS --safe --without-K #-}

-- Real probabilities with `do`-notation: the programs of `Example/Program.agda` over the additive
-- semiring ([0,∞], +, ×) of lower cuts.  The coin's outcomes are `Lift ℓ Bool` (the weights live at
-- level 1) and `half` is the cut of rationals below ½.  Two fair coins give
--   * `∫ both (indicator of true) ≈ half * half` (the probability that both are true is ¼),
--   * `∫ both 1 ≈ 1` (the total mass is one),
-- derived from the generic expectation rule `∫-both` by semiring algebra.  The calculation is
-- generic in a complete semiring with an element `half` (`half + half ≈ 1`); it is instantiated at
-- the additive semiring at the end.  (Doing the algebra at the concrete semiring makes Agda unfold
-- the cuts, so the generic form is much faster and more robust.)
module QBS.Example.Probability where

import Level as L
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty.Polymorphic using (⊥)
import Data.Empty as E
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)

open import QBS.Model.Semiring
open import QBS.Model.WeightClasses using (probClass)
open import QBS.Model.AdditiveSemiring
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Example.Program
open import QBS.Classical using (LEM)

module Calculation {ℓ} (A : CompleteSemiring ℓ) (half : CompleteSemiring.Carrier A)
    (hh : CompleteSemiring._≈_ A (CompleteSemiring._+_ A half half) (CompleteSemiring.1# A)) where
  open CompleteSemiring A renaming (Carrier to ∣A∣)
  open Programs A (probClass A) (λ p → p)

  -- outcomes of a coin
  B : Set ℓ
  B = L.Lift ℓ Bool

  _∧B_ : B → B → B
  L.lift a ∧B L.lift b = L.lift (a ∧ b)

  open Flip half hh B (L.lift true) (L.lift false) _∧B_

  isTrue : B → ∣A∣
  isTrue (L.lift true) = 1#
  isTrue (L.lift false) = 0#

  private
    one-one : half * 1# + half * 1# ≈ 1#
    one-one = trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh

    one-zero : half * 1# + half * 0# ≈ half
    one-zero = trans (+-cong (*-identityʳ half) (zeroʳ half)) (+-identityʳ half)

    zero-zero : half * 0# + half * 0# ≈ 0#
    zero-zero = trans (+-cong (zeroʳ half) (zeroʳ half)) (+-identityˡ 0#)

  -- P(both coins are true) = ½ · ½
  both-true : ∫ both (test isTrue) ≈ half * half
  both-true = trans (∫-both isTrue)
    (trans (+-cong (*-cong refl one-zero) (*-cong refl zero-zero))
      (trans (+-cong refl (zeroʳ half)) (+-identityʳ (half * half))))

  -- the total mass is one
  both-mass : ∫ both (test (λ _ → 1#)) ≈ 1#
  both-mass = trans (∫-both (λ _ → 1#))
    (trans (+-cong (*-cong refl one-one) (*-cong refl one-one))
      (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh))

  -- two quarters make a half
  quarter+quarter : half * half + half * half ≈ half
  quarter+quarter = trans (sym (distribˡ half half half)) (trans (*-cong refl hh) (*-identityʳ half))

-- the additive semiring ([0,∞], +, ×), with ½ the cut of rationals below ½
private
  ℓ₁ = L.suc L.zero

module Additive (lem₁ : LEM ℓ₁) where
  private
    lemS : ∀ (P : Set) → P ⊎ (P → E.⊥)
    lemS P with lem₁ (L.Lift ℓ₁ P)
    ... | inj₁ (L.lift p) = inj₁ p
    ... | inj₂ n = inj₂ (λ p → case n (L.lift p) of λ ())

  open Arch (lowerRealsArch lemS) using (half) renaming (half+half to hh)
  open Calculation (additiveComplete lem₁) half hh public
