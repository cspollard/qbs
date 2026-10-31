{-# OPTIONS --safe --without-K #-}

-- A worked Bayesian example with numbers: is the coin fair or two-headed?  The prior is a fair coin flip between the two
-- hypotheses (`true` = two-headed, `false` = fair); the data is one head, with likelihood 1 under "two-headed" and ½
-- under "fair".  The evidence is ½·1 + ½·½ = ¾, and the unnormalised posterior masses are ½ (two-headed) and ¼ (fair): the
-- posterior odds are 2 : 1, from prior odds 1 : 1.  Generic in a normalisable semiring with an element `half`.
module QBS.Inference.CoinBias where

import Level as L
import Data.Empty as E
open import Data.Empty.Polymorphic using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Unit.Polymorphic.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Model.Semiring
open import QBS.Model.WeightClasses using (allClass)
open import QBS.Model.AdditiveSemiring using (additiveNormalizable)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Example.Program using (module Programs)
open import QBS.Example.Bayes using (posteriorU; evidence; _·_; bayes-numerator)
open import QBS.Classical using (LEM)

module CoinBias {ℓ} (N : NormalizableSemiring ℓ) (half : NormalizableSemiring.Carrier N)
    (hh : NormalizableSemiring._≈_ N (NormalizableSemiring._+_ N half half) (NormalizableSemiring.1# N)) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Programs A (allClass A) (λ _ → tt)
  B = L.Lift ℓ Bool
  open Flip half hh B (L.lift true) (L.lift false) (λ _ b → b)

  -- the hypotheses, and the likelihood of a head under each
  heads : B → ∣A∣
  heads (L.lift true) = 1#
  heads (L.lift false) = half

  twoHeaded fair : B → ∣A∣
  twoHeaded (L.lift true) = 1#
  twoHeaded (L.lift false) = 0#
  fair (L.lift true) = 0#
  fair (L.lift false) = 1#

  -- the evidence of one head: ½·1 + ½·½
  evidence-heads : evidence N flip (test heads) ≈ half * 1# + half * half
  evidence-heads = ∫-flip heads

  -- the unnormalised posterior mass of "two-headed" is ½ and that of "fair" is ¼
  mass-twoHeaded : ∫ (posteriorU N flip (test heads)) (test twoHeaded) ≈ half
  mass-twoHeaded = trans (bayes-numerator N flip (test heads) (test twoHeaded))
    (trans (∫-flip (λ b → heads b * twoHeaded b))
      (trans (+-cong (trans (*-cong refl (*-identityˡ 1#)) (*-identityʳ half))
                     (trans (*-cong refl (zeroʳ half)) (zeroʳ half)))
        (+-identityʳ half)))

  mass-fair : ∫ (posteriorU N flip (test heads)) (test fair) ≈ half * half
  mass-fair = trans (bayes-numerator N flip (test heads) (test fair))
    (trans (∫-flip (λ b → heads b * fair b))
      (trans (+-cong (trans (*-cong refl (zeroʳ 1#)) (zeroʳ half)) (*-cong refl (*-identityʳ half)))
        (+-identityˡ (half * half))))

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
  open CoinBias (additiveNormalizable lem₁) half hh public
