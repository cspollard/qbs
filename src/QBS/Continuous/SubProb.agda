{-# OPTIONS --safe --without-K #-}

-- The sub-probability monad of the continuous model: the generic construction of `Continuous/Monad`
-- instantiated with the class of all (mass ≤ 1) measures, with its strength and commutativity
-- (Fubini), the failure measure, and soft conditioning by a likelihood in [0,1].
module QBS.Continuous.SubProb where

import Level as L
open import Function.Base using (const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; !Q)
open import QBS.Borel.Source
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong

module ContinuousSub (A : OmegaSemiring (L.suc L.zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥))
                     (funext : Extensionality L.zero L.zero) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ)
  open Continuous A lem funext subClass public
  open Strength A lem funext subClass public using (strongMonad; commutative)
  open Hom

  -- the sub-probability monad `TM` of `Continuous/Monad` is commutative and strong (inherited).

  -- the zero measure
  zeroM : Measure
  zeroM = record
    { I = λ _ _ → 0#
    ; I-cong = λ _ _ _ → refl
    ; I-mono = λ _ _ _ → ≤-refl
    ; I-add = λ _ _ _ _ → sym (+-identityˡ 0#)
    ; I-scale = λ c _ _ _ → sym (zeroʳ c)
    ; I-sup = λ hs fs inc f e → sym (⨆-const 0# _)
    ; I-sub = λ _ → 0-least
    }

  -- scaling a measure by a weight ≤ 1
  scaleM : ∀ c → c ≤ 1# → Measure → Measure
  scaleM c c≤1 μ = record
    { I = λ h f → c * I μ h f
    ; I-cong = λ e f f′ → *-cong refl (I-cong μ e f f′)
    ; I-mono = λ f f′ le → *-mono c (I-mono μ f f′ le)
    ; I-add = λ f f₁ f₂ e → trans (*-cong refl (I-add μ f f₁ f₂ e)) (distribˡ c _ _)
    ; I-scale = λ d f f′ e → trans (*-cong refl (I-scale μ d f f′ e))
        (trans (sym (*-assoc c d _)) (trans (*-cong (*-comm c d) refl) (*-assoc d c _)))
    ; I-sup = λ hs fs inc f e →
        let incI = λ n → I-mono μ (fs n) (fs (suc n)) (λ x → inc x n)
        in trans (*-cong refl (I-sup μ hs fs inc f e))
             (*-⨆ c (λ n → I μ (hs n) (fs n)) incI (λ n → *-mono c (incI n)))
    ; I-sub = λ f → ≤-trans (≤-trans (*-mono c (I-sub μ f)) (≤-reflexive (*-identityʳ c))) c≤1
    }

  -- failure: the zero measure (a run that is discarded)
  failPre : Pre (1Q S)
  failPre = mk (λ _ → tt) tt zeroM tt

  -- soft conditioning: weight the run by a likelihood w ∈ [0,1]
  scorePre : ∀ w → w ≤ 1# → Pre (1Q S)
  scorePre w w≤1 = mk (λ _ → tt) tt (scaleM w w≤1 (dirac r₀)) tt

  ∫-score : ∀ w (w≤1 : w ≤ 1#) (f : Hom S (1Q S) AQ) → ∫ (scorePre w w≤1) f ≈ w * proj₁ (map f ⟨$⟩ tt)
  ∫-score w w≤1 f = refl

  -- `score` is a morphism from the unit interval: a measurable likelihood gives a random measure
  scoreH : Hom S AQ (TQ (1Q S))
  scoreH = record
    { map = record
        { to = λ w → scorePre (proj₁ w) (proj₂ w)
        ; cong = λ {w} {w′} e f → *-cong e refl }
    ; map-random = λ {β} fβ → record
        { a = !Q S
        ; g = λ r → scaleM (proj₁ (β r)) (proj₂ (β r)) (dirac r₀)
        ; g-ok = λ {h} fh → Fun-ext (λ r → *-comm (h r₀) (proj₁ (β r)))
                              (Fun-scale (h r₀) (Fun-≤1 fh r₀) fβ)
        ; g-pr = λ _ → tt
        ; w-eq = λ r f → refl }
    }
