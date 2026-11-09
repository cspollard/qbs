{-# OPTIONS --safe --without-K #-}

-- The sub-probability monad of the continuous model: the generic construction of `Continuous/Monad`
-- instantiated with the class of all (mass ≤ 1) measures, with its strength and commutativity
-- (Fubini), the failure measure, and soft conditioning by a likelihood in [0,1].
module QBS.Continuous.SubProb where

import Level as L
open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (1Q; !Q)
open import QBS.Borel.Source
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Cone using (module Cone)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong
open import QBS.Continuous.Commutative using (module Commutativity)
open import QBS.Classical using (LEM₀)

module ContinuousSub (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ; rand-Fun)
  open Continuous A lem subClass public
  open Strength A lem subClass public using (strongMonad)
  open Commutativity A lem subClass public using (commutative)
  open Hom

  -- the sub-probability monad `TM` of `Continuous/Monad` is commutative and strong (inherited).

  open Cone A using (zeroM; scaleM)

  -- failure: the zero measure (a run that is discarded)
  failPre : Pre (1Q S)
  failPre = mk (constₛ tt) (QBS.const-random (1Q S) tt) zeroM tt

  -- soft conditioning: weight the run by a likelihood w ∈ [0,1]
  scorePre : ∀ w → w ≤ 1# → Pre (1Q S)
  scorePre w w≤1 = mk (constₛ tt) (QBS.const-random (1Q S) tt) (scaleM w w≤1 (dirac r₀)) tt

  ∫-score : ∀ w (w≤1 : w ≤ 1#) (f : Hom S (1Q S) AQ) → ∫ (scorePre w w≤1) f ≈ w * proj₁ (map f ⟨$⟩ tt)
  ∫-score w w≤1 f = trans (∫-unfold {1Q S} (scorePre w w≤1) f) refl

  -- `score` is a morphism from the unit interval: a measurable likelihood gives a random measure
  scoreH : Hom S AQ (TQ (1Q S))
  scoreH = record
    { map = record
        { to = λ w → scorePre (proj₁ w) (proj₂ w)
        ; cong = λ {w} {w′} e f →
            trans (∫-score (proj₁ w) (proj₂ w) f)
              (trans (*-cong e refl) (sym (∫-score (proj₁ w′) (proj₂ w′) f))) }
    ; map-random = λ {β} fβ → rwit record
        { a = !Q S
        ; g = λ r → scaleM (proj₁ (β ⟨$⟩ r)) (proj₂ (β ⟨$⟩ r)) (dirac r₀)
        ; g-ok = λ {h} fh → Fun-ext (λ r → *-comm (h r₀) (proj₁ (β ⟨$⟩ r)))
                              (Fun-scale (h r₀) (Fun-≤1 fh r₀) (rand-Fun fβ))
        ; g-pr = λ _ → tt
        ; w-eq = λ r f → via {1Q S} {1Q S} refl }
    }
