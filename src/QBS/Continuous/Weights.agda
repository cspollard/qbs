{-# OPTIONS --safe --without-K #-}

-- The object of weights of the s-finite monad: `[0,∞]` (lower cuts) as a quasi-Borel space whose
-- random elements are the threshold-measurable functions (`Analysis/Meas`), with the monoid
-- structure of multiplication (`continuousWeights`: a commutative monoid with absorbing zero).
module QBS.Continuous.Weights where

import Level as L
import Relation.Binary.PropositionalEquality.Core as ≡
open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Limits using (_×Q_)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Classical using (LEM₀)
open import QBS.Exponential using (cartesianClosed)
open import QBS.CartesianAlgebra using (fromPointwise)
open import QBS.Statistical using () renaming (Weights to WeightsOf)

module Weights (lem : LEM₀) where
  A = LowerRealsOmega lem
  open OmegaSemiring A using (_*_; 0#; 1#; setoid; *-assoc; *-comm; *-identityʳ; zeroʳ)
  open Meas lem
  open QBS
  open Hom

  WQ : QBS S
  WQ = record
    { Carrier = setoid
    ; probes = record
        { Random = λ α → Meas (α ⟨$⟩_)
        ; random-resp = λ {α} {β} e m → Meas-ext {α ⟨$⟩_} {β ⟨$⟩_} e m
        ; const-random = Meas-const
        ; pre-random = λ {α} {f} m mf → Meas-pre {α ⟨$⟩_} {f ⟨$⟩_} m mf
        }
    ; glue-random = λ {j} pj α ms → Meas-glue {j ⟨$⟩_} {λ k → α k ⟨$⟩_} pj ms
    }

  mulW : Hom S (_×Q_ S WQ WQ) WQ
  mulW = record
    { map = record
        { to = λ p → proj₁ p * proj₂ p
        ; cong = λ { (e₁ , e₂) → OmegaSemiring.*-cong A e₁ e₂ }
        }
    ; map-random = λ {γ} (m₁ , m₂) → Meas-⊗ {λ r → proj₁ (γ ⟨$⟩ r)} {λ r → proj₂ (γ ⟨$⟩ r)} m₁ m₂
    }

  constW : ∀ {X : QBS S} → Cut → Hom S X WQ
  constW c = record
    { map = record { to = λ _ → c ; cong = λ _ → OmegaSemiring.refl A }
    ; map-random = λ _ → Meas-const c
    }

  -- the weights as a commutative monoid with absorbing zero for the products of the cartesian closed `QBSCat S`
  continuousWeights : WeightsOf (cartesianClosed S)
  continuousWeights = fromPointwise (cartesianClosed S) WQ mulW (constW 1#) (constW 0#)
    (λ a b c {z} → *-assoc _ _ _)
    (λ a b {z} → *-comm _ _)
    (λ a {z} → *-identityʳ _)
    (λ a {z} → zeroʳ _)
