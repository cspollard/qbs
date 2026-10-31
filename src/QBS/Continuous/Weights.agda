{-# OPTIONS --safe --without-K #-}

-- The object of weights of the s-finite monad: `[0,∞]` (lower cuts) as a quasi-Borel space whose
-- random elements are the threshold-measurable functions (`Analysis/Meas`), with the monoid
-- structure of multiplication.
module QBS.Continuous.Weights where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (const)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)

open import QBS.Core
open import QBS.Limits using (_×Q_; 1Q)
open import QBS.Borel.Source using (cantorSource)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)

module Weights (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  A = LowerRealsOmega lem
  open OmegaSemiring A using (_*_; 0#; 1#; setoid)
  open Meas lem
  open QBS
  open Hom

  WQ : QBS S
  WQ = record
    { Carrier = setoid
    ; Random = Meas
    ; random-resp = λ {α} {β} e m → Meas-ext {α} {β} e m
    ; random-cong = λ m e → Meas-resp m (lower e)
    ; const-random = Meas-const
    ; pre-random = λ {α} {f} m mf → Meas-pre {α} {f} m mf
    ; glue-random = λ {j} pj α ms → Meas-glue {j} {α} pj ms
    }

  mulW : Hom S (_×Q_ S WQ WQ) WQ
  mulW = record
    { map = record { to = λ p → proj₁ p * proj₂ p ; cong = λ { (e₁ , e₂) → OmegaSemiring.*-cong A e₁ e₂ } }
    ; map-random = λ {γ} (m₁ , m₂) → Meas-⊗ {λ r → proj₁ (γ r)} {λ r → proj₂ (γ r)} m₁ m₂
    }

  constW : ∀ {X : QBS S} → Cut → Hom S X WQ
  constW c = record
    { map = record { to = λ _ → c ; cong = λ _ → OmegaSemiring.refl A }
    ; map-random = λ _ → Meas-const c
    }

  oneW zero⇒ : Hom S (1Q S) WQ
  oneW = constW 1#
  zero⇒ = constW 0#
