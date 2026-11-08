{-# OPTIONS --safe --without-K #-}

-- The object of weights of the s-finite monad: `[0,∞]` (lower cuts) as a quasi-Borel space whose
-- random elements are the threshold-measurable functions (`Analysis/Meas`), with the monoid
-- structure of multiplication (`continuousWeights`: a commutative monoid with absorbing zero).
module QBS.Continuous.Weights where

import Level as L
import Relation.Binary.PropositionalEquality.Core as ≡
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Limits using (_×Q_; rand-fst; rand-snd)
open import QBS.Pieces
import Categories.Category.SubCategory.SubHom as SH
open import Categories.Category.Instance.Setoids using (Setoids)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S; idxPart)
open import QBS.Classical using (LEM₀)
open import QBS.Exponential using (cartesianClosed)
open import QBS.CartesianAlgebra using (fromPointwise)
open import QBS.Statistical using () renaming (Weights to WeightsOf)

module Weights (lem : LEM₀) where
  A = LowerRealsOmega lem
  open OmegaSemiring A using (_*_; 0#; 1#; setoid; *-assoc; *-comm; *-identityʳ; zeroʳ)
  open Meas lem
  open RandomSource S using (measurable; Rˢ)
  open SH (Setoids (L.suc L.zero) (L.suc L.zero)) using (mem; probe; reads)
  open QBS
  open Hom

  WQ : QBS S
  WQ = record
    { Carrier = setoid
    ; probes = fromPred measurable setoid (λ α → Meas (α ⟨$⟩_)) Meas-const
        (λ {α} {f} m mf → Meas-pre {α ⟨$⟩_} {f ⟨$⟩_} m mf)
    ; glue-random = λ {j} pj α ms →
        let q = λ n → probe (ms n)
            β = λ n → proj₁ (q n) in
        mem (glueₛ j β
            , Meas-glue {λ r → L.lower (j ⟨$⟩ r)} {λ k → β k ⟨$⟩_} (idxPart pj) (λ n → proj₂ (q n)))
          (λ {r} → reads (ms (L.lower (j ⟨$⟩ r))) {r})
    }

  -- random elements of WQ are the measurable functions (up to the pointwise equality in the reading)
  rand-Meas : ∀ {h : Func Rˢ setoid} → Random WQ h → Meas (h ⟨$⟩_)
  rand-Meas {h} m = Meas-ext {proj₁ (probe m) ⟨$⟩_} {h ⟨$⟩_} (λ r → reads m {r}) (proj₂ (probe m))

  Meas-rand : ∀ {h : Func Rˢ setoid} → Meas (h ⟨$⟩_) → Random WQ h
  Meas-rand {h} m = mem (h , m) (OmegaSemiring.refl A)

  mulW : Hom S (_×Q_ S WQ WQ) WQ
  mulW = record
    { map = record
        { to = λ p → proj₁ p * proj₂ p
        ; cong = λ { (e₁ , e₂) → OmegaSemiring.*-cong A e₁ e₂ }
        }
    ; map-random = λ {γ} m →
        Meas-rand (Meas-⊗ {λ r → proj₁ (γ ⟨$⟩ r)} {λ r → proj₂ (γ ⟨$⟩ r)}
          (rand-Meas (rand-fst S {WQ} {WQ} {γ} m)) (rand-Meas (rand-snd S {WQ} {WQ} {γ} m)))
    }

  constW : ∀ {X : QBS S} → Cut → Hom S X WQ
  constW c = record
    { map = record { to = λ _ → c ; cong = λ _ → OmegaSemiring.refl A }
    ; map-random = λ _ → const-random WQ c
    }

  -- the weights as a commutative monoid with absorbing zero for the products of the cartesian closed `QBSCat S`
  continuousWeights : WeightsOf (cartesianClosed S)
  continuousWeights = fromPointwise (cartesianClosed S) WQ mulW (constW 1#) (constW 0#)
    (λ a b c {z} → *-assoc _ _ _)
    (λ a b {z} → *-comm _ _)
    (λ a {z} → *-identityʳ _)
    (λ a {z} → zeroʳ _)
