{-# OPTIONS --safe --without-K #-}

-- The s-finite measure monad `TM` over the continuous model is a model of
-- `StatisticalInterface` (soft conditioning).  Each field points at the lemma that will discharge it:
--   weights            Continuous/Weights (semiring laws of [0,∞])
--   commutativeMonad   SFiniteMonad (TM), SFiniteStrong (strength), SFiniteCommute (Fubini)
--   inclusion          SFiniteIncl (ιH, ι-nat, ι-unit, ι-mult, ι-strong)
--   zero, score        SFiniteIncl (zeroH, scoreH, ∫ᴹ-score)
--   sumK               SFiniteSum (sumPre/sumK and their pre-measure laws)
--   scaled-laws        SFiniteDecomp (level-set decomposition, normalised pieces)
--   normalize          SFiniteNorm (classical decision on the inverse of the mass)
-- Scaling is derived from `score`; the pre-measure bridge lemmas for each field live in `SFiniteStatBridge`.
-- The file uses `--lossy-unification`: without it checking the fields against the interface takes minutes.


-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteStat where

import Level as L
open import Function.Base using (_∘_)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (1Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.SFiniteDecomp using (module SFiniteDecomp)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteStatBridge using (module SFiniteStatBridge)
open import QBS.Continuous.ProbInstance using (module ContinuousProb)
open import QBS.Statistical using (StatisticalInterface; SubMonad; Score; CountableSums; Normalization)
open import QBS.Exponential using (cartesianClosed)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.JSum using (module JSum)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Monad using (Monad)
open import Categories.Monad.Commutative using (CommutativeMonad)
import Categories.Category.Core as Cat
open import QBS.Classical using (LEM₀)

module SFiniteStat (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; constW; continuousWeights)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open SFinite lem
  open WitM
  open SFiniteMonad lem
  open SFiniteStrong lem
  open SFiniteSum lem
  open SFiniteIncl lem
  open SFiniteCommute lem using (commutative)
  open JSum lem using (J-∑; Meas-∑)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open SFiniteDecomp lem
  open SFiniteNorm lem
  module CP = ContinuousProb A lem
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  open SFiniteStatBridge lem

  ----------------------------------------------------------------------------
  -- the parts of the interface

  continuousMeasures : SubMonad CP.continuousProb
  continuousMeasures = record
    { commutativeMonad = record { strongMonad = strongMonad ; commutative = commutative }
    ; inclusion = inclusion
    ; inclusion-strong = λ A B {p} h → ι-strong (proj₁ p) (proj₂ p) h
    }

  continuousScore : Score continuousWeights continuousMeasures
  continuousScore = record
    { zero = zeroH
    ; zero-bind = λ k {pt} h → zero-bind k pt h
    ; score = scoreH
    ; score-zero = λ {pt} h → refl
    ; score-one = λ {pt} f → scoreOneG pt f
    ; score-mul = λ a b {pt} h → scoreMulPre (map a ⟨$⟩ pt) b h
    }

  module ScI = Score continuousScore

  private
    module MI = Monad (CommutativeMonad.M (SubMonad.commutativeMonad continuousMeasures))
    open Cat.Category (QBSCat S) using () renaming (_∘_ to _∘ᵏ_; _≈_ to _≈ᵏ_)

  -- the kernels `n ↦ join ∘ map (kₙ) ∘ t`, in the notation of the interface
  bindKI : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S (1Q S) (TQ X) → ℕ → Hom S (1Q S) (TQ Y)
  bindKI {X} {Y} ks t n = MI.μ.η Y ∘ᵏ MI.F.F₁ (ks n) ∘ᵏ t

  bindSumKI : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (t : Hom S (1Q S) (TQ X)) →
    MI.μ.η Y ∘ᵏ MI.F.F₁ (sumK ks) ∘ᵏ t ≈ᵏ sumK {1Q S} {Y} (λ n → MI.μ.η Y ∘ᵏ MI.F.F₁ (ks n) ∘ᵏ t)
  bindSumKI ks t {pt} f = bindSumKG ks t pt f


  continuousSums : CountableSums continuousMeasures
  continuousSums = record
    { sumK = sumK
    ; sumK-point = λ {X} {Y} ks x {pt} f → sumKPointG {X} {Y} ks x pt f
    ; bind-sumK = bindSumKI
    ; sum-nat = λ {X} {Y} f ts {pt} g → sumNatG {X} {Y} f ts pt g
    ; sum-join = λ {X} ts {pt} h → sumJoinG {X} ts pt h
    }

  module SumI = CountableSums continuousSums

  continuousNormalization : Normalization (Cocartesian.Cocartesian.coproducts (cocartesian S)) continuousScore
  continuousNormalization = record
    { normalize = normH
    ; normalize-prob = λ X {p} → normProb {X} p (invDec (massP {X} (ιPre {X} p)))
    ; normalize-zero = λ x {pt} → normZeroGlobal x
    ; normalize-scale = λ {X} a b hab t {pt} → normScaleD {X} a b (hab {pt}) t
    }

  continuousStat : StatisticalInterface (L.suc L.zero) (QBSCat S) (Probes.ℛQ S) (cartesianClosed S)
    CP.continuousProb (Cocartesian.Cocartesian.coproducts (cocartesian S))
  continuousStat = record
    { weights = continuousWeights
    ; measures = continuousMeasures
    ; scoring = continuousScore
    ; sums = continuousSums
    ; scaled-laws = λ t → let r = scaledLaws-derived t in
        proj₁ r , proj₁ (proj₂ r) , proj₁ (proj₂ (proj₂ r)) , λ {pt} f → proj₂ (proj₂ (proj₂ r)) pt f
    ; normalization = continuousNormalization
    }
