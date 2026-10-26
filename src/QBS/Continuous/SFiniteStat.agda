{-# OPTIONS --safe --without-K #-}

-- SKELETON (holes).  The s-finite measure monad `TM` over the continuous model is a model of
-- `StatisticalInterface` (soft conditioning).  Each field points at the lemma that will discharge it:
--   weights            Continuous/Weights (semiring laws of [0,∞])
--   commutativeMonad   SFiniteMonad (TM), SFiniteStrong (strength), SFiniteCommute (Fubini)
--   inclusion          SFiniteIncl (ιH, ι-nat, ι-unit, ι-mult, ι-strong)
--   zero, score        SFiniteIncl (zeroH, scoreH, ∫ᴹ-score)
--   scaleM, sumM, sumK SFiniteSum (scalePre/sumPre/sumK and their pre-measure laws)
--   scaled-laws        SFiniteDecomp (level-set decomposition, normalised pieces)
--   normalize          SFiniteNorm (classical decision on the inverse of the mass)


-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteStat where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ; !Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.SFiniteDecomp using (module SFiniteDecomp)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.ProbInstance using (module ContinuousProb)
open import QBS.Statistical using (StatisticalInterface)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probability using (ProbabilityInterface)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_)
open import QBS.Analysis.Series using (module Series)
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

module SFiniteStat (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroW)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open Split funext
  open SFinite lem funext
  open WitM
  open SFiniteMonad lem funext
  open SFiniteStrong lem funext
  open SFiniteSum lem funext
  open SFiniteIncl lem funext
  open SFiniteCommute lem funext using (commutative)
  open SFiniteDecomp lem funext
  open SFiniteNorm lem funext
  module CP = ContinuousProb A lem funext
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  continuousStat : StatisticalInterface (L.suc L.zero) (QBSCat S) (Probes.ℛQ S) (cartesianClosed S)
    CP.continuousProb (Cocartesian.Cocartesian.coproducts (cocartesian S))
  continuousStat = record
    { W = WQ
    ; mulW = mulW
    ; oneW = oneW
    ; zeroW = zeroW
    ; mul-assoc = λ a b c z → *-assoc _ _ _
    ; mul-comm = λ a b z → *-comm _ _
    ; mul-one = λ a z → *-identityʳ _
    ; mul-zero = λ a z → zeroʳ _
    ; commutativeMonad = record { strongMonad = strongMonad ; commutative = commutative }
    ; inclusion = inclusion
    ; inclusion-strong = λ A B p h → ?          -- ι-strong
    ; zero = zeroH
    ; zero-bind = λ k pt h → ?                  -- zero-bind
    ; score = scoreH
    ; score-zero = λ pt h → ?                   -- ∫ᴹ-score 0#, zeroˡ
    ; score-mul = λ a b pt h → ?                -- ∫ᴹ-score, ∫ᴹ-join, J-scale: score (a·b) = join (map (score b) (score a))
    ; sumM = sumM
    ; scaleM = scaleM
    ; scale-one = λ t pt f → ?                  -- scale-one-lem
    ; scale-mul = λ a b t pt f → ?              -- scale-mul-lem
    ; scale-return = λ a x pt f → ?             -- ∫ᴹ-scale, ∫ᴹ-map, ∫ᴹ-η, ∫ᴹ-score
    ; scale-sum = λ a ts pt f → ?               -- scale-sum-lem
    ; sum-nat = λ f ts pt g → ?                 -- sum-nat-lem
    ; sum-join = λ ts pt f → ?                  -- sum-join-lem
    ; scale-nat = λ f a t pt g → ?              -- scale-nat-lem
    ; scale-join = λ a t pt f → ?               -- scale-join-lem
    ; sumK = sumK
    ; sumK-point = λ ks x pt f → ?              -- ∫ᴹ-sumK
    ; bind-sumK = λ ks t pt f → ?               -- ∫ᴹ-join, ∫ᴹ-sumK, ∑ᶠ-swap (Tonelli for series), ∫ᴹ-sum
    ; scaled-laws = λ t → ?                     -- scaledLawsPre (Decomp), lifted to global elements
    ; normalize = normH
    ; normalize-prob = λ X p → ?                -- normProb
    ; normalize-zero = λ x pt → ?               -- normZero
    ; normalize-scale = λ a b hab t pt → ?      -- normScale
    }
