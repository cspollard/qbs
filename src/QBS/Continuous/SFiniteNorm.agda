{-# OPTIONS --safe --without-K #-}

-- SKELETON (holes).  Normalisation `M X ⇒ Prob X + 1` of s-finite measures, with its three laws.
--
-- The mass `∫ᴹ p 1` of `[α, m, w]` is a lower real in `[0, ∞]`; classically it is either invertible
-- (finite and positive, `Analysis/LowerInverse`) or not (zero or infinite).  Invertible: normalise by
-- the inverse, which is again a pre-measure `[α, m, w/mass]`, here with `w` rebuilt to a probability
-- by pushing the weight into the measure (`Continuous/SFiniteDecomp.normM` on the level pieces).  Not
-- invertible: fail (`inj₂ tt`); the degenerate infinite-mass case is left unspecified by the interface.

-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteNorm where

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
open import QBS.Continuous.ProbInstance using (module ContinuousProb)
open import QBS.Statistical using (StatisticalInterface)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_; Piece; ev)
open import QBS.Analysis.Series using (module Series)
import Data.Nat.Base as ℕ
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

module SFiniteNorm (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroW)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open Split funext
  open UnitInterval A using (AQ)
  open RandomSource S using () renaming (meas-id to measId)
  open SFinite lem funext
  open WitM
  open SFiniteMonad lem funext
  open SFiniteStrong lem funext
  open SFiniteSum lem funext
  open SFiniteIncl lem funext
  open Series A
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  open import Data.Sum.Base using (inj₁; inj₂)

  private
    oneF : ∀ (X : QBS S) → Hom S X WQ
    oneF X = constW 1#

  -- total massP of a pre-measure
  massP : ∀ {X : QBS S} → Pre (XW X) → Cut
  massP {X} p = ∫ᴹ {X} p (oneF X)

  massP-cong : ∀ {X : QBS S} {p q : Pre (XW X)} → _≈ᴹ_ {X} p q → massP p ≈ massP q
  massP-cong {X} {p} {q} e = e (oneF X)

  massP-scale : ∀ {X : QBS S} c (p : Pre (XW X)) → massP (scalePre {X} c p) ≈ c * massP p
  massP-scale {X} c p = ∫ᴹ-scale {X} c p (oneF X)

  -- the decision "is the massP invertible?", classical (`lem`)
  InvDec : Cut → Set₁
  InvDec m = Σ Cut (λ n → m * n ≈ 1#) ⊎ (∀ n → m * n ≈ 1# → ⊥)

  invDec : ∀ m → InvDec m
  invDec m = ?

  -- normalisation of a measure of invertible massP: a probability pre-measure on X
  normPre : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) → massP p * n ≈ 1# → C.Pre X
  normPre p n h = ?

  ∫-normPre : ∀ {X : QBS S} (p : Pre (XW X)) (n : Cut) (h : massP p * n ≈ 1#) (f : Hom S X WQ) →
    ∫ᴹ {X} (ιPre {X} (normPre p n h)) f ≈ n * ∫ᴹ {X} p f
  ∫-normPre p n h f = ?

  normC′ : ∀ {X : QBS S} (p : Pre (XW X)) → InvDec (massP p) → ∣ C.TQ X ∣ ⊎ ∣ 1Q S ∣
  normC′ p (inj₁ (n , h)) = inj₁ (normPre p n h)
  normC′ p (inj₂ _) = inj₂ tt

  normC : ∀ {X : QBS S} → Pre (XW X) → ∣ C.TQ X ∣ ⊎ ∣ 1Q S ∣
  normC p = normC′ p (invDec (massP p))

  normC-cong : ∀ {X : QBS S} {p q : Pre (XW X)} → _≈ᴹ_ {X} p q →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC p) (normC q)
  normC-cong e = ?

  -- the case index of a measure: 0 = invertible massP (normalise), 1 = not (fail)
  caseIdx : ∀ {X : QBS S} → Pre (XW X) → ℕ
  caseIdx p with invDec (massP p)
  ... | inj₁ _ = 0
  ... | inj₂ _ = 1

  -- measurability: {r | massP (β r) invertible} is Borel, since r ↦ massP (β r) is `Meas`
  -- (`Tonelli.Meas-J`) and 0 < m < ∞ is a countable union of intersections of threshold sets
  caseIdx-Idx : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β → RandomSource.Idx S (λ r → caseIdx (β r))
  caseIdx-Idx w = ?

  -- r ↦ massP (β r) is `Meas` (Tonelli.Meas-J)
  massP-Meas : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β → Meas (λ r → massP (β r))
  massP-Meas w = ?

  -- the classical inverse as a function (0 where there is none); a Borel function of the mass
  invOf : Cut → Cut
  invOf m = ?

  invOf-Meas : ∀ {f : R₁ → Cut} → Meas f → Meas (λ r → invOf (f r))
  invOf-Meas mf = ?

  -- on the invertible case, the normalised family is a random element of C.TQ X
  normPre-random : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β →
    (inv : ∀ r → massP (β r) * invOf (massP (β r)) ≈ 1#) →
    QBS.Random (C.TQ X) (λ r → normPre (β r) (invOf (massP (β r))) (inv r))
  normPre-random w inv = ?

  normRandom : ∀ {X : QBS S} {β : R₁ → Pre (XW X)} → WitM {X} β →
    QBS.Random (_+Q_ S (C.TQ X) (1Q S)) (λ r → normC (β r))
  normRandom w = ?

  normH : ∀ X → Hom S (TQ X) (_+Q_ S (C.TQ X) (1Q S))
  normH X = record { map = record { to = normC ; cong = normC-cong } ; map-random = normRandom }

  -- the three laws
  normProb : ∀ {X : QBS S} (p : C.Pre X) (e : InvDec (massP (ιPre {X} p))) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ (ιPre {X} p) e) (inj₁ p)
  normProb p e = ?

  normZero : ∀ {X : QBS S} (p : Pre (XW X)) → massP p ≈ 0# → (e : InvDec (massP p)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ p e) (inj₂ tt)
  normZero p z e = ?

  normScale : ∀ {X : QBS S} (c d : Cut) → c * d ≈ 1# → (p : Pre (XW X))
    (e′ : InvDec (massP (scalePre {X} c p))) (e : InvDec (massP p)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S))) (normC′ (scalePre {X} c p) e′) (normC′ p e)
  normScale c d cd p e′ e = ?
