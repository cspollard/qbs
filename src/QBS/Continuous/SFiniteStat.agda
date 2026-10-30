{-# OPTIONS --safe --without-K #-}

-- The s-finite measure monad `TM` over the continuous model is a model of
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
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
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
open import QBS.Analysis.JSum using (module JSum)
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
  open JSum lem using (J-∑; Meas-∑)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open SFiniteDecomp lem funext
  open SFiniteNorm lem funext
  module CP = ContinuousProb A lem funext
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- bridge lemmas for the weight and series fields, at the pre-measure level

  -- score (u·v) = join (map (score v) (score u))
  kScore : Hom S (1Q S) WQ → Hom S (1Q S) (TQ (1Q S))
  kScore b = _∘H_ S {1Q S} {WQ} {TQ (1Q S)} scoreH (_∘H_ S {1Q S} {1Q S} {WQ} b (!Q S))

  kScore-int : ∀ (b : Hom S (1Q S) WQ) (h : Hom S (1Q S) WQ) →
    map (_∘H_ S {1Q S} {TQ (1Q S)} {WQ} (∫ᶠ {1Q S} h) (kScore b)) ⟨$⟩ tt ≈ (map b ⟨$⟩ tt) * (map h ⟨$⟩ tt)
  kScore-int b h = ∫ᴹ-score (map b ⟨$⟩ tt) h

  scoreMulPre : ∀ (u : ∣ WQ ∣) (b : Hom S (1Q S) WQ) (h : Hom S (1Q S) WQ) →
    ∫ᴹ {1Q S} (scorePre (u * (map b ⟨$⟩ tt))) h
      ≈ ∫ᴹ {1Q S} (joinPre {1Q S} (mapM {1Q S} {TQ (1Q S)} (kScore b) (scorePre u))) h
  scoreMulPre u b h = trans (∫ᴹ-score (u * (map b ⟨$⟩ tt)) h)
    (trans (*-assoc u (map b ⟨$⟩ tt) (map h ⟨$⟩ tt))
      (sym (trans (∫ᴹ-join {1Q S} (mapM {1Q S} {TQ (1Q S)} (kScore b) (scorePre u)) h)
        (trans (∫ᴹ-map {1Q S} {TQ (1Q S)} (kScore b) (scorePre u) (∫ᶠ {1Q S} h))
          (trans (∫ᴹ-score u (_∘H_ S {1Q S} {TQ (1Q S)} {WQ} (∫ᶠ {1Q S} h) (kScore b)))
            (*-cong refl (kScore-int b h)))))))

  -- scale a (return x) = map x (score a)
  kPoint : ∀ {X : QBS S} → Hom S (1Q S) X → Hom S (1Q S) X
  kPoint {X} x = _∘H_ S {1Q S} {1Q S} {X} x (!Q S)

  scaleReturnPre : ∀ {X : QBS S} (a : ∣ WQ ∣) (xh : Hom S (1Q S) X) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} a (C.ηPre {XW X} (1# , map xh ⟨$⟩ tt))) f
      ≈ ∫ᴹ {X} (mapM {1Q S} {X} (kPoint {X} xh) (scorePre a)) f
  scaleReturnPre {X} a xh f = trans (∫ᴹ-scale {X} a (C.ηPre {XW X} (1# , map xh ⟨$⟩ tt)) f)
    (trans (*-cong refl (∫ᴹ-η (map xh ⟨$⟩ tt) f))
      (trans (sym (∫ᴹ-score a (_∘H_ S f (kPoint {X} xh))))
        (sym (∫ᴹ-map {1Q S} {X} (kPoint {X} xh) (scorePre a) f))))

  -- sumK at a point
  sumK-pointPre : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (x : ∣ X ∣) (f : Hom S Y WQ) →
    ∫ᴹ {Y} (map (sumK ks) ⟨$⟩ x) f ≈ ∫ᴹ {Y} (sumPre {Y} (λ n → map (ks n) ⟨$⟩ x)) f
  sumK-pointPre {X} {Y} ks x f = trans (∫ᴹ-sumK ks x f) (sym (∫ᴹ-sum {Y} (λ n → map (ks n) ⟨$⟩ x) f))

  -- the integral of a pre-measure against a pointwise series of test functions
  ∫ᴹ-series : ∀ {X : QBS S} (p : Pre (XW X)) (g : Hom S X WQ) (hs : ℕ → Hom S X WQ) →
    (∀ x → map g ⟨$⟩ x ≈ ∑ᶠ (λ n → map (hs n) ⟨$⟩ x)) →
    ∫ᴹ {X} p g ≈ ∑ᶠ (λ n → ∫ᴹ {X} p (hs n))
  ∫ᴹ-series {X} p g hs e = trans
    (J-cong (m p) {ψ {X} p g} {λ r → ∑ᶠ (λ n → ψ {X} p (hs n) r)} (mψ {X} p g)
       (Meas-∑ (λ n → ψ {X} p (hs n)) (λ n → mψ {X} p (hs n)))
       (λ r → trans (*-cong refl (e (proj₂ (α p r)))) (∑ᶠ-scale (proj₁ (α p r)) (λ n → map (hs n) ⟨$⟩ proj₂ (α p r)))))
    (J-∑ (m p) (λ n → ψ {X} p (hs n)) (λ n → mψ {X} p (hs n)))

  kSum : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → ℕ → Hom S (TQ Y) WQ → Hom S X WQ
  kSum {X} {Y} ks n f = _∘H_ S {X} {TQ Y} {WQ} f (ks n)

  bindSumKPre : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (t : Pre (XW X)) (f : Hom S Y WQ) →
    ∫ᴹ {Y} (joinPre {Y} (mapM {X} {TQ Y} (sumK ks) t)) f
      ≈ ∫ᴹ {Y} (sumPre {Y} (λ n → joinPre {Y} (mapM {X} {TQ Y} (ks n) t))) f
  bindSumKPre {X} {Y} ks t f = trans (∫ᴹ-join {Y} (mapM {X} {TQ Y} (sumK ks) t) f)
    (trans (∫ᴹ-map {X} {TQ Y} (sumK ks) t (∫ᶠ {Y} f))
      (trans (∫ᴹ-series {X} t (_∘H_ S {X} {TQ Y} {WQ} (∫ᶠ {Y} f) (sumK ks))
                (λ n → kSum {X} {Y} ks n (∫ᶠ {Y} f)) (λ x → ∫ᴹ-sumK ks x f))
        (trans (∑ᶠ-cong (λ n → sym (trans (∫ᴹ-join {Y} (mapM {X} {TQ Y} (ks n) t) f)
                                      (∫ᴹ-map {X} {TQ Y} (ks n) t (∫ᶠ {Y} f)))))
          (sym (∫ᴹ-sum {Y} (λ n → joinPre {Y} (mapM {X} {TQ Y} (ks n) t)) f)))))

  ----------------------------------------------------------------------------
  -- scaled laws, at global elements

  scaledLaws-global : ∀ {X : QBS S} (t : Hom S (1Q S) (TQ X)) →
    Σ (ℕ → Hom S (Probes.ℛQ S) X) λ a →
    Σ (ℕ → Hom S (1Q S) WQ) λ w →
    Σ (ℕ → Σ Measure IsProb) λ μ →
      ∀ (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
        ∫ᴹ {X} (map t ⟨$⟩ pt) f ≈ ∫ᴹ {X} (sumPre {X} (λ n → scalePre {X} (map (w n) ⟨$⟩ tt) (ιPre {X} (lawPre (a n) (μ n))))) f
  scaledEq : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} p f ≈ ∫ᴹ {X} (sumPre {X} (λ n → scalePre {X} (proj₁ (proj₂ (scaledLawsPre {X} p)) n)
      (ιPre {X} (lawPre (proj₁ (scaledLawsPre {X} p) n) (proj₁ (proj₂ (proj₂ (scaledLawsPre {X} p))) n))))) f
  scaledEq {X} p f = trans (proj₂ (proj₂ (proj₂ (scaledLawsPre {X} p))) f)
    (sym (∫ᴹ-sum {X} (λ n → scalePre {X} (proj₁ (proj₂ (scaledLawsPre {X} p)) n)
      (ιPre {X} (lawPre (proj₁ (scaledLawsPre {X} p) n) (proj₁ (proj₂ (proj₂ (scaledLawsPre {X} p))) n)))) f))

  scaledLaws-global {X} t = proj₁ (scaledLawsPre {X} (map t ⟨$⟩ tt)) ,
    (λ n → constW {1Q S} (proj₁ (proj₂ (scaledLawsPre {X} (map t ⟨$⟩ tt))) n)) ,
    proj₁ (proj₂ (proj₂ (scaledLawsPre {X} (map t ⟨$⟩ tt)))) ,
    (λ pt f → scaledEq {X} (map t ⟨$⟩ tt) f)

  massZero : ∀ {X : QBS S} (x : Hom S (1Q S) X) → massP {X} (mapM {1Q S} {X} x (scorePre 0#)) ≈ 0#
  massZero {X} x = trans (∫ᴹ-map {1Q S} {X} x (scorePre 0#) (constW {X} 1#))
    (trans (∫ᴹ-score 0# (_∘H_ S {1Q S} {X} {WQ} (constW {X} 1#) x)) (zeroˡ _))

  normZeroGlobal : ∀ {X : QBS S} (x : Hom S (1Q S) X) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S)))
      (normC′ {X} (mapM {1Q S} {X} x (scorePre 0#)) (invDec (massP {X} (mapM {1Q S} {X} x (scorePre 0#))))) (inj₂ tt)
  normZeroGlobal {X} x = normZero {X} (mapM {1Q S} {X} x (scorePre 0#)) (massZero {X} x)
    (invDec (massP {X} (mapM {1Q S} {X} x (scorePre 0#))))

  normScaleGlobal : ∀ {X : QBS S} (c d : Cut) → c * d ≈ 1# → (p : Pre (XW X)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S)))
      (normC′ {X} (scalePre {X} c p) (invDec (massP {X} (scalePre {X} c p)))) (normC′ {X} p (invDec (massP {X} p)))
  normScaleGlobal {X} c d cd p = normScale {X} c d cd p (invDec (massP {X} (scalePre {X} c p))) (invDec (massP {X} p))

  ----------------------------------------------------------------------------
  -- bridge lemmas for the scaling fields, stated at the category-theoretic form of each field
  -- (unifying `scale-*-lem _ f` against the field type unfolded the weights and ran out of memory)

  scaleOneG : ∀ {X : QBS S} (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
    ∫ᴹ {X} (map (scaleM {X} oneW t) ⟨$⟩ pt) f ≈ ∫ᴹ {X} (map t ⟨$⟩ pt) f
  scaleOneG {X} t pt f = scale-one-lem {X} (map t ⟨$⟩ pt) f

  scaleMulG : ∀ {X : QBS S} (a b : Hom S (1Q S) WQ) (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
    ∫ᴹ {X} (map (scaleM {X} (_∘H_ S {1Q S} {_×Q_ S WQ WQ} {WQ} mulW (pairQ S {1Q S} {WQ} {WQ} a b)) t) ⟨$⟩ pt) f
      ≈ ∫ᴹ {X} (map (scaleM {X} a (scaleM {X} b t)) ⟨$⟩ pt) f
  scaleMulG {X} a b t pt f = scale-mul-lem {X} (map a ⟨$⟩ pt) (map b ⟨$⟩ pt) (map t ⟨$⟩ pt) f

  scaleSumG : ∀ {X : QBS S} (a : Hom S (1Q S) WQ) (ts : ℕ → Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
    ∫ᴹ {X} (map (scaleM {X} a (sumM {X} ts)) ⟨$⟩ pt) f ≈ ∫ᴹ {X} (map (sumM {X} (λ n → scaleM {X} a (ts n))) ⟨$⟩ pt) f
  scaleSumG {X} a ts pt f = scale-sum-lem {X} (map a ⟨$⟩ pt) (λ n → map (ts n) ⟨$⟩ pt) f

  scaleNatG : ∀ {X Y : QBS S} (f : Hom S X Y) (a : Hom S (1Q S) WQ) (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (g : Hom S Y WQ) →
    ∫ᴹ {Y} (map (_∘H_ S {1Q S} {TQ X} {TQ Y} (Functor.F₁ TF f) (scaleM {X} a t)) ⟨$⟩ pt) g
      ≈ ∫ᴹ {Y} (map (scaleM {Y} a (_∘H_ S {1Q S} {TQ X} {TQ Y} (Functor.F₁ TF f) t)) ⟨$⟩ pt) g
  scaleNatG {X} {Y} f a t pt g = scale-nat-lem {X} {Y} f (map a ⟨$⟩ pt) (map t ⟨$⟩ pt) g

  scaleJoinG : ∀ {X : QBS S} (a : Hom S (1Q S) WQ) (t : Hom S (1Q S) (TQ (TQ X))) (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
    ∫ᴹ {X} (map (_∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X) (scaleM {TQ X} a t)) ⟨$⟩ pt) f
      ≈ ∫ᴹ {X} (map (scaleM {X} a (_∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X) t)) ⟨$⟩ pt) f
  scaleJoinG {X} a t pt f = scale-join-lem {X} (map a ⟨$⟩ pt) (map t ⟨$⟩ pt) f

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
    ; inclusion-strong = λ A B p h → ι-strong (proj₁ p) (proj₂ p) h
    ; zero = zeroH
    ; zero-bind = λ k pt h → zero-bind k pt h
    ; score = scoreH
    ; score-zero = λ pt h → refl
    ; score-mul = λ a b pt h → scoreMulPre (map a ⟨$⟩ pt) b h
    ; sumM = sumM
    ; scaleM = scaleM
    ; scale-one = λ {X} t pt f → scaleOneG {X} t pt f
    ; scale-mul = λ {X} a b t pt f → scaleMulG {X} a b t pt f
    ; scale-return = λ a x pt f → scaleReturnPre (map a ⟨$⟩ pt) x f
    ; scale-sum = λ {X} a ts pt f → scaleSumG {X} a ts pt f
    ; sum-nat = λ f ts pt g → sum-nat-lem f _ g
    ; sum-join = λ ts pt f → sum-join-lem _ f
    ; scale-nat = λ {X} {Y} f a t pt g → scaleNatG {X} {Y} f a t pt g
    ; scale-join = λ {X} a t pt f → scaleJoinG {X} a t pt f
    ; sumK = sumK
    ; sumK-point = λ ks x pt f → sumK-pointPre ks (map x ⟨$⟩ pt) f
    ; bind-sumK = λ ks t pt f → bindSumKPre ks (map t ⟨$⟩ pt) f
    ; scaled-laws = λ t → scaledLaws-global t
    ; normalize = normH
    ; normalize-prob = λ X p → normProb {X} p (invDec (massP {X} (ιPre {X} p)))
    ; normalize-zero = λ x pt → normZeroGlobal x
    ; normalize-scale = λ a b hab t pt → normScaleGlobal (map a ⟨$⟩ pt) (map b ⟨$⟩ pt) (hab pt) (map t ⟨$⟩ pt)
    }
