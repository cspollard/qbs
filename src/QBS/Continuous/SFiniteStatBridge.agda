{-# OPTIONS --safe --without-K #-}

-- Pre-measure bridge lemmas for `SFiniteStat`: each field of `StatisticalInterface` for the s-finite measure
-- monad is stated here at the category-theoretic form of the field (unifying `…-lem _ f` against the field
-- type itself unfolded the weights and ran out of memory), and proved from the integral laws of
-- SFiniteSum / SFiniteIncl / SFiniteDecomp / SFiniteNorm.
module QBS.Continuous.SFiniteStatBridge where

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

module SFiniteStatBridge (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
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
  private module CP = ContinuousProb A lem funext
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
  -- score at weight 1 is the unit, and scaling is a bind through score

  scoreOneG : ∀ (pt : ∣ 1Q S ∣) (f : Hom S (1Q S) WQ) →
    ∫ᴹ {1Q S} (scorePre 1#) f ≈ ∫ᴹ {1Q S} (C.ηPre {XW (1Q S)} (1# , pt)) f
  scoreOneG pt f = trans (∫ᴹ-score 1# f) (trans (*-identityˡ _) (sym (∫ᴹ-η pt f)))

  scaleDefPre : ∀ {X : QBS S} (c : ∣ WQ ∣) (t : Hom S (1Q S) (TQ X)) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} c (map t ⟨$⟩ tt)) f ≈ ∫ᴹ {X} (joinPre {X} (mapM {1Q S} {TQ X} t (scorePre c))) f
  scaleDefPre {X} c t f = trans (∫ᴹ-scale {X} c (map t ⟨$⟩ tt) f)
    (sym (trans (∫ᴹ-join {X} (mapM {1Q S} {TQ X} t (scorePre c)) f)
      (trans (∫ᴹ-map {1Q S} {TQ X} t (scorePre c) (∫ᶠ {X} f))
        (∫ᴹ-score c (_∘H_ S {1Q S} {TQ X} {WQ} (∫ᶠ {X} f) t)))))

  ----------------------------------------------------------------------------
  -- the sum fields, stated at the category-theoretic form of each field (see the note above)
  sumKPointG : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (x : Hom S (1Q S) X) (pt : ∣ 1Q S ∣) (f : Hom S Y WQ) →
    ∫ᴹ {Y} (map (_∘H_ S {1Q S} {X} {TQ Y} (sumK ks) x) ⟨$⟩ pt) f
      ≈ ∫ᴹ {Y} (map (sumK {1Q S} {Y} (λ n → _∘H_ S {1Q S} {X} {TQ Y} (ks n) x)) ⟨$⟩ pt) f
  sumKPointG {X} {Y} ks x pt f =
    trans (∫ᴹ-sumK ks (map x ⟨$⟩ pt) f) (sym (∫ᴹ-sumK (λ n → _∘H_ S {1Q S} {X} {TQ Y} (ks n) x) pt f))

  bindKPt : ∀ {X Y : QBS S} (k : Hom S X (TQ Y)) (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S Y WQ) →
    ∫ᴹ {Y} (map (_∘H_ S {1Q S} {TQ (TQ Y)} {TQ Y} (NaturalTransformation.η (Monad.μ TM) Y)
                  (_∘H_ S {1Q S} {TQ X} {TQ (TQ Y)} (Functor.F₁ TF k) t)) ⟨$⟩ pt) f
      ≈ ∫ᴹ {Y} (joinPre {Y} (mapM {X} {TQ Y} k (map t ⟨$⟩ pt))) f
  bindKPt k t pt f = refl

  sumNatG : ∀ {X Y : QBS S} (f : Hom S X Y) (ts : ℕ → Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (g : Hom S Y WQ) →
    ∫ᴹ {Y} (map (_∘H_ S {1Q S} {TQ X} {TQ Y} (Functor.F₁ TF f) (sumK {1Q S} {X} ts)) ⟨$⟩ pt) g
      ≈ ∫ᴹ {Y} (map (sumK {1Q S} {Y} (λ n → _∘H_ S {1Q S} {TQ X} {TQ Y} (Functor.F₁ TF f) (ts n))) ⟨$⟩ pt) g
  sumNatG {X} {Y} f ts pt g =
    trans (∫ᴹ-map {X} {Y} f (map (sumK {1Q S} {X} ts) ⟨$⟩ pt) g)
      (trans (∫ᴹ-sumK ts pt (_∘H_ S g f))
        (trans (∑ᶠ-cong (λ n → sym (∫ᴹ-map {X} {Y} f (map (ts n) ⟨$⟩ pt) g)))
          (sym (∫ᴹ-sumK (λ n → _∘H_ S {1Q S} {TQ X} {TQ Y} (Functor.F₁ TF f) (ts n)) pt g))))

  sumJoinG : ∀ {X : QBS S} (ts : ℕ → Hom S (1Q S) (TQ (TQ X))) (pt : ∣ 1Q S ∣) (h : Hom S X WQ) →
    ∫ᴹ {X} (map (_∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X) (sumK {1Q S} {TQ X} ts)) ⟨$⟩ pt) h
      ≈ ∫ᴹ {X} (map
          (sumK {1Q S} {X} (λ n → _∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X) (ts n))) ⟨$⟩ pt) h
  sumJoinG {X} ts pt h =
    trans (∫ᴹ-join {X} (map (sumK {1Q S} {TQ X} ts) ⟨$⟩ pt) h)
      (trans (∫ᴹ-sumK ts pt (∫ᶠ {X} h))
        (trans (∑ᶠ-cong (λ n → sym (∫ᴹ-join {X} (map (ts n) ⟨$⟩ pt) h)))
          (sym (∫ᴹ-sumK (λ n → _∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X) (ts n)) pt h))))

  -- the kernels `n ↦ join ∘ map (kₙ) ∘ t` of the bind of a sum
  bindK : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S (1Q S) (TQ X) → ℕ → Hom S (1Q S) (TQ Y)
  bindK {X} {Y} ks t n = _∘H_ S {1Q S} {TQ (TQ Y)} {TQ Y} (NaturalTransformation.η (Monad.μ TM) Y)
    (_∘H_ S {1Q S} {TQ X} {TQ (TQ Y)} (Functor.F₁ TF (ks n)) t)

  bindSumKG : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S Y WQ) →
    ∫ᴹ {Y} (map (_∘H_ S {1Q S} {TQ (TQ Y)} {TQ Y} (NaturalTransformation.η (Monad.μ TM) Y)
                  (_∘H_ S {1Q S} {TQ X} {TQ (TQ Y)} (Functor.F₁ TF (sumK ks)) t)) ⟨$⟩ pt) f
      ≈ ∫ᴹ {Y} (map (sumK {1Q S} {Y} (bindK ks t)) ⟨$⟩ pt) f
  bindSumKG {X} {Y} ks t pt f = trans (bindSumKPre ks (map t ⟨$⟩ pt) f)
    (trans (∫ᴹ-sum {Y} (λ n → joinPre {Y} (mapM {X} {TQ Y} (ks n) (map t ⟨$⟩ pt))) f)
      (trans (∑ᶠ-cong (λ n → sym (bindKPt (ks n) t pt f)))
        (sym (∫ᴹ-sumK {1Q S} {Y} (bindK ks t) pt f))))

  ----------------------------------------------------------------------------
  -- scaling as a bind through `score`, and the laws that mention it

  -- the weight-`a` multiple of a global measure: `t` bound through `score a`
  scaleD : ∀ {X : QBS S} → Hom S (1Q S) WQ → Hom S (1Q S) (TQ X) → Hom S (1Q S) (TQ X)
  scaleD {X} a t = _∘H_ S {1Q S} {TQ (TQ X)} {TQ X} (NaturalTransformation.η (Monad.μ TM) X)
    (_∘H_ S {1Q S} {TQ (1Q S)} {TQ (TQ X)} (Functor.F₁ TF t) (_∘H_ S {1Q S} {WQ} {TQ (1Q S)} scoreH a))

  scaleDefG : ∀ {X : QBS S} (a : Hom S (1Q S) WQ) (t : Hom S (1Q S) (TQ X)) (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} (map a ⟨$⟩ pt) (map t ⟨$⟩ pt)) f ≈ ∫ᴹ {X} (map (scaleD {X} a t) ⟨$⟩ pt) f
  scaleDefG {X} a t pt f = scaleDefPre {X} (map a ⟨$⟩ pt) t f

  sumPre-cong : ∀ {X : QBS S} (p q : ℕ → Pre (XW X)) → (∀ n f → ∫ᴹ {X} (p n) f ≈ ∫ᴹ {X} (q n) f) →
    ∀ f → ∫ᴹ {X} (sumPre {X} p) f ≈ ∫ᴹ {X} (sumPre {X} q) f
  sumPre-cong {X} p q h f = trans (∫ᴹ-sum {X} p f) (trans (∑ᶠ-cong (λ n → h n f)) (sym (∫ᴹ-sum {X} q f)))

  normScaleD : ∀ {X : QBS S} (a b : Hom S (1Q S) WQ) → (map a ⟨$⟩ tt) * (map b ⟨$⟩ tt) ≈ 1# →
    ∀ (t : Hom S (1Q S) (TQ X)) →
    Setoid._≈_ (Carrier (_+Q_ S (C.TQ X) (1Q S)))
      (map (normH X) ⟨$⟩ (map (scaleD {X} a t) ⟨$⟩ tt)) (map (normH X) ⟨$⟩ (map t ⟨$⟩ tt))
  normScaleD {X} a b hab t =
    Setoid.trans (Carrier (_+Q_ S (C.TQ X) (1Q S)))
      (Func.cong (map (normH X)) (λ f → sym (scaleDefG {X} a t tt f)))
      (normScaleGlobal {X} (map a ⟨$⟩ tt) (map b ⟨$⟩ tt) hab (map t ⟨$⟩ tt))

  -- the pieces of the s-finite decomposition of a measure: the scaled laws
  scaledK : ∀ {X : QBS S} → (ℕ → Hom S (1Q S) WQ) → (ℕ → Hom S (Probes.ℛQ S) X) → (ℕ → Σ Measure IsProb) →
    ℕ → Hom S (1Q S) (TQ X)
  scaledK {X} w a μ n = scaleD {X} (w n)
    (_∘H_ S {1Q S} {C.TQ X} {TQ X} (ιH X) (ProbabilityInterface.law CP.continuousProb (a n) (μ n)))

  scaledLaws-derived : ∀ {X : QBS S} (t : Hom S (1Q S) (TQ X)) →
    Σ (ℕ → Hom S (Probes.ℛQ S) X) λ a →
    Σ (ℕ → Hom S (1Q S) WQ) λ w →
    Σ (ℕ → Σ Measure IsProb) λ μ →
      ∀ (pt : ∣ 1Q S ∣) (f : Hom S X WQ) →
        ∫ᴹ {X} (map t ⟨$⟩ pt) f ≈ ∫ᴹ {X} (map (sumK {1Q S} {X} (scaledK {X} w a μ)) ⟨$⟩ pt) f
  scaledKPt : ∀ {X : QBS S} (w : ℕ → Hom S (1Q S) WQ) (a : ℕ → Hom S (Probes.ℛQ S) X) (μ : ℕ → Σ Measure IsProb)
    (n : ℕ) (g : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} (map (w n) ⟨$⟩ tt) (ιPre {X} (lawPre (a n) (μ n)))) g
      ≈ ∫ᴹ {X} (map (scaledK {X} w a μ n) ⟨$⟩ tt) g
  scaledKPt {X} w a μ n g = scaleDefPre {X} (map (w n) ⟨$⟩ tt)
    (_∘H_ S {1Q S} {C.TQ X} {TQ X} (ιH X) (ProbabilityInterface.law CP.continuousProb (a n) (μ n))) g

  scaledLaws-derived {X} t =
    let sl = scaledLaws-global {X} t
        a = proj₁ sl
        w = proj₁ (proj₂ sl)
        μ = proj₁ (proj₂ (proj₂ sl))
    in a , w , μ , λ pt f →
         trans (proj₂ (proj₂ (proj₂ sl)) pt f)
           (trans (sumPre-cong {X} (λ n → scalePre {X} (map (w n) ⟨$⟩ tt) (ιPre {X} (lawPre (a n) (μ n))))
                                   (λ n → map (scaledK {X} w a μ n) ⟨$⟩ tt) (λ n g → scaledKPt {X} w a μ n g) f)
             (sym (sumK-pointPre {1Q S} {X} (scaledK {X} w a μ) pt f)))
