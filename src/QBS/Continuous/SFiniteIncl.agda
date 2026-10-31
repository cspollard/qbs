{-# OPTIONS --safe --without-K #-}

-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteIncl where

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
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

module SFiniteIncl (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroâ)
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
  module CS = Strength A lem funext probClass
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- Prob ⊂ M: a probability measure is a measure with weight 1

  pairW : ∀ {X : QBS S} → Hom S X (XW X)
  pairW {X} = pairQ S {X} {WQ} {X} (constW 1#) (idH S)

  ιPre : ∀ {X : QBS S} → C.Pre X → Pre (XW X)
  ιPre {X} p = C.mapPre {X} {XW X} (pairW {X}) p

  ι-cong : ∀ {X : QBS S} {p q : C.Pre X} → C._≈ᵖ_ {X} p q → C._≈ᵖ_ {XW X} (ιPre {X} p) (ιPre {X} q)
  ι-cong {X} {p} {q} e h = trans (C.∫-map {X} {XW X} (pairW {X}) p h)
    (trans (e (_∘H_ S h (pairW {X}))) (sym (C.∫-map {X} {XW X} (pairW {X}) q h)))

  ιH : ∀ X → Hom S (C.TQ X) (TQ X)
  ιH X = record
    { map = record
        { to = ιPre {X}
        ; cong = λ {p} {q} e → ≈ᵖ⇒≈ᴹ {X} (ιPre {X} p) (ιPre {X} q) (ι-cong {X} {p} {q} e) }
    ; map-random = λ {β} w → fromWit {X} (map-random (C.TH {X} {XW X} (pairW {X})) w)
    }

  ι-nat : ∀ {X Y : QBS S} (f : Hom S X Y) (p : C.Pre X) (h : Hom S Y WQ) →
    ∫ᴹ {Y} (ιPre {Y} (C.mapPre {X} {Y} f p)) h ≈ ∫ᴹ {Y} (mapM {X} {Y} f (ιPre {X} p)) h
  ι-nat {X} {Y} f p h =
    trans (J-cong (m p) {ψ {Y} (ιPre {Y} (C.mapPre {X} {Y} f p)) h} {ψ {X} (ιPre {X} p) (_∘H_ S h f)}
             (mψ {Y} (ιPre {Y} (C.mapPre {X} {Y} f p)) h) (mψ {X} (ιPre {X} p) (_∘H_ S h f)) (λ r → refl))
      (sym (∫ᴹ-map {X} {Y} f (ιPre {X} p) h))

  ι-unit : ∀ {X : QBS S} (x : ∣ X ∣) (h : Hom S X WQ) →
    ∫ᴹ {X} (ιPre {X} (C.ηPre {X} x)) h ≈ ∫ᴹ {X} (C.ηPre {XW X} (1# , x)) h
  ι-unit {X} x h = J-cong (dirac r₀) {ψ {X} (ιPre {X} (C.ηPre {X} x)) h} {ψ {X} (C.ηPre {XW X} (1# , x)) h}
    (mψ {X} (ιPre {X} (C.ηPre {X} x)) h) (mψ {X} (C.ηPre {XW X} (1# , x)) h) (λ r → refl)

  -- the r-th section of the merged kernel in `ι-mult`, as an element of `Pre U`
  ι-kp : ∀ {U : QBS S} (q : C.Pre (C.TQ U)) → R₁ → C.Pre U
  ι-kp {U} q r = mk {U} (sec {U} (C.Wit.a {U} {α q} (α-random q)) r) (sec-random {U} (C.Wit.a {U} {α q} (α-random q)) r)
    (C.Wit.g {U} {α q} (α-random q) r) (C.Wit.g-pr {U} {α q} (α-random q) r)

  -- the data of `ι-mult-pw`: the outer kernel `gq`, the joint probe `a₀`, the integrand `Ψ` and the r-th section `kq r`
  module IMult {U : QBS S} (q : C.Pre (C.TQ U)) (h : Hom S U WQ) where
    gq : R₁ → Measure
    gq = C.Wit.g {U} {α q} (α-random q)
    a₀ : C.Joint U
    a₀ = C.Wit.a {U} {α q} (α-random q)
    Ψ : R₁ → ∣A∣
    Ψ = ψ {U} (ιPre {U} (C.joinPre {U} q)) h
    mΨ : Meas Ψ
    mΨ = mψ {U} (ιPre {U} (C.joinPre {U} q)) h

    kq : R₁ → Pre (XW U)
    kq r = ιPre {U} (ι-kp q r)

    mΨ∘merge : ∀ r → Meas (λ s → Ψ (mergeR r s))
    mΨ∘merge r = Meas-pre {Ψ} {mergeR r} mΨ (measurable-merge₁ (lower r))

    -- 1. push the merged measure back along `mergeR r`
    step-push : ∀ r → J (P₁.pushMerge gq r) Ψ mΨ ≈ J (gq r) (λ s → Ψ (mergeR r s)) (mΨ∘merge r)
    step-push r = J-push {mergeR r} (measurable-merge₁ (lower r)) (gq r) {Ψ} mΨ (mΨ∘merge r)

    -- 2. the section of the joined probe is the r-th section `kq r`
    step-section : ∀ r → J (gq r) (λ s → Ψ (mergeR r s)) (mΨ∘merge r) ≈ J (gq r) (ψ {U} (kq r) h) (mψ {U} (kq r) h)
    step-section r = J-cong (gq r) {λ s → Ψ (mergeR r s)} {ψ {U} (kq r) h} (mΨ∘merge r) (mψ {U} (kq r) h)
      (λ s → *-cong refl (Func.cong (map h) (Func.cong (map a₀) (merge-evens r s , merge-odds r s))))

    -- 3. that section integrates to the r-th value of the pushed-forward `ι q`
    step-kernel : ∀ r → J (gq r) (ψ {U} (kq r) h) (mψ {U} (kq r) h)
      ≈ ψ {TQ U} (ιPre {TQ U} (C.mapPre {C.TQ U} {TQ U} (ιH U) q)) (∫ᶠ {U} h) r
    step-kernel r = trans
      (sym (≈ᵖ⇒≈ᴹ {U} (ιPre {U} (α q r)) (kq r) (ι-cong {U} {α q r} {ι-kp q r} (C.Wit.w-eq {U} {α q} (α-random q) r)) h))
      (sym (*-identityˡ _))

  -- pointwise in the outer parameter r: the merged kernel integrates ψ of the join to ψ of the pushed-forward ι q
  ι-mult-pw : ∀ {U : QBS S} (q : C.Pre (C.TQ U)) (h : Hom S U WQ) (r : R₁) →
    J (P₁.pushMerge (C.Wit.g {U} {α q} (α-random q)) r) (ψ {U} (ιPre {U} (C.joinPre {U} q)) h)
        (mψ {U} (ιPre {U} (C.joinPre {U} q)) h)
      ≈ ψ {TQ U} (ιPre {TQ U} (C.mapPre {C.TQ U} {TQ U} (ιH U) q)) (∫ᶠ {U} h) r
  ι-mult-pw {U} q h r = trans (step-push r) (trans (step-section r) (step-kernel r))
    where open IMult {U} q h

  ι-mult : ∀ {U : QBS S} (q : C.Pre (C.TQ U)) (h : Hom S U WQ) →
    ∫ᴹ {U} (ιPre {U} (C.joinPre {U} q)) h
      ≈ ∫ᴹ {U} (joinPre {U} (ιPre {TQ U} (C.mapPre {C.TQ U} {TQ U} (ιH U) q))) h
  ι-mult {U} q h = trans
    (J-bind (m q) (P₁.pushMerge (C.Wit.g {U} {α q} (α-random q)))
       (P₁.KernelOk-pushMerge {C.Wit.g {U} {α q} (α-random q)} (C.Wit.g-ok {U} {α q} (α-random q)))
       {ψ {U} (ιPre {U} (C.joinPre {U} q)) h} (mψ {U} (ιPre {U} (C.joinPre {U} q)) h)
       (Meas-J (P₁.pushMerge (C.Wit.g {U} {α q} (α-random q)))
          (P₁.KernelOk-pushMerge {C.Wit.g {U} {α q} (α-random q)} (C.Wit.g-ok {U} {α q} (α-random q)))
          {ψ {U} (ιPre {U} (C.joinPre {U} q)) h} (mψ {U} (ιPre {U} (C.joinPre {U} q)) h)))
    (trans (J-cong (m q)
              (Meas-J (P₁.pushMerge (C.Wit.g {U} {α q} (α-random q)))
                (P₁.KernelOk-pushMerge {C.Wit.g {U} {α q} (α-random q)} (C.Wit.g-ok {U} {α q} (α-random q)))
                {ψ {U} (ιPre {U} (C.joinPre {U} q)) h} (mψ {U} (ιPre {U} (C.joinPre {U} q)) h))
              (mψ {TQ U} (ιPre {TQ U} (C.mapPre {C.TQ U} {TQ U} (ιH U) q)) (∫ᶠ {U} h))
              (ι-mult-pw q h))
           (sym (∫ᴹ-join {U} (ιPre {TQ U} (C.mapPre {C.TQ U} {TQ U} (ιH U) q)) h)))

  ι-strong : ∀ {A B : QBS S} (a : ∣ A ∣) (p : C.Pre B) (h : Hom S (_×Q_ S A B) WQ) →
    ∫ᴹ {_×Q_ S A B} (ιPre {_×Q_ S A B} (CS.σPre {A} {B} (a , p))) h
      ≈ ∫ᴹ {_×Q_ S A B} (σPre {A} {B} (a , ιPre {B} p)) h
  ι-strong {A} {B} a p h = J-cong (m p)
    {ψ {_×Q_ S A B} (ιPre {_×Q_ S A B} (CS.σPre {A} {B} (a , p))) h} {ψ {_×Q_ S A B} (σPre {A} {B} (a , ιPre {B} p)) h}
    (mψ {_×Q_ S A B} (ιPre {_×Q_ S A B} (CS.σPre {A} {B} (a , p))) h) (mψ {_×Q_ S A B} (σPre {A} {B} (a , ιPre {B} p)) h)
    (λ r → refl)

  inclusion : Monad⇒-id TM C.TM
  inclusion = record
    { α = record
        { η = ιH
        ; commute = λ {X} {Y} f p h → ι-nat {X} {Y} f p h
        ; sym-commute = λ {X} {Y} f p h → sym (ι-nat {X} {Y} f p h)
        }
    ; unit-comp = λ {X} x h → ι-unit {X} x h
    ; mult-comp = λ {U} q h → ι-mult {U} q h
    }

  ----------------------------------------------------------------------------
  -- the zero measure and score

  -- a weight at a point: the measure on 1 with total mass w
  scorePre : ∣ WQ ∣ → Pre (XW (1Q S))
  scorePre w = mk (λ _ → w , tt) (Meas-const w , tt) (dirac r₀) (IsProb-dirac r₀)

  ∫ᴹ-score : ∀ (w : ∣ WQ ∣) (h : Hom S (1Q S) WQ) → ∫ᴹ {1Q S} (scorePre w) h ≈ w * (map h ⟨$⟩ tt)
  ∫ᴹ-score w h = J-dirac r₀ {ψ {1Q S} (scorePre w) h} (mψ {1Q S} (scorePre w) h)

  scoreH : Hom S WQ (TQ (1Q S))
  scoreH = record
    { map = record
        { to = scorePre
        ; cong = λ {w} {w′} e h → trans (∫ᴹ-score w h) (trans (*-cong e refl) (sym (∫ᴹ-score w′ h))) }
    ; map-random = λ {γ} mγ → record
        { a = pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {WQ} {1Q S} (fstJ {WQ} γ mγ) (!Q S)
        ; g = λ _ → dirac r₀
        ; g-ok = constK (dirac r₀)
        ; g-pr = λ _ → IsProb-dirac r₀
        ; w-eq = λ r h → trans (∫ᴹ-score (γ r) h)
            (sym (J-dirac r₀
                {ψ {1Q S} (kerP {1Q S} (pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {WQ} {1Q S} (fstJ {WQ} γ mγ) (!Q S))
                                         (λ _ → dirac r₀) (λ _ → IsProb-dirac r₀) r) h}
                (mψ {1Q S} (kerP {1Q S} (pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {WQ} {1Q S} (fstJ {WQ} γ mγ) (!Q S))
                              (λ _ → dirac r₀) (λ _ → IsProb-dirac r₀) r) h))) }
    }

  zeroPre : Pre (XW (1Q S))
  zeroPre = scorePre 0#

  zeroH : Hom S (1Q S) (TQ (1Q S))
  zeroH = _∘H_ S {1Q S} {WQ} {TQ (1Q S)} scoreH zeroâ

  zero-bind : ∀ (k : Hom S (1Q S) (TQ (1Q S))) (pt : ∣ 1Q S ∣) (h : Hom S (1Q S) WQ) →
    ∫ᴹ {1Q S} (joinPre {1Q S} (mapM {1Q S} {TQ (1Q S)} k zeroPre)) h ≈ ∫ᴹ {1Q S} zeroPre h
  zero-bind k pt h = trans (∫ᴹ-join {1Q S} (mapM {1Q S} {TQ (1Q S)} k zeroPre) h)
    (trans (∫ᴹ-map {1Q S} {TQ (1Q S)} k zeroPre (∫ᶠ {1Q S} h))
      (trans (∫ᴹ-score 0# (_∘H_ S {1Q S} {TQ (1Q S)} {WQ} (∫ᶠ {1Q S} h) k))
        (trans (zeroˡ _) (trans (sym (zeroˡ _)) (sym (∫ᴹ-score 0# h))))))
