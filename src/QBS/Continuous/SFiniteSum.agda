{-# OPTIONS --safe --without-K #-}

-- Scaling by weights and countable sums of s-finite measures, and the laws of `StatisticalInterface`
-- for them.  A sum is the join of a glued random family of measures over a discrete probability
-- measure on the index (`Borel/Lead`), with the weights `2ⁿ⁺¹` compensating the masses `2⁻⁽ⁿ⁺¹⁾`.

module QBS.Continuous.SFiniteSum where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ; !Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘; borel-≗)
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
open import QBS.Borel.Lead using (module Lead; pt)
open import QBS.Analysis.JSum using (module JSum)
open import QBS.Analysis.MixtureN using (module MixtureN)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Classical using (LEM₀)

module SFiniteSum (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ)
  open RandomSource S using (Rˢ) renaming (meas-id to measId)
  open SFinite lem
  open WitM
  open SFiniteMonad lem
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom
  open JSum lem
  open MixtureN A using (mixN; mixN-prob)
  open Series A
  open Lead lem

  ----------------------------------------------------------------------------
  -- scaling by a weight

  scalePre : ∀ {X : QBS S} → ∣ WQ ∣ → Pre (XW X) → Pre (XW X)
  scalePre {X} c p = mk (scaleₛ ∘ₛ α p)
    (Meas-⊗ {λ _ → c} {λ r → proj₁ (α p ⟨$⟩ r)} (Meas-const c) (proj₁ (α-random p)) , proj₂ (α-random p))
    (m p) (ok p)
    where
      scaleₛ : Func (Carrier (XW X)) (Carrier (XW X))
      scaleₛ = record { to = λ (w , x) → c * w , x ; cong = λ e → *-cong refl (proj₁ e) , proj₂ e }

  ∫ᴹ-scale : ∀ {X : QBS S} (c : ∣ WQ ∣) (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} c p) f ≈ c * ∫ᴹ {X} p f
  ∫ᴹ-scale {X} c p f = trans
    (J-cong (m p) {ψ {X} (scalePre {X} c p) f} {λ r → c * ψ {X} p f r}
       (mψ {X} (scalePre {X} c p) f) (Meas-⊗ {λ _ → c} {ψ {X} p f} (Meas-const c) (mψ {X} p f))
       (λ r → *-assoc c (proj₁ (α p ⟨$⟩ r)) (map f ⟨$⟩ proj₂ (α p ⟨$⟩ r))))
    (J-scale (m p) c {ψ {X} p f} (mψ {X} p f))

  ----------------------------------------------------------------------------
  -- countable sums

  -- `lead` does not distinguish points that agree everywhere
  lead-≗ : ∀ {x y : R₁} → x R≈.≈ y → lead (lower x) ≡.≡ lead (lower y)
  lead-≗ {x} {y} e = ≡.sym (proj₁ (borel-≗ (lead-partition (lead (lower x))) {lower x} {lower y} (lower e)) ≡.refl)

  leadₛ : Func Rˢ ℕˢ
  leadₛ = record { to = λ r → lead (lower r) ; cong = lead-≗ }

  -- the discrete probability measure with mass hp (n+1) at the point trueⁿ false false …
  νI : Measure
  νI = mixN (λ n → hp (ℕ.suc n)) ∑hp≤1 (λ n → dirac (lift (pt n)))

  νI-prob : IsProb νI
  νI-prob = mixN-prob (λ n → hp (ℕ.suc n)) ∑hp≤1 (λ n → dirac (lift (pt n))) ∑hp≈1 (λ n → IsProb-dirac (lift (pt n)))

  abstract
    -- the random family r ↦ (2ⁿ⁺¹, tsₙ) with n = lead r, glued from constants
    sumFam : ∀ {X : QBS S} → (ℕ → Pre (XW X)) → Pre (XW (TQ X))
    sumFam {X} ts = mk (glueₛ leadₛ (λ n → constₛ (pw (ℕ.suc n) , ts n)))
      ( Meas-glue {λ r → lead (lower r)} {λ k _ → pw (ℕ.suc k)} lead-partition (λ k → Meas-const (pw (ℕ.suc k)))
      , QBS.glue-random (TQ X) {leadₛ} lead-partition (λ n → constₛ (ts n))
          (λ n → QBS.const-random (TQ X) (ts n)) )
      νI νI-prob

    sumPre : ∀ {X : QBS S} → (ℕ → Pre (XW X)) → Pre (XW X)
    sumPre {X} ts = joinPre {X} (sumFam {X} ts)

    ∫ᴹ-sum : ∀ {X : QBS S} (ts : ℕ → Pre (XW X)) (f : Hom S X WQ) →
      ∫ᴹ {X} (sumPre {X} ts) f ≈ ∑ᶠ (λ n → ∫ᴹ {X} (ts n) f)
    ∫ᴹ-sum {X} ts f = trans (∫ᴹ-join {X} (sumFam {X} ts) f)
      (trans (J-mixN (λ n → hp (ℕ.suc n)) ∑hp≤1 (λ n → dirac (lift (pt n))) {ψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f)}
                (mψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f)))
        (∑ᶠ-cong term))
      where
        term : ∀ n → hp (ℕ.suc n) * J (dirac (lift (pt n))) (ψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f))
            (mψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f))
                     ≈ ∫ᴹ {X} (ts n) f
        term n = trans
            (*-cong refl (J-dirac (lift (pt n)) {ψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f)} (mψ {TQ X} (sumFam {X} ts) (∫ᶠ {X} f))))
          (trans (Setoid.reflexive Aˢ (≡.cong (λ k → hp (ℕ.suc n) * (pw (ℕ.suc k) * ∫ᴹ {X} (ts k) f)) (lead-pt n)))
            (trans (sym (*-assoc (hp (ℕ.suc n)) (pw (ℕ.suc n)) (∫ᴹ {X} (ts n) f)))
              (trans (*-cong (hp-pw (ℕ.suc n)) refl) (*-identityˡ _))))

  ----------------------------------------------------------------------------
  -- laws at the level of pre-measures

  ∫ᴹ-sum-cong : ∀ {X : QBS S} (ts ts′ : ℕ → Pre (XW X)) → (∀ n → _≈ᴹ_ {X} (ts n) (ts′ n)) →
    _≈ᴹ_ {X} (sumPre {X} ts) (sumPre {X} ts′)
  ∫ᴹ-sum-cong {X} ts ts′ e f = trans (∫ᴹ-sum {X} ts f)
    (trans (∑ᶠ-cong (λ n → e n f)) (sym (∫ᴹ-sum {X} ts′ f)))

  sum-nat-lem : ∀ {X Y : QBS S} (f : Hom S X Y) (ts : ℕ → Pre (XW X)) (h : Hom S Y WQ) →
    ∫ᴹ {Y} (mapM {X} {Y} f (sumPre {X} ts)) h ≈ ∫ᴹ {Y} (sumPre {Y} (λ n → mapM {X} {Y} f (ts n))) h
  sum-nat-lem {X} {Y} f ts h = trans (∫ᴹ-map {X} {Y} f (sumPre {X} ts) h)
    (trans (∫ᴹ-sum {X} ts (_∘H_ S h f))
      (trans (∑ᶠ-cong (λ n → sym (∫ᴹ-map {X} {Y} f (ts n) h)))
        (sym (∫ᴹ-sum {Y} (λ n → mapM {X} {Y} f (ts n)) h))))

  sum-join-lem : ∀ {X : QBS S} (ts : ℕ → Pre (XW (TQ X))) (h : Hom S X WQ) →
    ∫ᴹ {X} (joinPre {X} (sumPre {TQ X} ts)) h ≈ ∫ᴹ {X} (sumPre {X} (λ n → joinPre {X} (ts n))) h
  sum-join-lem {X} ts h = trans (∫ᴹ-join {X} (sumPre {TQ X} ts) h)
    (trans (∫ᴹ-sum {TQ X} ts (∫ᶠ {X} h))
      (trans (∑ᶠ-cong (λ n → sym (∫ᴹ-join {X} (ts n) h)))
        (sym (∫ᴹ-sum {X} (λ n → joinPre {X} (ts n)) h))))

  scale-sum-lem : ∀ {X : QBS S} (a : ∣ WQ ∣) (ts : ℕ → Pre (XW X)) (h : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} a (sumPre {X} ts)) h ≈ ∫ᴹ {X} (sumPre {X} (λ n → scalePre {X} a (ts n))) h
  scale-sum-lem {X} a ts h = trans (∫ᴹ-scale {X} a (sumPre {X} ts) h)
    (trans (*-cong refl (∫ᴹ-sum {X} ts h))
      (trans (∑ᶠ-scale a (λ n → ∫ᴹ {X} (ts n) h))
        (trans (∑ᶠ-cong (λ n → sym (∫ᴹ-scale {X} a (ts n) h)))
          (sym (∫ᴹ-sum {X} (λ n → scalePre {X} a (ts n)) h)))))

  scale-nat-lem : ∀ {X Y : QBS S} (f : Hom S X Y) (a : ∣ WQ ∣) (p : Pre (XW X)) (h : Hom S Y WQ) →
    ∫ᴹ {Y} (mapM {X} {Y} f (scalePre {X} a p)) h ≈ ∫ᴹ {Y} (scalePre {Y} a (mapM {X} {Y} f p)) h
  scale-nat-lem {X} {Y} f a p h = trans (∫ᴹ-map {X} {Y} f (scalePre {X} a p) h)
    (trans (∫ᴹ-scale {X} a p (_∘H_ S h f))
      (trans (*-cong refl (sym (∫ᴹ-map {X} {Y} f p h)))
        (sym (∫ᴹ-scale {Y} a (mapM {X} {Y} f p) h))))

  scale-join-lem : ∀ {X : QBS S} (a : ∣ WQ ∣) (q : Pre (XW (TQ X))) (h : Hom S X WQ) →
    ∫ᴹ {X} (joinPre {X} (scalePre {TQ X} a q)) h ≈ ∫ᴹ {X} (scalePre {X} a (joinPre {X} q)) h
  scale-join-lem {X} a q h = trans (∫ᴹ-join {X} (scalePre {TQ X} a q) h)
    (trans (∫ᴹ-scale {TQ X} a q (∫ᶠ {X} h))
      (trans (*-cong refl (sym (∫ᴹ-join {X} q h)))
        (sym (∫ᴹ-scale {X} a (joinPre {X} q) h))))

  scale-one-lem : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) → ∫ᴹ {X} (scalePre {X} 1# p) f ≈ ∫ᴹ {X} p f
  scale-one-lem {X} p f = trans (∫ᴹ-scale {X} 1# p f) (*-identityˡ _)

  scale-mul-lem : ∀ {X : QBS S} (a b : ∣ WQ ∣) (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} (scalePre {X} (a * b) p) f ≈ ∫ᴹ {X} (scalePre {X} a (scalePre {X} b p)) f
  scale-mul-lem {X} a b p f = trans (∫ᴹ-scale {X} (a * b) p f)
    (trans (*-assoc a b _) (trans (*-cong refl (sym (∫ᴹ-scale {X} b p f))) (sym (∫ᴹ-scale {X} a (scalePre {X} b p) f))))

  ----------------------------------------------------------------------------
  -- global elements

  scaleM : ∀ {X : QBS S} → Hom S (1Q S) WQ → Hom S (1Q S) (TQ X) → Hom S (1Q S) (TQ X)
  scaleM {X} a t = record
    { map = record
        { to = λ pt → scalePre {X} (map a ⟨$⟩ pt) (map t ⟨$⟩ pt)
        ; cong = λ _ _ → refl }
    ; map-random = λ _ → QBS.const-random (TQ X) (scalePre {X} (map a ⟨$⟩ tt) (map t ⟨$⟩ tt))
    }

  sumM : ∀ {X : QBS S} → (ℕ → Hom S (1Q S) (TQ X)) → Hom S (1Q S) (TQ X)
  sumM {X} ts = record
    { map = record
        { to = λ _ → sumPre {X} (λ n → map (ts n) ⟨$⟩ tt)
        ; cong = λ _ _ → refl }
    ; map-random = λ _ → QBS.const-random (TQ X) (sumPre {X} (λ n → map (ts n) ⟨$⟩ tt))
    }

  ----------------------------------------------------------------------------
  -- countable sums of kernels

  abstract
    -- the joint probe r , s ↦ (2ⁿ⁺¹, kₙ (γ r)) with n = lead s, for a random γ in X
    aSum : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) {γ : Func Rˢ (Carrier X)} → Random X γ → Joint (XW (TQ Y))
    aSum {X} {Y} ks {γ} rγ = record
      { map = record
          { to = λ p → pw (ℕ.suc (lead (lower (proj₂ p)))) , map (ks (lead (lower (proj₂ p)))) ⟨$⟩ (γ ⟨$⟩ proj₁ p)
          ; cong = λ {p} {p′} (e₁ , e₂) →
              let le = lead-≗ e₂ ; T = Carrier (TQ Y)
              in Setoid.reflexive Aˢ (≡.cong (λ n → pw (ℕ.suc n)) le)
               , Setoid.trans T (Func.cong (map (ks _)) (Func.cong γ e₁))
                   (Setoid.reflexive T (≡.cong (λ n → map (ks n) ⟨$⟩ (γ ⟨$⟩ proj₁ p′)) le)) }
      ; map-random = λ {γ′} (m₁ , m₂) →
          Meas-pre {λ s → pw (ℕ.suc (lead (lower s)))} {λ x → proj₂ (γ′ ⟨$⟩ x)}
            (Meas-glue {λ s → lead (lower s)} {λ k _ → pw (ℕ.suc k)} lead-partition (λ k → Meas-const (pw (ℕ.suc k)))) m₂
          , QBS.glue-random (TQ Y) {leadₛ ∘ₛ proj₂ₛ ∘ₛ γ′}
              (RandomSource.idx-pre S {leadₛ} {proj₂ₛ ∘ₛ γ′} lead-partition m₂)
              (λ n → map (ks n) ∘ₛ γ ∘ₛ proj₁ₛ ∘ₛ γ′)
              (λ n → map-random (ks n) {γ ∘ₛ proj₁ₛ ∘ₛ γ′} (QBS.pre-random X {γ} {proj₁ₛ ∘ₛ γ′} rγ m₁))
      }

    sumFamW : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) {γ : Func Rˢ (Carrier X)} (rγ : Random X γ) →
      WitM {TQ Y} (λ r → sumFam {Y} (λ n → map (ks n) ⟨$⟩ (γ ⟨$⟩ r)))
    sumFamW {X} {Y} ks {γ} rγ = record
      { a = aSum ks rγ ; g = λ _ → νI ; g-ok = constK νI ; g-pr = λ _ → νI-prob
      ; w-eq = λ r h → J-cong νI {ψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ (γ ⟨$⟩ r))) h}
          {ψ {TQ Y} (kerP {TQ Y} (aSum ks rγ) (λ _ → νI) (λ _ → νI-prob) r) h}
          (mψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ (γ ⟨$⟩ r))) h)
          (mψ {TQ Y} (kerP {TQ Y} (aSum ks rγ) (λ _ → νI) (λ _ → νI-prob) r) h) (λ s → refl) }

    sumFamH : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S X (TQ (TQ Y))
    sumFamH {X} {Y} ks = record
      { map = record
          { to = λ x → sumFam {Y} (λ n → map (ks n) ⟨$⟩ x)
          ; cong = λ {x} {x′} e F → J-cong νI {ψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ x)) F}
              {ψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ x′)) F}
              (mψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ x)) F) (mψ {TQ Y} (sumFam {Y} (λ n → map (ks n) ⟨$⟩ x′)) F)
              (λ s → *-cong refl (Func.cong (map F) (Func.cong (map (ks (lead (lower s)))) e))) }
      ; map-random = λ {γ} rγ → sumFamW ks {γ} rγ
      }

    sumK : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S X (TQ Y)
    sumK {X} {Y} ks = _∘H_ S {X} {TQ (TQ Y)} {TQ Y} (joinT Y) (sumFamH ks)

    -- the integral of a sum of kernels at a point
    ∫ᴹ-sumK : ∀ {X Y : QBS S} (ks : ℕ → Hom S X (TQ Y)) (x : ∣ X ∣) (h : Hom S Y WQ) →
      ∫ᴹ {Y} (map (sumK ks) ⟨$⟩ x) h ≈ ∑ᶠ (λ n → ∫ᴹ {Y} (map (ks n) ⟨$⟩ x) h)
    ∫ᴹ-sumK {X} {Y} ks x h = ∫ᴹ-sum {Y} (λ n → map (ks n) ⟨$⟩ x) h
