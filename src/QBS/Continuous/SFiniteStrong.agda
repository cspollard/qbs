{-# OPTIONS --safe --without-K #-}

-- Strength and commutativity of the s-finite measure monad.  Commutativity is Fubini for unbounded
-- integrands (`Analysis/JFubini`).

module QBS.Continuous.SFiniteStrong where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.IntegralMonad using (IntegralStrength; module StrongLaws)
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
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
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Classical using (LEM₀)

module SFiniteStrong (lem : LEM₀) where
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

  -- the test function y ↦ f (x , y)
  fixH : ∀ {X Y : QBS S} → ∣ X ∣ → Hom S (_×Q_ S X Y) WQ → Hom S Y WQ
  fixH {X} {Y} x f = record
    { map = record
        { to = λ y → map f ⟨$⟩ (x , y)
        ; cong = λ e → Func.cong (map f) (Setoid.refl (Carrier X) , e) }
    ; map-random = λ {γ} rγ → map-random f {< constₛ x , γ >ₛ} (const-random X x , rγ)
    }

  -- the left strength on pre-measures
  σPre : ∀ {X Y : QBS S} → ∣ _×Q_ S X (TQ Y) ∣ → Pre (XW (_×Q_ S X Y))
  σPre {X} {Y} (x , q) = mk < proj₁ₛ ∘ₛ α q , < constₛ x , proj₂ₛ ∘ₛ α q >ₛ >ₛ
    (proj₁ (α-random q) , (const-random X x , proj₂ (α-random q))) (m q) (ok q)

  ∫ᴹ-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre (XW Y)) (f : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f ≈ ∫ᴹ {Y} q (fixH {X} {Y} x f)
  ∫ᴹ-σ {X} {Y} x q f = J-cong (m q) {ψ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f} {ψ {Y} q (fixH {X} {Y} x f)}
    (mψ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f) (mψ {Y} q (fixH {X} {Y} x f)) (λ r → refl)

  -- the joint probe of a random family `r ↦ (x r , q r)` with `q` given by a section witness
  σJ : ∀ {X Y : QBS S} {β : Func Rˢ (Carrier (_×Q_ S X (TQ Y)))} → Random X (proj₁ₛ ∘ₛ β) →
    WitM {Y} (λ r → proj₂ (β ⟨$⟩ r)) → Joint (XW (_×Q_ S X Y))
  σJ {X} {Y} {β} pb w = pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {WQ} {_×Q_ S X Y}
    (_∘H_ S (fstQ S {WQ} {Y}) (a w))
    (pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {X} {Y} (fstJ {X} (proj₁ₛ ∘ₛ β) pb)
       (_∘H_ S (sndQ S {WQ} {Y}) (a w)))

  σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
  σH X Y = record
    { map = record
        { to = σPre {X} {Y}
        ; cong = λ {(x , q)} {(x′ , q′)} (ex , eq) f →
            trans (∫ᴹ-σ {X} {Y} x q f)
              (trans (eq (fixH {X} {Y} x f))
                (trans (∫ᴹ-cong {Y} q′ {fixH {X} {Y} x f} {fixH {X} {Y} x′ f}
                          (λ y → Func.cong (map f) (ex , Setoid.refl (Carrier Y))))
                  (sym (∫ᴹ-σ {X} {Y} x′ q′ f))))
        }
    ; map-random = λ {β} (pb , w) → record
        { a = σJ {X} {Y} {β} pb w
        ; g = g w
        ; g-ok = g-ok w
        ; g-pr = g-pr w
        ; w-eq = λ r f →
            trans (∫ᴹ-σ {X} {Y} (proj₁ (β ⟨$⟩ r)) (proj₂ (β ⟨$⟩ r)) f)
              (trans (w-eq w r (fixH {X} {Y} (proj₁ (β ⟨$⟩ r)) f))
                (J-cong (g w r) {ψ {Y} (kerP {Y} (a w) (g w) (g-pr w) r) (fixH {X} {Y} (proj₁ (β ⟨$⟩ r)) f)}
                  {ψ {_×Q_ S X Y} (kerP {_×Q_ S X Y} (σJ {X} {Y} {β} pb w) (g w) (g-pr w) r) f}
                  (mψ {Y} (kerP {Y} (a w) (g w) (g-pr w) r) (fixH {X} {Y} (proj₁ (β ⟨$⟩ r)) f))
                  (mψ {_×Q_ S X Y} (kerP {_×Q_ S X Y} (σJ {X} {Y} {β} pb w) (g w) (g-pr w) r) f)
                  (λ s → refl)))
        }
    }

  -- the strength laws follow from the integral equations (`QBS.IntegralMonad`)
  integralσ : IntegralStrength integral
  integralσ = record
    { σH = σH
    ; fixᵗ = λ {X} {Y} → fixH {X} {Y}
    ; eval-fix = λ _ _ _ → refl
    ; ∫-σ = λ X Y x q f → ∫ᴹ-σ {X} {Y} x q f
    }

  open StrongLaws integral monadData integralσ public using (strength; strongMonad)
