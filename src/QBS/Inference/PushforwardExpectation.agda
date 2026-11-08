{-# OPTIONS --safe --without-K #-}

-- Expectations of pushforwards are expectations of composites, through the expectation API of `Inference/ExpectationInt`.
-- In a QBS a random variable is a map `f : Y ⇒ X`, and `mapPre f p` is the pushforward of a measure `p` along it
-- (`∫ᴹ (mapM f μ) g ≈ ∫ᴹ μ (g ∘ f)` is `Continuous/SFinite.∫ᴹ-map`; for the probability monad `Continuous/Monad.∫-map`).
--   * `pushI f p c g⁺ g⁻ ep en : ITest (mapPre f p)`: from an integrable test `c` of `p` whose parts agree pointwise with
--     the composites `g⁺ ∘ f`, `g⁻ ∘ f` (`ep`, `en`), the test with parts `g⁺`, `g⁻` for the pushforward;
--   * `E-atᴵ-push : E-atᴵ (mapPre f p) (pushI …) ≃ E-atᴵ p c`, so no new integral is needed for a family built as a pushforward;
--   * `constI p a : ITest p` is the constant test (finite, as the integral of a constant against a probability) with
--     `E-atᴵ-const : E-atᴵ p (constI p a) ≃ a`.
module QBS.Inference.PushforwardExpectation where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
import QBS.Inference.ExpectationInt as EI

module PushforwardExpectation (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; 0#; refl; sym; trans; +-cong)
  open OmegaSemiring A using () renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; Bnd; finite; _≃_; mk≃)
  open SubSemiring using (Is-resp; Is-0)
  open SignedIntegral (lemOf lem₁) using (SF; E-cong; J-const)
  open BoundedSignedTests (lemOf lem₁) using (CutQ)
  open Meas (lemOf lem₁) using (Meas-const)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ; toSF)
  open ITest
  open QBS using (∣_∣)
  open Hom

  ----------------------------------------------------------------------------
  -- the pushforward test

  pushI : ∀ {X Y : QBS S} (f : Hom S Y X) (p : Pre Y) (c : ITest p) (g⁺ g⁻ : Hom S X CutQ) →
    (∀ y → map (pos c) ⟨$⟩ y ≈ map g⁺ ⟨$⟩ (map f ⟨$⟩ y)) → (∀ y → map (neg c) ⟨$⟩ y ≈ map g⁻ ⟨$⟩ (map f ⟨$⟩ y)) →
    ITest (mapPre f p)
  pushI f p c g⁺ g⁻ ep en = record
    { pos = g⁺ ; neg = g⁻
    ; pos-int = Is-resp finite (J-cong (m p) (map-random (pos c) (α-random p)) (map-random g⁺ (α-random (mapPre f p)))
        (λ r → ep (α p ⟨$⟩ r))) (pos-int c)
    ; neg-int = Is-resp finite (J-cong (m p) (map-random (neg c) (α-random p)) (map-random g⁻ (α-random (mapPre f p)))
        (λ r → en (α p ⟨$⟩ r))) (neg-int c) }

  -- `E_{f∗p}[g] ≃ E_p[g ∘ f]`
  E-atᴵ-push : ∀ {X Y : QBS S} (f : Hom S Y X) (p : Pre Y) (c : ITest p) (g⁺ g⁻ : Hom S X CutQ)
    (ep : ∀ y → map (pos c) ⟨$⟩ y ≈ map g⁺ ⟨$⟩ (map f ⟨$⟩ y)) (en : ∀ y → map (neg c) ⟨$⟩ y ≈ map g⁻ ⟨$⟩ (map f ⟨$⟩ y)) →
    E-atᴵ (mapPre f p) (pushI f p c g⁺ g⁻ ep en) ≃ E-atᴵ p c
  E-atᴵ-push f p c g⁺ g⁻ ep en = E-cong {f = toSF (pushI f p c g⁺ g⁻ ep en)} {g = toSF c}
    (λ r → +-cong (sym (ep (α p ⟨$⟩ r))) (en (α p ⟨$⟩ r)))

  ----------------------------------------------------------------------------
  -- constants

  constQ : ∀ {X : QBS S} → ∣A∣ → Hom S X CutQ
  constQ a = record
    { map = record { to = λ _ → a ; cong = λ _ → refl }
    ; map-random = λ _ → Meas-const a }

  constI : ∀ {X : QBS S} (p : Pre X) → Sg → ITest p
  constI {X} p a = record
    { pos = constQ {X} (Sg.pos a) ; neg = constQ {X} (Sg.neg a)
    ; pos-int = Is-resp finite (sym (J-const (ok p) (Sg.pos a))) (Sg.pos-fin a)
    ; neg-int = Is-resp finite (sym (J-const (ok p) (Sg.neg a))) (Sg.neg-fin a) }

  E-atᴵ-const : ∀ {X : QBS S} (p : Pre X) (a : Sg) → E-atᴵ p (constI p a) ≃ a
  E-atᴵ-const p a = mk≃ 0# (Is-0 finite)
    (+-cong (+-cong (J-const (ok p) (Sg.pos a)) (sym (J-const (ok p) (Sg.neg a)))) refl)
