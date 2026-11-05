{-# OPTIONS --safe --without-K #-}

-- Conditionally iid observations given a parameter (plan 05, item 48).  For a kernel K : Θ ⇒ T X of s-finite measures
-- (`SFinite.TQ`):
--   * `ψH`, Kock's double strength T X × T Y ⇒ T (X × Y) as a morphism, agreeing with `Product.prodPre` (`ψ-at`);
--   * the kernel power `kpow n K : Θ ⇒ T (Xⁿ)`, θ ↦ (K θ)^{⊗n} (`ψH` against `kpow`, ending in δ on 1);
--   * `CondIID K n M`: the model M : Θ ⇒ T (Xⁿ) has law (K θ)^{⊗n} at every θ; `kpow` is one (`kpow-iid`), and the
--     notion respects pointwise ≈ᴹ (`CondIID-≈`);
--   * the Bayesian joint π ⋉ M on Θ × Y (`jointM`) and the marginal of the data `margM π M = ∫ M θ dπ(θ)`:
--     integrals against the joint are iterated (`∫-joint`), the data marginal is `margM` (`joint-snd`) and, for a
--     probability model, the parameter marginal is π (`joint-fst`);
--   * for a conditionally iid model of probability kernels, each data coordinate has the marginal law
--     `margM π K` (`marg-coord`): marginally the observations are identically distributed (not independent).
-- Route: `ψ-at` is definitional (`ψH` unfolds to `prodPre`); `kpow-iid` by induction on n with `ψ-at` and `Product.prod-cong`;
-- `∫-joint` from `∫ᴹ-join` and `∫ᴹ-map`; `joint-snd`/`joint-fst` are `∫-joint` at g ∘ snd and g ∘ fst, with the inner
-- integrals computed by `∫ᴹ-σ` (and, for the constant integrand of `joint-fst`, `CondIIDConst.∫-constW`); `marg-coord`
-- from `∫ᴹ-join`, `∫ᴹ-map` and `FinProd.margⁿ` pointwise in θ.
module QBS.Inference.CondIID where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ; 1Q)
open import QBS.BoolQ using (module BoolOn)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Inference.CondIIDConst using (module CondIIDConst)

module CondIID (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; *-cong; *-identityʳ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; TQ; TH; ∫ᴹ; ∫ᶠ; ∫ᴹ-map; ∫ᴹ-join; ∫ᴹ-cong; _≈ᴹ_; mapM; joinPre; module C)
  open SFiniteMonad (lemOf lem₁) using (joinT)
  open SFiniteStrong (lemOf lem₁) using (σH; σPre; ∫ᴹ-σ; fixH)
  open SFiniteCommute (lemOf lem₁) using (τH)
  open Product (lemOf lem₁) using (prodPre; prod-cong)
  open CondIIDConst (lemOf lem₁) using (∫-constW)
  open FinProd lem₁ using (ΠQ; projQ; prodⁿ; margⁿ)
  open BoolOn S using (constQ)
  open QBS
  open Hom

  -- the double strength T X × T Y ⇒ T (X × Y)
  ψH : ∀ X Y → Hom S (_×Q_ S (TQ X) (TQ Y)) (TQ (_×Q_ S X Y))
  ψH X Y = _∘H_ S (joinT (_×Q_ S X Y)) (_∘H_ S (TH (τH X Y)) (σH (TQ X) Y))

  ψ-at : ∀ {X Y : QBS S} (s : C.Pre (XW X)) (t : C.Pre (XW Y)) →
    _≈ᴹ_ {_×Q_ S X Y} (map (ψH X Y) ⟨$⟩ (s , t)) (prodPre {X} {Y} s t)
  ψ-at s t f = refl

  -- the kernel power θ ↦ (K θ)^{⊗n}
  kpow : ∀ {Θ X : QBS S} n → Hom S Θ (TQ X) → Hom S Θ (TQ (ΠQ n (λ _ → X)))
  kpow {Θ} zero K = constQ {Θ} {TQ (1Q S)} (C.ηPre {XW (1Q S)} (1# , tt))
  kpow {Θ} {X} (suc n) K = _∘H_ S (ψH X (ΠQ n (λ _ → X))) (pairQ S K (kpow n K))

  -- conditionally iid given the parameter
  CondIID : ∀ {Θ X : QBS S} → Hom S Θ (TQ X) → ∀ n → Hom S Θ (TQ (ΠQ n (λ _ → X))) → Set₁
  CondIID {Θ} {X} K n M = ∀ θ → _≈ᴹ_ {ΠQ n (λ _ → X)} (map M ⟨$⟩ θ) (prodⁿ n (λ _ → X) (λ _ → map K ⟨$⟩ θ))

  kpow-iid : ∀ {Θ X : QBS S} (K : Hom S Θ (TQ X)) n → CondIID K n (kpow n K)
  kpow-iid {Θ} {X} K zero θ f = refl
  kpow-iid {Θ} {X} K (suc n) θ f = trans (ψ-at {X} {ΠQ n (λ _ → X)} (map K ⟨$⟩ θ) (map (kpow n K) ⟨$⟩ θ) f)
    (prod-cong {X} {ΠQ n (λ _ → X)} (λ g → refl) (kpow-iid K n θ) f)

  CondIID-≈ : ∀ {Θ X : QBS S} (K : Hom S Θ (TQ X)) n (M N : Hom S Θ (TQ (ΠQ n (λ _ → X)))) →
    (∀ θ → _≈ᴹ_ {ΠQ n (λ _ → X)} (map M ⟨$⟩ θ) (map N ⟨$⟩ θ)) → CondIID K n M → CondIID K n N
  CondIID-≈ K n M N e c θ f = trans (sym (e θ f)) (c θ f)

  -- the Bayesian joint π ⋉ M and the marginal of the data
  jointM : ∀ {Θ Y : QBS S} → C.Pre (XW Θ) → Hom S Θ (TQ Y) → C.Pre (XW (_×Q_ S Θ Y))
  jointM {Θ} {Y} π M = joinPre {_×Q_ S Θ Y} (mapM {Θ} {TQ (_×Q_ S Θ Y)} (_∘H_ S (σH Θ Y) (pairQ S (idH S {Θ}) M)) π)

  margM : ∀ {Θ Y : QBS S} → C.Pre (XW Θ) → Hom S Θ (TQ Y) → C.Pre (XW Y)
  margM {Θ} {Y} π M = joinPre {Y} (mapM {Θ} {TQ Y} M π)

  margM-int : ∀ {Θ Y : QBS S} (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ Y)) f →
    ∫ᴹ {Y} (margM π M) f ≈ ∫ᴹ {Θ} π (_∘H_ S (∫ᶠ {Y} f) M)
  margM-int {Θ} {Y} π M f = trans (∫ᴹ-join {Y} (mapM {Θ} {TQ Y} M π) f) (∫ᴹ-map {Θ} {TQ Y} M π (∫ᶠ {Y} f))

  -- θ ↦ ∫ g(θ, y) dM θ(y)
  inner : ∀ {Θ Y : QBS S} → Hom S Θ (TQ Y) → Hom S (_×Q_ S Θ Y) WQ → Hom S Θ WQ
  inner {Θ} {Y} M g = _∘H_ S (∫ᶠ {_×Q_ S Θ Y} g) (_∘H_ S (σH Θ Y) (pairQ S (idH S {Θ}) M))

  ∫-joint : ∀ {Θ Y : QBS S} (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ Y)) g →
    ∫ᴹ {_×Q_ S Θ Y} (jointM π M) g ≈ ∫ᴹ {Θ} π (inner M g)
  ∫-joint {Θ} {Y} π M g = trans (∫ᴹ-join {_×Q_ S Θ Y} _ g) (∫ᴹ-map {Θ} {TQ (_×Q_ S Θ Y)} _ π (∫ᶠ {_×Q_ S Θ Y} g))

  inner-snd : ∀ {Θ Y : QBS S} (M : Hom S Θ (TQ Y)) (f : Hom S Y WQ) θ →
    map (inner M (_∘H_ S f (sndQ S))) ⟨$⟩ θ ≈ ∫ᴹ {Y} (map M ⟨$⟩ θ) f
  inner-snd {Θ} {Y} M f θ = trans (∫ᴹ-σ {Θ} {Y} θ (map M ⟨$⟩ θ) (_∘H_ S f (sndQ S))) (∫ᴹ-cong {Y} (map M ⟨$⟩ θ) (λ y → refl))

  inner-fst : ∀ {Θ Y : QBS S} (M : Hom S Θ (TQ Y)) (f : Hom S Θ WQ) θ → ∫ᴹ {Y} (map M ⟨$⟩ θ) (constW {Y} 1#) ≈ 1# →
    map (inner M (_∘H_ S f (fstQ S))) ⟨$⟩ θ ≈ map f ⟨$⟩ θ
  inner-fst {Θ} {Y} M f θ h = trans (∫ᴹ-σ {Θ} {Y} θ (map M ⟨$⟩ θ) (_∘H_ S f (fstQ S)))
    (trans (∫ᴹ-cong {Y} (map M ⟨$⟩ θ) {fixH {Θ} {Y} θ (_∘H_ S f (fstQ S))} {constW {Y} (map f ⟨$⟩ θ)} (λ y → refl))
      (trans (∫-constW {Y} (map M ⟨$⟩ θ) (map f ⟨$⟩ θ)) (trans (*-cong refl h) (*-identityʳ _))))

  joint-snd : ∀ {Θ Y : QBS S} (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ Y)) →
    _≈ᴹ_ {Y} (mapM {_×Q_ S Θ Y} {Y} (sndQ S) (jointM π M)) (margM π M)
  joint-snd {Θ} {Y} π M f = trans (∫ᴹ-map {_×Q_ S Θ Y} {Y} (sndQ S) (jointM π M) f)
    (trans (∫-joint π M (_∘H_ S f (sndQ S)))
      (trans (∫ᴹ-cong {Θ} π {inner M (_∘H_ S f (sndQ S))} {_∘H_ S (∫ᶠ {Y} f) M} (inner-snd M f)) (sym (margM-int π M f))))

  joint-fst : ∀ {Θ Y : QBS S} (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ Y)) → (∀ θ → ∫ᴹ {Y} (map M ⟨$⟩ θ) (constW {Y} 1#) ≈ 1#) →
    _≈ᴹ_ {Θ} (mapM {_×Q_ S Θ Y} {Θ} (fstQ S) (jointM π M)) π
  joint-fst {Θ} {Y} π M h f = trans (∫ᴹ-map {_×Q_ S Θ Y} {Θ} (fstQ S) (jointM π M) f)
    (trans (∫-joint π M (_∘H_ S f (fstQ S))) (∫ᴹ-cong {Θ} π {inner M (_∘H_ S f (fstQ S))} {f} (λ θ → inner-fst M f θ (h θ))))

  -- marginally, each observation has the law ∫ K θ dπ(θ)
  marg-coord : ∀ {Θ X : QBS S} (π : C.Pre (XW Θ)) (K : Hom S Θ (TQ X)) n M → CondIID K n M →
    (∀ θ → ∫ᴹ {X} (map K ⟨$⟩ θ) (constW {X} 1#) ≈ 1#) →
    ∀ i → _≈ᴹ_ {X} (mapM {ΠQ n (λ _ → X)} {X} (projQ n (λ _ → X) i) (margM π M)) (margM π K)
  marg-coord {Θ} {X} π K n M c h i f = trans (∫ᴹ-map {ΠQ n (λ _ → X)} {X} pr (margM π M) f)
    (trans (∫ᴹ-join {ΠQ n (λ _ → X)} (mapM {Θ} {TQ (ΠQ n (λ _ → X))} M π) (_∘H_ S f pr))
      (trans (∫ᴹ-map {Θ} {TQ (ΠQ n (λ _ → X))} M π (∫ᶠ {ΠQ n (λ _ → X)} (_∘H_ S f pr)))
        (trans (∫ᴹ-cong {Θ} π {_∘H_ S (∫ᶠ {ΠQ n (λ _ → X)} (_∘H_ S f pr)) M} {_∘H_ S (∫ᶠ {X} f) K} pw)
          (sym (trans (∫ᴹ-join {X} (mapM {Θ} {TQ X} K π) f) (∫ᴹ-map {Θ} {TQ X} K π (∫ᶠ {X} f)))))))
    where
      pr = projQ n (λ _ → X) i
      pw : ∀ θ → ∫ᴹ {ΠQ n (λ _ → X)} (map M ⟨$⟩ θ) (_∘H_ S f pr) ≈ ∫ᴹ {X} (map K ⟨$⟩ θ) f
      pw θ = trans (c θ (_∘H_ S f pr)) (trans (sym (∫ᴹ-map {ΠQ n (λ _ → X)} {X} pr (prodⁿ n (λ _ → X) (λ _ → map K ⟨$⟩ θ)) f))
        (margⁿ n (λ _ → X) (λ _ → map K ⟨$⟩ θ) (λ _ → h θ) i f))
