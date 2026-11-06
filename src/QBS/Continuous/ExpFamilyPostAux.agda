{-# OPTIONS --safe --without-K #-}

-- Finite signed tests, their values, and reweighting (plan 07, item 60; helper for `Continuous/ExpFamilyPost`).
-- On tests with both parts finite at every point (`FinT`) the cross-added `_≐_` is safe to chain; here such a test is
-- evaluated at a point to a signed value (`ExpWeight.atSg`), where `≃` is a ring congruence, and the algebra is done
-- on values:
--   * `FinT-+`, `FinT-neg`, `FinT-scale`, `FinT-const`, `FinT-dot`: `FinT` is closed under the test operations and
--     under `ExpFamily.dotT` (finite coefficients);
--   * `atSg-irr`, `atSg-+`, `atSg-neg`, `atSg-scale`, `atSg-const`, `atSg-dot`: evaluation commutes with the
--     operations, `atSg (dotT k χ T) x ≃ χ · (Tⱼ(x))ⱼ`; `≐-atSg`: tests with ≃ values are `≐`;
--   * `expWT-at`: the weight of a finite test at x is `expW` of its value;
--   * `mulH-at`, `reweight-cong`, `reweight-reweight`: reweighting respects pointwise ≈ of densities, and
--     reweighting twice is reweighting by the product;
--   * `prodW N w`, the pointwise product of N weights, with `prodW-zero`, `prodW-suc`;
--   * `norm-cong`: ≈ᴹ measures have ≈ᴹ normalisations (`SFiniteNorm.normPre`), whatever the normalisers.
-- Route: the `atSg` lemmas are definitional up to `≃` (witness 0, `≃-by`); `≐-atSg` cancels the finite witness
-- (`InfAlg.cancel-bnd`); the reweighting lemmas from `SFiniteReweight.∫ᴹ-reweight`, `∫ᴹ-cong` and associativity;
-- `norm-cong` from `SFiniteNorm.normPre-≈` and `SFiniteIncl.ι-cong`.
module QBS.Continuous.ExpFamilyPostAux where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.ExpFamily using (module ExpFamily)
open import QBS.Continuous.InfAlg using (module InfAlg)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module ExpFamilyPostAux (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; 1#; refl; sym; +-cong; +-comm; *-cong; *-assoc)
  open Weights lem using (WQ; constW)
  open Bounded A using (Sg; signedRing; _+S_; _*S_; -S_; _≃_; mk≃; ≃-trans; +S-cong; finite)
  open Sg
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-0; Is-+; Is-*)
  open SgLinAlg signedRing using (Vec; _·_)
  open SignedTest lem₁ using (SgT; _+T_; -T_; scaleT; constT; FinT; _≐_; at⁺; at⁻)
  open SetoidReasoning (OmegaSemiring.setoid A)
  open SFinite lem using (module C; XW; _≈ᴹ_; ≈ᵖ⇒≈ᴹ; ∫ᴹ; ∫ᴹ-cong)
  open C using (Pre)
  open SFiniteReweight lem using (reweightPre; mulH; ∫ᴹ-reweight)
  open SFiniteNorm lem using (normPre; massP; normPre-≈)
  open SFiniteIncl lem using (ιPre; ι-cong)
  open InfAlg lem₁ using (cancel-bnd)
  open ExpWeight lem₁ using (expW; expWT; atSg)
  open ExpFamily lem₁ using (dotT)
  open Hom

  ----------------------------------------------------------------------------
  -- finite tests

  FinT-+ : ∀ {X : QBS S} {f g : SgT X} → FinT f → FinT g → FinT (f +T g)
  FinT-+ ff fg x = Is-+ (proj₁ (ff x)) (proj₁ (fg x)) , Is-+ (proj₂ (ff x)) (proj₂ (fg x))

  FinT-neg : ∀ {X : QBS S} {f : SgT X} → FinT f → FinT (-T f)
  FinT-neg ff x = proj₂ (ff x) , proj₁ (ff x)

  FinT-scale : ∀ {X : QBS S} (c : Sg) {f : SgT X} → FinT f → FinT (scaleT c f)
  FinT-scale c ff x = Is-+ (Is-* (pos-fin c) (proj₁ (ff x))) (Is-* (neg-fin c) (proj₂ (ff x)))
                    , Is-+ (Is-* (pos-fin c) (proj₂ (ff x))) (Is-* (neg-fin c) (proj₁ (ff x)))

  FinT-const : ∀ {X : QBS S} (c : Sg) → FinT (constT {X} c)
  FinT-const c x = pos-fin c , neg-fin c

  FinT-dot : ∀ {X : QBS S} k (χ : Vec k) {T : Fin k → SgT X} → (∀ j → FinT (T j)) → FinT (dotT k χ T)
  FinT-dot zero χ fT = FinT-const (Bounded.0S A)
  FinT-dot (suc k) χ fT = FinT-+ (FinT-scale (χ zero) (fT zero)) (FinT-dot k (λ j → χ (suc j)) (λ j → fT (suc j)))

  ----------------------------------------------------------------------------
  -- values of finite tests

  -- signed values with cross-equal parts are ≃ (witness 0)
  ≃-by : (s t : Sg) → pos s + neg t ≈ pos t + neg s → s ≃ t
  ≃-by s t e = mk≃ 0# Is-0 (+-cong e refl)

  atSg-irr : ∀ {X : QBS S} (f : SgT X) (p q : FinT f) x → atSg f p x ≃ atSg f q x
  atSg-irr f p q x = ≃-by _ _ refl

  atSg-+ : ∀ {X : QBS S} {f g : SgT X} (ff : FinT f) (fg : FinT g) x →
    atSg (f +T g) (FinT-+ ff fg) x ≃ atSg f ff x +S atSg g fg x
  atSg-+ ff fg x = ≃-by _ _ refl

  atSg-neg : ∀ {X : QBS S} {f : SgT X} (ff : FinT f) x → atSg (-T f) (FinT-neg ff) x ≃ -S atSg f ff x
  atSg-neg ff x = ≃-by _ _ refl

  atSg-scale : ∀ {X : QBS S} (c : Sg) {f : SgT X} (ff : FinT f) x →
    atSg (scaleT c f) (FinT-scale c ff) x ≃ c *S atSg f ff x
  atSg-scale c ff x = ≃-by _ _ refl

  atSg-const : ∀ {X : QBS S} (c : Sg) x → atSg (constT {X} c) (FinT-const c) x ≃ c
  atSg-const c x = ≃-by _ _ refl

  atSg-dot : ∀ {X : QBS S} k (χ : Vec k) {T : Fin k → SgT X} (fT : ∀ j → FinT (T j)) x →
    atSg (dotT k χ T) (FinT-dot k χ fT) x ≃ χ · (λ j → atSg (T j) (fT j) x)
  atSg-dot zero χ fT x = ≃-by _ _ refl
  atSg-dot (suc k) χ fT x = ≃-trans (atSg-+ (FinT-scale (χ zero) (fT zero)) (FinT-dot k χ′ fT′) x)
    (+S-cong (atSg-scale (χ zero) (fT zero) x) (atSg-dot k χ′ fT′ x))
    where χ′ = λ j → χ (suc j)
          fT′ = λ j → fT (suc j)

  ≐-atSg : ∀ {X : QBS S} {f g : SgT X} (ff : FinT f) (fg : FinT g) → (∀ x → atSg f ff x ≃ atSg g fg x) → f ≐ g
  ≐-atSg {f = f} {g} ff fg h x with h x
  ... | mk≃ k fk eq = cancel-bnd fk (begin
    k + (at⁺ f x + at⁻ g x)  ≈⟨ +-comm k _ ⟩
    at⁺ f x + at⁻ g x + k    ≈⟨ eq ⟩
    at⁺ g x + at⁻ f x + k    ≈⟨ +-comm _ k ⟩
    k + (at⁺ g x + at⁻ f x)  ∎)

  expWT-at : ∀ {X : QBS S} (f : SgT X) (ff : FinT f) x → map (expWT f) ⟨$⟩ x ≈ expW (atSg f ff x)
  expWT-at f ff x = refl

  ----------------------------------------------------------------------------
  -- reweighting

  mulH-at : ∀ {X : QBS S} (d e : Hom S X WQ) x → map (mulH {X} d e) ⟨$⟩ x ≈ (map d ⟨$⟩ x) * (map e ⟨$⟩ x)
  mulH-at d e x = refl

  reweight-cong : ∀ {X : QBS S} {d d′ : Hom S X WQ} (μ : Pre (XW X)) → (∀ x → map d ⟨$⟩ x ≈ map d′ ⟨$⟩ x) →
    _≈ᴹ_ {X} (reweightPre d μ) (reweightPre d′ μ)
  reweight-cong {X} {d} {d′} μ h f = begin
    ∫ᴹ (reweightPre d μ) f   ≈⟨ ∫ᴹ-reweight d μ f ⟩
    ∫ᴹ μ (mulH {X} d f)      ≈⟨ ∫ᴹ-cong μ {mulH {X} d f} {mulH {X} d′ f} (λ x → *-cong (h x) refl) ⟩
    ∫ᴹ μ (mulH {X} d′ f)     ≈⟨ sym (∫ᴹ-reweight d′ μ f) ⟩
    ∫ᴹ (reweightPre d′ μ) f  ∎

  reweight-reweight : ∀ {X : QBS S} (d e : Hom S X WQ) (μ : Pre (XW X)) →
    _≈ᴹ_ {X} (reweightPre d (reweightPre e μ)) (reweightPre (mulH {X} e d) μ)
  reweight-reweight {X} d e μ f = begin
    ∫ᴹ (reweightPre d (reweightPre e μ)) f  ≈⟨ ∫ᴹ-reweight d (reweightPre e μ) f ⟩
    ∫ᴹ (reweightPre e μ) (mulH {X} d f)     ≈⟨ ∫ᴹ-reweight e μ (mulH {X} d f) ⟩
    ∫ᴹ μ (mulH {X} e (mulH {X} d f))
      ≈⟨ ∫ᴹ-cong μ {mulH {X} e (mulH {X} d f)} {mulH {X} (mulH {X} e d) f} (λ x → sym (*-assoc _ _ _)) ⟩
    ∫ᴹ μ (mulH {X} (mulH {X} e d) f)        ≈⟨ sym (∫ᴹ-reweight (mulH {X} e d) μ f) ⟩
    ∫ᴹ (reweightPre (mulH {X} e d) μ) f     ∎

  ----------------------------------------------------------------------------
  -- products of weights

  prodW : ∀ {X : QBS S} N → (Fin N → Hom S X WQ) → Hom S X WQ
  prodW {X} zero w = constW {X} 1#
  prodW {X} (suc N) w = mulH {X} (w zero) (prodW N (λ i → w (suc i)))

  prodW-zero : ∀ {X : QBS S} (w : Fin 0 → Hom S X WQ) x → map (prodW 0 w) ⟨$⟩ x ≈ 1#
  prodW-zero w x = refl

  prodW-suc : ∀ {X : QBS S} N (w : Fin (suc N) → Hom S X WQ) x →
    map (prodW (suc N) w) ⟨$⟩ x ≈ (map (w zero) ⟨$⟩ x) * (map (prodW N (λ i → w (suc i))) ⟨$⟩ x)
  prodW-suc N w x = refl

  ----------------------------------------------------------------------------
  -- normalisation

  norm-cong : ∀ {X : QBS S} {μ ν : Pre (XW X)} (n m : Cut) (hn : massP μ * n ≈ 1#) (hm : massP ν * m ≈ 1#) →
    _≈ᴹ_ {X} μ ν → _≈ᴹ_ {X} (ιPre (normPre μ n hn)) (ιPre (normPre ν m hm))
  norm-cong {X} {μ} {ν} n m hn hm h = ≈ᵖ⇒≈ᴹ {X} (ιPre (normPre μ n hn)) (ιPre (normPre ν m hm))
    (ι-cong {X} {normPre μ n hn} {normPre ν m hm} (normPre-≈ {X} h n m hn hm))
