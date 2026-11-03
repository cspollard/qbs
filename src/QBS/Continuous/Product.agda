{-# OPTIONS --safe --without-K #-}

-- Product measures and Fubini for tests on X × Y (plan 03, "Translation and products").
--   * `prodPre s t : Pre (XW (X × Y))`, the product of s-finite measures s on X and t on Y (the commutative monad's
--     double strength: σ, then τ, then join);
--   * `∫-prod`: ∫ g d(s ⊗ t) ≈ ∫ (y ↦ ∫ g(x, y) ds(x)) dt(y), and `∫-prod′`: ≈ ∫ (x ↦ ∫ g(x, y) dt(y)) ds(x);
--   * `∫-rect`: ∫ g(x) h(y) d(s ⊗ t) ≈ ∫ g ds · ∫ h dt;
--   * `marg₁`/`marg₂`: the marginals are t(Y) · s and s(X) · t; `prod-cong`: ⊗ respects ≈ᴹ in both arguments.
-- Route: `∫-prod` is `SFiniteCommute.commA` with `intL` pointwise equal to `Fub.Gs` (`τ-int`), `∫-prod′` adds
-- `Fub.fubiniᴹ` (with `intR` pointwise equal to `Fub.Gt`, `SFiniteStrong.∫ᴹ-σ`); `∫-rect` from `∫-prod`, `∫ᴹ-cong`
-- and `∫ᴹ-scale` twice; the marginals from `∫ᴹ-map` and `∫-rect` with h = 1; `prod-cong` from `∫-prod` and `∫-prod′`.
--   Skeleton: holes first.
module QBS.Continuous.Product where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Limits using (_×Q_; fstQ; sndQ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)

module Product (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#)
  open Weights lem using (WQ; constW)
  open SFinite lem using (XW; TQ; ∫ᴹ; _≈ᴹ_; mapM; joinPre; module C)
  open SFiniteSum lem using (scalePre)
  open SFiniteReweight lem using (mulH)
  open SFiniteCommute lem using (τH; fixH₂)
  open SFiniteStrong lem using (σPre; fixH)
  open QBS
  open Hom

  module _ {X Y : QBS S} where

    XY : QBS S
    XY = _×Q_ S X Y

    -- s ⊗ t
    prodPre : C.Pre (XW X) → C.Pre (XW Y) → C.Pre (XW XY)
    prodPre s t = joinPre {XY} (mapM {_×Q_ S (TQ X) Y} {TQ XY} (τH X Y) (σPre {TQ X} {Y} (s , t)))

    -- y ↦ ∫ g(x, y) ds(x) and x ↦ ∫ g(x, y) dt(y)
    intL : C.Pre (XW X) → Hom S XY WQ → Hom S Y WQ
    intL = ?

    intR : C.Pre (XW Y) → Hom S XY WQ → Hom S X WQ
    intR = ?

    intL-pt : ∀ s g y → map (intL s g) ⟨$⟩ y ≈ ∫ᴹ {X} s (fixH₂ {X} {Y} y g)
    intL-pt = ?

    intR-pt : ∀ t g x → map (intR t g) ⟨$⟩ x ≈ ∫ᴹ {Y} t (fixH {X} {Y} x g)
    intR-pt = ?

    -- Fubini
    ∫-prod : ∀ s t (g : Hom S XY WQ) → ∫ᴹ {XY} (prodPre s t) g ≈ ∫ᴹ {Y} t (intL s g)
    ∫-prod = ?

    ∫-prod′ : ∀ s t (g : Hom S XY WQ) → ∫ᴹ {XY} (prodPre s t) g ≈ ∫ᴹ {X} s (intR t g)
    ∫-prod′ = ?

    -- rectangles
    ∫-rect : ∀ s t (g : Hom S X WQ) (h : Hom S Y WQ) →
      ∫ᴹ {XY} (prodPre s t) (mulH {XY} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S))) ≈ ∫ᴹ {X} s g * ∫ᴹ {Y} t h
    ∫-rect = ?

    -- marginals
    marg₁ : ∀ s t → _≈ᴹ_ {X} (mapM {XY} {X} (fstQ S) (prodPre s t)) (scalePre {X} (∫ᴹ {Y} t (constW {Y} 1#)) s)
    marg₁ = ?

    marg₂ : ∀ s t → _≈ᴹ_ {Y} (mapM {XY} {Y} (sndQ S) (prodPre s t)) (scalePre {Y} (∫ᴹ {X} s (constW {X} 1#)) t)
    marg₂ = ?

    prod-cong : ∀ {s s′ t t′} → _≈ᴹ_ {X} s s′ → _≈ᴹ_ {Y} t t′ → _≈ᴹ_ {XY} (prodPre s t) (prodPre s′ t′)
    prod-cong = ?
