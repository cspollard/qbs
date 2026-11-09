{-# OPTIONS --safe --without-K #-}

-- Product measures and Fubini for tests on X × Y (the double strength of the s-finite monad, at the integral level).
--   * `prodPre s t : Pre (XW (X × Y))`, the product of s-finite measures s on X and t on Y (the commutative monad's
--     double strength: σ, then τ, then join);
--   * `∫-prod`: ∫ g d(s ⊗ t) ≈ ∫ (y ↦ ∫ g(x, y) ds(x)) dt(y), and `∫-prod′`: ≈ ∫ (x ↦ ∫ g(x, y) dt(y)) ds(x);
--   * `∫-rect`: ∫ g(x) h(y) d(s ⊗ t) ≈ ∫ g ds · ∫ h dt;
--   * `marg₁`/`marg₂`: the marginals are t(Y) · s and s(X) · t; `prod-cong`: ⊗ respects ≈ᴹ in both arguments.
-- Route: `∫-prod` is `SFiniteCommute.commA` with `intL` pointwise equal to `Fub.Gs` (`τ-int`), `∫-prod′` adds
-- `Fub.fubiniᴹ` (with `intR` pointwise equal to `Fub.Gt`, `SFiniteStrong.∫ᴹ-σ`); `∫-rect` from `∫-prod`, `∫ᴹ-cong`
-- and `∫ᴹ-scale` twice; the marginals from `∫ᴹ-map` and `∫-rect` with h = 1; `prod-cong` from `∫-prod` and `∫-prod′`.
module QBS.Continuous.Product where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Limits using (_×Q_; fstQ; sndQ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)

module Product (lem : LEM₀) where
  open Lebesgue lem using (A; J-cong; J-scale)
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; *-assoc; *-comm; *-cong; *-identityˡ; *-identityʳ)
  open Meas lem using (Meas-const; Meas-⊗)
  open Weights lem using (WQ; constW)
  open SFinite lem using (XW; TQ; ∫ᴹ; ∫ᶠ; ψ; mψ; ∫ᴹ-map; ∫ᴹ-cong; _≈ᴹ_; mapM; joinPre; module C)
  open SFiniteSum lem using (scalePre; ∫ᴹ-scale)
  open SFiniteReweight lem using (mulH)
  open import QBS.Continuous.Weights using ()
  open SFiniteCommute lem using (τH; τ-int; fixH₂; commA; module Fub)
  open SFiniteStrong lem using (σPre; σH; fixH; ∫ᴹ-σ)
  open C.Pre using (m)
  open QBS
  open Hom

  -- c · f integrates to c · ∫ f
  cmul : ∀ {Z : QBS S} (p : C.Pre (XW Z)) c (f : Hom S Z WQ) → ∫ᴹ {Z} p (mulH {Z} (constW {Z} c) f) ≈ c * ∫ᴹ {Z} p f
  cmul {Z} p c f = trans (J-cong (m p) {ψ {Z} p (mulH {Z} (constW {Z} c) f)} {λ r → c * ψ {Z} p f r}
    (mψ {Z} p (mulH {Z} (constW {Z} c) f)) (Meas-⊗ {λ _ → c} {ψ {Z} p f} (Meas-const c) (mψ {Z} p f))
    (λ r → trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _))))
    (J-scale (m p) c {ψ {Z} p f} (mψ {Z} p f))

  module _ {X Y : QBS S} where

    XY : QBS S
    XY = _×Q_ S X Y

    -- s ⊗ t
    prodPre : C.Pre (XW X) → C.Pre (XW Y) → C.Pre (XW XY)
    prodPre s t = joinPre {XY} (mapM {_×Q_ S (TQ X) Y} {TQ XY} (τH X Y) (σPre {TQ X} {Y} (s , t)))

    -- y ↦ ∫ g(x, y) ds(x) and x ↦ ∫ g(x, y) dt(y)
    intL : C.Pre (XW X) → Hom S XY WQ → Hom S Y WQ
    intL s g = fixH {TQ X} {Y} s (_∘H_ S (∫ᶠ {XY} g) (τH X Y))

    intR : C.Pre (XW Y) → Hom S XY WQ → Hom S X WQ
    intR t g = fixH₂ {X} {TQ Y} t (_∘H_ S (∫ᶠ {XY} g) (σH X Y))

    intL-pt : ∀ s g y → map (intL s g) ⟨$⟩ y ≈ ∫ᴹ {X} s (fixH₂ {X} {Y} y g)
    intL-pt s g y = τ-int {X} {Y} s y g

    intR-pt : ∀ t g x → map (intR t g) ⟨$⟩ x ≈ ∫ᴹ {Y} t (fixH {X} {Y} x g)
    intR-pt t g x = ∫ᴹ-σ {X} {Y} x t g

    rect-pt : ∀ s (g : Hom S X WQ) (h : Hom S Y WQ) y →
      map (intL s (mulH {XY} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S)))) ⟨$⟩ y ≈ map (mulH {Y} (constW {Y} (∫ᴹ {X} s g)) h) ⟨$⟩ y
    rect-pt s g h y = trans (intL-pt s _ y) (trans (∫ᴹ-cong {X} s {fixH₂ {X} {Y} y _} {mulH {X} (constW {X} (map h ⟨$⟩ y)) g}
      (λ x → *-comm _ _)) (trans (cmul s (map h ⟨$⟩ y) g) (*-comm _ _)))

    ∫ᴹ-cong-prod : ∀ s t (f f′ : Hom S XY WQ) → (∀ p → map f ⟨$⟩ p ≈ map f′ ⟨$⟩ p) →
      ∫ᴹ {XY} (prodPre s t) f ≈ ∫ᴹ {XY} (prodPre s t) f′
    ∫ᴹ-cong-prod s t f f′ e = ∫ᴹ-cong {XY} (prodPre s t) {f} {f′} e

    -- Fubini
    ∫-prod : ∀ s t (g : Hom S XY WQ) → ∫ᴹ {XY} (prodPre s t) g ≈ ∫ᴹ {Y} t (intL s g)
    ∫-prod s t g = trans (commA {X} {Y} s t g) (∫ᴹ-cong {Y} t {Fub.Gs {X} {Y} s t g} {intL s g} (λ y → refl))

    ∫-prod′ : ∀ s t (g : Hom S XY WQ) → ∫ᴹ {XY} (prodPre s t) g ≈ ∫ᴹ {X} s (intR t g)
    ∫-prod′ s t g = trans (∫-prod s t g) (trans (Fub.fubiniᴹ {X} {Y} s t g)
      (∫ᴹ-cong {X} s {Fub.Gt {X} {Y} s t g} {intR t g} (λ x → refl)))

    -- rectangles
    ∫-rect : ∀ s t (g : Hom S X WQ) (h : Hom S Y WQ) →
      ∫ᴹ {XY} (prodPre s t) (mulH {XY} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S))) ≈ ∫ᴹ {X} s g * ∫ᴹ {Y} t h
    ∫-rect s t g h = trans (∫-prod s t G)
      (trans (∫ᴹ-cong {Y} t {intL s G} {mulH {Y} (constW {Y} (∫ᴹ {X} s g)) h} (rect-pt s g h)) (cmul t (∫ᴹ {X} s g) h))
      where G = mulH {XY} (_∘H_ S g (fstQ S)) (_∘H_ S h (sndQ S))

    -- marginals
    marg₁ : ∀ s t → _≈ᴹ_ {X} (mapM {XY} {X} (fstQ S) (prodPre s t)) (scalePre {X} (∫ᴹ {Y} t (constW {Y} 1#)) s)
    marg₁ s t f = trans (∫ᴹ-map {XY} {X} (fstQ S) (prodPre s t) f)
      (trans (∫ᴹ-cong-prod s t (_∘H_ S f (fstQ S)) (mulH {XY} (_∘H_ S f (fstQ S)) (_∘H_ S (constW {Y} 1#) (sndQ S)))
                (λ _ → sym (*-identityʳ _)))
        (trans (∫-rect s t f (constW {Y} 1#)) (trans (*-comm _ _) (sym (∫ᴹ-scale {X} (∫ᴹ {Y} t (constW {Y} 1#)) s f)))))

    marg₂ : ∀ s t → _≈ᴹ_ {Y} (mapM {XY} {Y} (sndQ S) (prodPre s t)) (scalePre {Y} (∫ᴹ {X} s (constW {X} 1#)) t)
    marg₂ s t f = trans (∫ᴹ-map {XY} {Y} (sndQ S) (prodPre s t) f)
      (trans (∫ᴹ-cong-prod s t (_∘H_ S f (sndQ S)) (mulH {XY} (_∘H_ S (constW {X} 1#) (fstQ S)) (_∘H_ S f (sndQ S)))
                (λ _ → sym (*-identityˡ _)))
        (trans (∫-rect s t (constW {X} 1#) f) (sym (∫ᴹ-scale {Y} (∫ᴹ {X} s (constW {X} 1#)) t f))))

    prod-cong : ∀ {s s′ t t′} → _≈ᴹ_ {X} s s′ → _≈ᴹ_ {Y} t t′ → _≈ᴹ_ {XY} (prodPre s t) (prodPre s′ t′)
    prod-cong {s} {s′} {t} {t′} es et f =
      trans (∫-prod s t f) (trans (∫ᴹ-cong {Y} t {intL s f} {intL s′ f} (λ y → trans (intL-pt s f y)
        (trans (es (fixH₂ {X} {Y} y f)) (sym (intL-pt s′ f y)))))
        (trans (et (intL s′ f)) (sym (∫-prod s′ t′ f))))
