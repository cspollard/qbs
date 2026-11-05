{-# OPTIONS --safe --without-K #-}

-- Swapping the first two factors of a triple product (plan 05, helper for `Exchangeable`).
--   * `sw3`: the map (x, (y, z)) ↦ (y, (x, z)) and `swap3`: pushing s ⊗ (t ⊗ r) forward along it gives t ⊗ (s ⊗ r),
--     for arbitrary s-finite s, t, r.
-- Route: both sides integrate to ∫ G d(s ⊗ t) for G(x, y) = ∫ h(y, (x, z)) dr(z): the right side by `Product.∫-prod`
-- (outer t, then s), the left by `∫-prod′` (outer s, then t), the inner integrals compared pointwise by `intR-pt`,
-- `intL-pt` and `∫ᴹ-cong`.
module QBS.Continuous.ExchangeableSwap where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)

module ExchangeableSwap (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; _≈ᴹ_; mapM; module C)
  open Product lem using (prodPre; intL; intR; intL-pt; intR-pt; ∫-prod; ∫-prod′)
  open SFiniteCommute lem using (fixH₂)
  open SFiniteStrong lem using (fixH)
  open QBS
  open Hom

  module _ {X Y Z : QBS S} where

    sw3 : Hom S (_×Q_ S X (_×Q_ S Y Z)) (_×Q_ S Y (_×Q_ S X Z))
    sw3 = pairQ S (_∘H_ S (fstQ S) (sndQ S)) (pairQ S (fstQ S) (_∘H_ S (sndQ S) (sndQ S)))

    -- (x, y), z ↦ (y, (x, z))
    rearr : Hom S (_×Q_ S (_×Q_ S X Y) Z) (_×Q_ S Y (_×Q_ S X Z))
    rearr = pairQ S (_∘H_ S (sndQ S) (fstQ S)) (pairQ S (_∘H_ S (fstQ S) (fstQ S)) (sndQ S))

    -- G(x, y) = ∫ h(y, (x, z)) dr(z)
    Gh : C.Pre (XW Z) → Hom S (_×Q_ S Y (_×Q_ S X Z)) WQ → Hom S (_×Q_ S X Y) WQ
    Gh r h = intR {_×Q_ S X Y} {Z} r (_∘H_ S h rearr)

    G-pt : ∀ r h x y → map (Gh r h) ⟨$⟩ (x , y) ≈ ∫ᴹ {Z} r (fixH {X} {Z} x (fixH {Y} {_×Q_ S X Z} y h))
    G-pt r h x y = trans (intR-pt {_×Q_ S X Y} {Z} r (_∘H_ S h rearr) (x , y)) (∫ᴹ-cong {Z} r (λ z → refl))

    -- ∫ h d(t ⊗ (s ⊗ r)) is ∫ G d(s ⊗ t)
    right-side : ∀ s t r h → ∫ᴹ {_×Q_ S Y (_×Q_ S X Z)} (prodPre {Y} {_×Q_ S X Z} t (prodPre {X} {Z} s r)) h
      ≈ ∫ᴹ {_×Q_ S X Y} (prodPre {X} {Y} s t) (Gh r h)
    right-side s t r h = trans (∫-prod′ {Y} {_×Q_ S X Z} t (prodPre {X} {Z} s r) h)
      (trans (∫ᴹ-cong {Y} t {intR {Y} {_×Q_ S X Z} (prodPre {X} {Z} s r) h} {intL {X} {Y} s (Gh r h)} step)
        (sym (∫-prod {X} {Y} s t (Gh r h))))
      where
        inner : ∀ y x → map (intR {X} {Z} r (fixH {Y} {_×Q_ S X Z} y h)) ⟨$⟩ x ≈ map (fixH₂ {X} {Y} y (Gh r h)) ⟨$⟩ x
        inner y x = trans (intR-pt {X} {Z} r (fixH {Y} {_×Q_ S X Z} y h) x) (sym (G-pt r h x y))
        step : ∀ y → map (intR {Y} {_×Q_ S X Z} (prodPre {X} {Z} s r) h) ⟨$⟩ y ≈ map (intL {X} {Y} s (Gh r h)) ⟨$⟩ y
        step y = trans (intR-pt {Y} {_×Q_ S X Z} (prodPre {X} {Z} s r) h y)
          (trans (∫-prod′ {X} {Z} s r (fixH {Y} {_×Q_ S X Z} y h))
            (trans (∫ᴹ-cong {X} s {intR {X} {Z} r (fixH {Y} {_×Q_ S X Z} y h)} {fixH₂ {X} {Y} y (Gh r h)} (inner y))
              (sym (intL-pt {X} {Y} s (Gh r h) y))))

    inner-L : ∀ r h x y → map (intR {Y} {Z} r (fixH {X} {_×Q_ S Y Z} x (_∘H_ S h sw3))) ⟨$⟩ y
      ≈ map (fixH {X} {Y} x (Gh r h)) ⟨$⟩ y
    inner-L r h x y = trans (intR-pt {Y} {Z} r (fixH {X} {_×Q_ S Y Z} x (_∘H_ S h sw3)) y) (sym (G-pt r h x y))

    left-side : ∀ s t r h → ∫ᴹ {_×Q_ S X (_×Q_ S Y Z)} (prodPre {X} {_×Q_ S Y Z} s (prodPre {Y} {Z} t r)) (_∘H_ S h sw3)
      ≈ ∫ᴹ {_×Q_ S X Y} (prodPre {X} {Y} s t) (Gh r h)
    left-side s t r h = trans (∫-prod′ {X} {_×Q_ S Y Z} s (prodPre {Y} {Z} t r) hs)
      (trans (∫ᴹ-cong {X} s {intR {X} {_×Q_ S Y Z} (prodPre {Y} {Z} t r) hs} {intR {X} {Y} t (Gh r h)} step)
        (sym (∫-prod′ {X} {Y} s t (Gh r h))))
      where
        hs : Hom S (_×Q_ S X (_×Q_ S Y Z)) WQ
        hs = _∘H_ S h sw3
        step : ∀ x → map (intR {X} {_×Q_ S Y Z} (prodPre {Y} {Z} t r) hs) ⟨$⟩ x ≈ map (intR {X} {Y} t (Gh r h)) ⟨$⟩ x
        step x = trans (intR-pt {X} {_×Q_ S Y Z} (prodPre {Y} {Z} t r) hs x)
          (trans (∫-prod′ {Y} {Z} t r (fixH {X} {_×Q_ S Y Z} x hs))
            (trans (∫ᴹ-cong {Y} t {intR {Y} {Z} r (fixH {X} {_×Q_ S Y Z} x hs)} {fixH {X} {Y} x (Gh r h)} (inner-L r h x))
              (sym (intR-pt {X} {Y} t (Gh r h) x))))

    swap3 : ∀ s t r → _≈ᴹ_ {_×Q_ S Y (_×Q_ S X Z)} (mapM {_×Q_ S X (_×Q_ S Y Z)} {_×Q_ S Y (_×Q_ S X Z)} sw3
      (prodPre {X} {_×Q_ S Y Z} s (prodPre {Y} {Z} t r))) (prodPre {Y} {_×Q_ S X Z} t (prodPre {X} {Z} s r))
    swap3 s t r h = trans (∫ᴹ-map {_×Q_ S X (_×Q_ S Y Z)} {_×Q_ S Y (_×Q_ S X Z)} sw3
      (prodPre {X} {_×Q_ S Y Z} s (prodPre {Y} {Z} t r)) h)
      (trans (left-side s t r h) (sym (right-side s t r h)))
