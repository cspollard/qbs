{-# OPTIONS --safe --without-K #-}

-- Push-forward of s-finite measures along maps and products (plan 05, helper for `Independence` and `FinProdPair`).
--   * `mapM-comp`, `mapM-cong`, `mapM-ext`: push-forward composes, respects ≈ᴹ and pointwise equal maps;
--   * `_×H_`: the map (x, y) ↦ (f x, g y), and `map-prod`: pushing s ⊗ t forward along f × g gives f₊s ⊗ g₊t;
--   * `swapQ` and `swapM`: pushing s ⊗ t forward along (x, y) ↦ (y, x) gives t ⊗ s.
-- Route: through the integrals: `SFinite.∫ᴹ-map`, `Product.∫-prod` for the left-nested product and `Product.∫-prod′` for
-- the swap, with the inner integrals compared pointwise by `Product.intL-pt`/`intR-pt` and `∫ᴹ-cong`.
module QBS.Continuous.ProdMap where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Bundles using (Setoid)

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

module ProdMap (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; _≈ᴹ_; mapM; module C)
  open Product lem using (prodPre; intL; intR; intL-pt; intR-pt; ∫-prod; ∫-prod′)
  open SFiniteCommute lem using (fixH₂)
  open SFiniteStrong lem using (fixH)
  open QBS
  open Hom

  mapM-comp : ∀ {X Y Z : QBS S} (f : Hom S X Y) (g : Hom S Y Z) (p : C.Pre (XW X)) →
    _≈ᴹ_ {Z} (mapM {Y} {Z} g (mapM {X} {Y} f p)) (mapM {X} {Z} (_∘H_ S g f) p)
  mapM-comp {X} {Y} {Z} f g p h = trans (∫ᴹ-map {Y} {Z} g (mapM {X} {Y} f p) h)
    (trans (∫ᴹ-map {X} {Y} f p (_∘H_ S h g)) (sym (∫ᴹ-map {X} {Z} (_∘H_ S g f) p h)))

  mapM-cong : ∀ {X Y : QBS S} (f : Hom S X Y) {p q : C.Pre (XW X)} → _≈ᴹ_ {X} p q → _≈ᴹ_ {Y} (mapM {X} {Y} f p) (mapM {X} {Y} f q)
  mapM-cong {X} {Y} f e h = trans (∫ᴹ-map {X} {Y} f _ h) (trans (e (_∘H_ S h f)) (sym (∫ᴹ-map {X} {Y} f _ h)))

  mapM-ext : ∀ {X Y : QBS S} (f g : Hom S X Y) (p : C.Pre (XW X)) →
    (∀ x → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)) → _≈ᴹ_ {Y} (mapM {X} {Y} f p) (mapM {X} {Y} g p)
  mapM-ext {X} {Y} f g p e h = trans (∫ᴹ-map {X} {Y} f p h) (trans (∫ᴹ-cong {X} p {_∘H_ S h f} {_∘H_ S h g}
    (λ x → Func.cong (map h) (e x))) (sym (∫ᴹ-map {X} {Y} g p h)))

  -- (x, y) ↦ (f x, g y)
  _×H_ : ∀ {X Y X′ Y′ : QBS S} → Hom S X X′ → Hom S Y Y′ → Hom S (_×Q_ S X Y) (_×Q_ S X′ Y′)
  f ×H g = pairQ S (_∘H_ S f (fstQ S)) (_∘H_ S g (sndQ S))

  map-prod : ∀ {X Y X′ Y′ : QBS S} (f : Hom S X X′) (g : Hom S Y Y′) (s : C.Pre (XW X)) (t : C.Pre (XW Y)) →
    _≈ᴹ_ {_×Q_ S X′ Y′} (mapM {_×Q_ S X Y} {_×Q_ S X′ Y′} (f ×H g) (prodPre {X} {Y} s t))
      (prodPre {X′} {Y′} (mapM {X} {X′} f s) (mapM {Y} {Y′} g t))
  map-prod {X} {Y} {X′} {Y′} f g s t h =
    trans (∫ᴹ-map {_×Q_ S X Y} {_×Q_ S X′ Y′} (f ×H g) (prodPre {X} {Y} s t) h)
    (trans (∫-prod {X} {Y} s t (_∘H_ S h (f ×H g)))
    (trans (∫ᴹ-cong {Y} t {intL {X} {Y} s (_∘H_ S h (f ×H g))} {_∘H_ S (intL {X′} {Y′} (mapM {X} {X′} f s) h) g}
      (λ y → trans (intL-pt {X} {Y} s (_∘H_ S h (f ×H g)) y)
        (trans (∫ᴹ-cong {X} s {fixH₂ {X} {Y} y (_∘H_ S h (f ×H g))} {_∘H_ S (fixH₂ {X′} {Y′} (map g ⟨$⟩ y) h) f} (λ x → refl))
        (trans (sym (∫ᴹ-map {X} {X′} f s (fixH₂ {X′} {Y′} (map g ⟨$⟩ y) h)))
          (sym (intL-pt {X′} {Y′} (mapM {X} {X′} f s) h (map g ⟨$⟩ y)))))))
    (trans (sym (∫ᴹ-map {Y} {Y′} g t (intL {X′} {Y′} (mapM {X} {X′} f s) h)))
      (sym (∫-prod {X′} {Y′} (mapM {X} {X′} f s) (mapM {Y} {Y′} g t) h)))))

  -- (x, y) ↦ (y, x)
  swapQ : ∀ {X Y : QBS S} → Hom S (_×Q_ S X Y) (_×Q_ S Y X)
  swapQ = pairQ S (sndQ S) (fstQ S)

  swapM : ∀ {X Y : QBS S} (s : C.Pre (XW X)) (t : C.Pre (XW Y)) →
    _≈ᴹ_ {_×Q_ S Y X} (mapM {_×Q_ S X Y} {_×Q_ S Y X} swapQ (prodPre {X} {Y} s t)) (prodPre {Y} {X} t s)
  swapM {X} {Y} s t h = trans (∫ᴹ-map {_×Q_ S X Y} {_×Q_ S Y X} swapQ (prodPre {X} {Y} s t) h)
    (trans (∫-prod′ {X} {Y} s t (_∘H_ S h swapQ))
    (trans (∫ᴹ-cong {X} s {intR {X} {Y} t (_∘H_ S h swapQ)} {intL {Y} {X} t h}
      (λ x → trans (intR-pt {X} {Y} t (_∘H_ S h swapQ) x) (trans (∫ᴹ-cong {Y} t {fixH {X} {Y} x (_∘H_ S h swapQ)}
        {fixH₂ {Y} {X} x h} (λ _ → refl)) (sym (intL-pt {Y} {X} t h x)))))
    (sym (∫-prod {Y} {X} t s h))))
