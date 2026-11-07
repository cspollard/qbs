{-# OPTIONS --safe --without-K #-}

-- Densities and scalings of product measures (helper for `Continuous/ExpFamilyAux`).  For s-finite
-- s on X, t on Y, weights v : X ⇒ WQ, w : Y ⇒ WQ and constants a, b in [0, ∞]:
--   * `reweight-cong`: pointwise equal densities give ≈ᴹ measures;
--   * `prod-reweight`: (v · s) ⊗ (w · t) ≈ᴹ (v(x) w(y)) · (s ⊗ t);
--   * `prod-scale`: (a s) ⊗ (b t) ≈ᴹ (a b) (s ⊗ t).
-- Route: both sides through `Product.∫-prod`, with the inner integrals compared pointwise (`Product.intL-pt`,
-- `SFiniteReweight.∫ᴹ-reweight`, `SFiniteSum.∫ᴹ-scale`) and the outer constant moved by `Product.cmul`.
module QBS.Continuous.ProdReweight where

open import Function.Bundles using (_⟨$⟩_)
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
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.Product using (module Product)

module ProdReweight (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _*_; refl; sym; trans; *-assoc; *-comm; *-cong; setoid)
    renaming (Carrier to ∣A∣)
  open import Relation.Binary.Reasoning.Setoid setoid
  open Weights lem using (WQ; constW)
  open SFinite lem using (XW; ∫ᴹ; ∫ᴹ-cong; _≈ᴹ_; module C)
  open C using (Pre)
  open SFiniteSum lem using (scalePre; ∫ᴹ-scale)
  open SFiniteReweight lem using (reweightPre; ∫ᴹ-reweight; mulH)
  open SFiniteCommute lem using (fixH₂)
  open Product lem using (prodPre; intL; intL-pt; ∫-prod; cmul)
  open Hom

  reweight-cong : ∀ {X : QBS S} {v w : Hom S X WQ} (s : Pre (XW X)) → (∀ x → map v ⟨$⟩ x ≈ map w ⟨$⟩ x) →
    _≈ᴹ_ {X} (reweightPre {X} v s) (reweightPre {X} w s)
  reweight-cong {X} {v} {w} s e f = begin
    ∫ᴹ (reweightPre {X} v s) f  ≈⟨ ∫ᴹ-reweight {X} v s f ⟩
    ∫ᴹ s (mulH {X} v f)         ≈⟨ ∫ᴹ-cong {X} s {mulH {X} v f} {mulH {X} w f} (λ x → *-cong (e x) refl) ⟩
    ∫ᴹ s (mulH {X} w f)         ≈⟨ sym (∫ᴹ-reweight {X} w s f) ⟩
    ∫ᴹ (reweightPre {X} w s) f  ∎

  -- c (a b) ≈ (a c) b, the pointwise rearrangement of the densities
  rw-alg : ∀ (a b c : ∣A∣) → c * (a * b) ≈ (a * c) * b
  rw-alg a b c = trans (sym (*-assoc c a b)) (*-cong (*-comm c a) refl)

  -- b (a I) ≈ (a b) I
  sc-alg : ∀ (a b i : ∣A∣) → b * (a * i) ≈ (a * b) * i
  sc-alg a b i = rw-alg a i b

  module _ {X Y : QBS S} (v : Hom S X WQ) (w : Hom S Y WQ) (s : Pre (XW X)) (t : Pre (XW Y)) where
    private
      XY = _×Q_ S X Y
      V : Hom S XY WQ
      V = mulH {XY} (_∘H_ S v (fstQ S)) (_∘H_ S w (sndQ S))

    -- the inner integral at y, with the density w(y) moved inside
    rw-inner : ∀ (g : Hom S XY WQ) y →
      (map w ⟨$⟩ y) * (map (intL {X} {Y} (reweightPre {X} v s) g) ⟨$⟩ y) ≈ map (intL {X} {Y} s (mulH {XY} V g)) ⟨$⟩ y
    rw-inner g y = begin
      wy * (map (intL (reweightPre {X} v s) g) ⟨$⟩ y) ≈⟨ *-cong refl (intL-pt (reweightPre {X} v s) g y) ⟩
      wy * ∫ᴹ {X} (reweightPre {X} v s) (fixH₂ y g)     ≈⟨ *-cong refl (∫ᴹ-reweight {X} v s (fixH₂ y g)) ⟩
      wy * ∫ᴹ {X} s (mulH {X} v (fixH₂ y g))            ≈⟨ sym (cmul s (wy) (mulH {X} v (fixH₂ y g))) ⟩
      ∫ᴹ {X} s (mulH {X} (constW {X} (wy)) (mulH {X} v (fixH₂ y g)))
        ≈⟨ ∫ᴹ-cong {X} s (λ x → rw-alg (map v ⟨$⟩ x) (map g ⟨$⟩ (x , y)) (wy)) ⟩
      ∫ᴹ {X} s (fixH₂ y (mulH {XY} V g))                  ≈⟨ sym (intL-pt s (mulH {XY} V g) y) ⟩
      map (intL s (mulH {XY} V g)) ⟨$⟩ y ∎
      where
        wy : ∣A∣
        wy = map w ⟨$⟩ y

    prod-reweight : _≈ᴹ_ {XY} (prodPre {X} {Y} (reweightPre {X} v s) (reweightPre {Y} w t))
      (reweightPre {XY} V (prodPre {X} {Y} s t))
    prod-reweight g = begin
      ∫ᴹ {XY} (prodPre (reweightPre {X} v s) (reweightPre {Y} w t)) g
        ≈⟨ ∫-prod (reweightPre {X} v s) (reweightPre {Y} w t) g ⟩
      ∫ᴹ {Y} (reweightPre {Y} w t) (intL (reweightPre {X} v s) g)   ≈⟨ ∫ᴹ-reweight {Y} w t (intL (reweightPre {X} v s) g) ⟩
      ∫ᴹ {Y} t (mulH {Y} w (intL (reweightPre {X} v s) g))         ≈⟨ ∫ᴹ-cong {Y} t (rw-inner g) ⟩
      ∫ᴹ {Y} t (intL s (mulH {XY} V g))                           ≈⟨ sym (∫-prod s t (mulH {XY} V g)) ⟩
      ∫ᴹ {XY} (prodPre s t) (mulH {XY} V g)                        ≈⟨ sym (∫ᴹ-reweight {XY} V (prodPre s t) g) ⟩
      ∫ᴹ {XY} (reweightPre {XY} V (prodPre s t)) g ∎

  module _ {X Y : QBS S} (a b : ∣A∣) (s : Pre (XW X)) (t : Pre (XW Y)) where
    private
      XY = _×Q_ S X Y

    sc-inner : ∀ (g : Hom S XY WQ) y →
      map (intL {X} {Y} (scalePre {X} a s) g) ⟨$⟩ y ≈ map (mulH {Y} (constW {Y} a) (intL {X} {Y} s g)) ⟨$⟩ y
    sc-inner g y = begin
      map (intL (scalePre {X} a s) g) ⟨$⟩ y   ≈⟨ intL-pt (scalePre {X} a s) g y ⟩
      ∫ᴹ {X} (scalePre {X} a s) (fixH₂ y g)  ≈⟨ ∫ᴹ-scale {X} a s (fixH₂ y g) ⟩
      a * ∫ᴹ {X} s (fixH₂ y g)              ≈⟨ *-cong refl (sym (intL-pt s g y)) ⟩
      a * (map (intL s g) ⟨$⟩ y) ∎

    prod-scale : _≈ᴹ_ {XY} (prodPre {X} {Y} (scalePre {X} a s) (scalePre {Y} b t))
      (scalePre {XY} (a * b) (prodPre {X} {Y} s t))
    prod-scale g = begin
      ∫ᴹ {XY} (prodPre (scalePre {X} a s) (scalePre {Y} b t)) g
        ≈⟨ ∫-prod (scalePre {X} a s) (scalePre {Y} b t) g ⟩
      ∫ᴹ {Y} (scalePre {Y} b t) (intL (scalePre {X} a s) g)   ≈⟨ ∫ᴹ-scale {Y} b t (intL (scalePre {X} a s) g) ⟩
      b * ∫ᴹ {Y} t (intL (scalePre {X} a s) g)                ≈⟨ *-cong refl (∫ᴹ-cong {Y} t (sc-inner g)) ⟩
      b * ∫ᴹ {Y} t (mulH {Y} (constW {Y} a) (intL s g))       ≈⟨ *-cong refl (cmul t a (intL s g)) ⟩
      b * (a * ∫ᴹ {Y} t (intL s g))                           ≈⟨ sc-alg a b (∫ᴹ {Y} t (intL s g)) ⟩
      (a * b) * ∫ᴹ {Y} t (intL s g)                           ≈⟨ *-cong refl (sym (∫-prod s t g)) ⟩
      (a * b) * ∫ᴹ {XY} (prodPre s t) g                       ≈⟨ sym (∫ᴹ-scale {XY} (a * b) (prodPre s t) g) ⟩
      ∫ᴹ {XY} (scalePre {XY} (a * b) (prodPre s t)) g ∎
