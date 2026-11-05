{-# OPTIONS --safe --without-K #-}

-- Additivity of KL divergence and entropy over independent products (plan 03, "Information quantities").  For base
-- measures Q₁ on X and Q₂ on Y and densities p₁, p₂ that are normalised (∫ pᵢ dQᵢ ≈ 1) and pointwise strictly
-- positive and finite (`SignedLog.PosQ`, `BndQ`), with the product density p₁ ⊗ p₂ = (x, y) ↦ p₁ x · p₂ y on
-- Q₁ ⊗ Q₂ (`Product.prodPre`):
--   * KL(p₁ ⊗ p₂) ≃ KL(p₁) + KL(p₂) (`KL-⊗`, with `KLInt-⊗`);
--   * Ent(p₁ ⊗ p₂) ≃ Ent(p₁) + Ent(p₂) (`Ent-⊗`, with `EntInt-⊗`).
-- Route: `SignedLog.log-mul` read on the parts, logP(xy) + (logN x + logN y) ≈ (logP x + logP y) + logN(xy) for
-- positive finite x, y (`InfoProductAux.log-mul-pt`, with log⁻(xy) ≤ log⁻ x + log⁻ y and the same for log⁺, by cases on
-- xy ≤ 1, giving `EntInt`/`KLInt` by domination); multiply by p₁ x · p₂ y and integrate
-- over Q₁ ⊗ Q₂ (`Entropy.∫-dens`, `FatouAux.∫ᴹ-addX`, `Product.∫-rect`), where ∫ p₂ dQ₂ ≈ 1 removes the second factor
-- from the terms in p₁ only (and symmetrically); read off `_≃∞_` with witness 0.
module QBS.Continuous.InfoProduct where

open import Function.Bundles using (_⟨$⟩_)
open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.InfoProductAux using (module InfoProductAux)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.SignedInf using (module SignedInf)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.Entropy using (module Entropy)
open import QBS.Continuous.KLDiv using (module KLDiv)

module InfoProduct (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Product (lemOf lem₁) using (prodPre)
  open SignedInf lem₁ using (_≃∞_; _+∞_)
  open SignedLog lem₁ using (PosQ)
  open Entropy lem₁ using (EntInt; Ent)
  open KLDiv lem₁ using (KLInt; KL)
  open OmegaSemiring A using (_≤_; _+_; _*_; refl; sym; trans; +-cong; *-cong; *-assoc; *-comm; *-identityˡ; *-identityʳ;
    ≤-trans; ≤-reflexive; +-comm; +-identityʳ; 0#; distribˡ; *-mono)
  open Bounded A using (Bnd; finite)
  open SubSemiring finite using (Is-0; Is-+)
  open SFinite (lemOf lem₁) using (∫ᴹ-cong)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SupTest (lemOf lem₁) using (∫ᴹ-monoX)
  open Product (lemOf lem₁) using (∫-rect)
  open SignedExpect lem₁ using (bnd≤; bnd≈)
  open InfoProductAux lem₁ using (log-mul-pt; logN-sub; logP-sub; mul-id)
  open SignedLog lem₁ using (logP; logN)
  open Entropy lem₁ using (logPH; logNH; ∫-dens)
  open SignedInf lem₁ using (mk≃∞)
  open QBS
  open Hom

  module _ {X Y : QBS S} (Q₁ : C.Pre (XW X)) (Q₂ : C.Pre (XW Y)) (p₁ : Hom S X WQ) (p₂ : Hom S Y WQ)
    (pos₁ : ∀ x → PosQ (map p₁ ⟨$⟩ x)) (bnd₁ : ∀ x → BndQ (map p₁ ⟨$⟩ x))
    (pos₂ : ∀ y → PosQ (map p₂ ⟨$⟩ y)) (bnd₂ : ∀ y → BndQ (map p₂ ⟨$⟩ y))
    (n₁ : ∫ᴹ {X} Q₁ p₁ ≈ 1#) (n₂ : ∫ᴹ {Y} Q₂ p₂ ≈ 1#) where

    XY : QBS S
    XY = _×Q_ S X Y

    Q₁₂ : C.Pre (XW XY)
    Q₁₂ = prodPre {X} {Y} Q₁ Q₂

    -- (x, y) ↦ p₁ x · p₂ y
    p₁₂ : Hom S XY WQ
    p₁₂ = mulH {XY} (_∘H_ S p₁ (fstQ S)) (_∘H_ S p₂ (sndQ S))

    u v : Hom S XY WQ
    u = _∘H_ S p₁ (fstQ S)
    v = _∘H_ S p₂ (sndQ S)

    -- w · h(u) and w · h(v), w = p₁ ⊗ p₂, integrate to the integrals of p₁ h(p₁) and p₂ h(p₂)
    rectL : ∀ h → ∫ᴹ {XY} Q₁₂ (mulH {XY} p₁₂ (_∘H_ S h u)) ≈ ∫ᴹ {X} Q₁ (mulH {X} p₁ (_∘H_ S h p₁))
    rectL h = trans (∫ᴹ-cong {XY} Q₁₂ {mulH {XY} p₁₂ (_∘H_ S h u)} {mulH {XY} (_∘H_ S (mulH {X} p₁ (_∘H_ S h p₁)) (fstQ S)) v}
      (λ z → trans (*-assoc _ _ _) (trans (*-cong refl (*-comm _ _)) (sym (*-assoc _ _ _)))))
      (trans (∫-rect Q₁ Q₂ (mulH {X} p₁ (_∘H_ S h p₁)) p₂) (trans (*-cong refl n₂) (*-identityʳ _)))

    rectR : ∀ h → ∫ᴹ {XY} Q₁₂ (mulH {XY} p₁₂ (_∘H_ S h v)) ≈ ∫ᴹ {Y} Q₂ (mulH {Y} p₂ (_∘H_ S h p₂))
    rectR h = trans (∫ᴹ-cong {XY} Q₁₂ {mulH {XY} p₁₂ (_∘H_ S h v)} {mulH {XY} u (_∘H_ S (mulH {Y} p₂ (_∘H_ S h p₂)) (sndQ S))}
      (λ z → *-assoc _ _ _))
      (trans (∫-rect Q₁ Q₂ p₁ (mulH {Y} p₂ (_∘H_ S h p₂))) (trans (*-cong n₁ refl) (*-identityˡ _)))

    Pw Nw Pu Pv Nu Nv : Hom S XY WQ
    Pw = mulH {XY} p₁₂ (_∘H_ S logPH p₁₂)
    Nw = mulH {XY} p₁₂ (_∘H_ S logNH p₁₂)
    Pu = mulH {XY} p₁₂ (_∘H_ S logPH u)
    Pv = mulH {XY} p₁₂ (_∘H_ S logPH v)
    Nu = mulH {XY} p₁₂ (_∘H_ S logNH u)
    Nv = mulH {XY} p₁₂ (_∘H_ S logNH v)

    -- the identity of log-mul-pt, multiplied by w
    ptI : ∀ z → (map Pw ⟨$⟩ z) + ((map Nu ⟨$⟩ z) + (map Nv ⟨$⟩ z)) ≈ ((map Pu ⟨$⟩ z) + (map Pv ⟨$⟩ z)) + (map Nw ⟨$⟩ z)
    ptI z = mul-id _ _ _ _ _ _ _ (log-mul-pt _ _ (pos₁ (map (fstQ S {X} {Y}) ⟨$⟩ z)) (pos₂ (map (sndQ S {X} {Y}) ⟨$⟩ z))
      (bnd₁ (map (fstQ S {X} {Y}) ⟨$⟩ z)) (bnd₂ (map (sndQ S {X} {Y}) ⟨$⟩ z)))

    -- the identity of log-mul-pt, integrated
    ident : ∫ᴹ {XY} Q₁₂ Pw +
        (∫ᴹ {X} Q₁ (mulH {X} p₁ (_∘H_ S logNH p₁)) + ∫ᴹ {Y} Q₂ (mulH {Y} p₂ (_∘H_ S logNH p₂)))
      ≈ (∫ᴹ {X} Q₁ (mulH {X} p₁ (_∘H_ S logPH p₁)) + ∫ᴹ {Y} Q₂ (mulH {Y} p₂ (_∘H_ S logPH p₂)))
        + ∫ᴹ {XY} Q₁₂ Nw
    ident = trans (+-cong refl (+-cong (sym (rectL logNH)) (sym (rectR logNH))))
      (trans (+-cong refl (sym (∫ᴹ-addX {XY} Q₁₂ Nu Nv)))
      (trans (sym (∫ᴹ-addX {XY} Q₁₂ Pw (addX Nu Nv))) (trans (∫ᴹ-cong {XY} Q₁₂ {addX Pw (addX Nu Nv)} {addX (addX Pu Pv) Nw} ptI)
      (trans (∫ᴹ-addX {XY} Q₁₂ (addX Pu Pv) Nw)
        (+-cong (trans (∫ᴹ-addX {XY} Q₁₂ Pu Pv) (+-cong (rectL logPH) (rectR logPH))) refl)))))

    -- finiteness of ∫ w h(w) when h(xy) ≤ h x + h y
    bnd-sub : ∀ (h : Hom S WQ WQ) → (∀ a b → PosQ a → PosQ b → BndQ a → BndQ b →
        map h ⟨$⟩ (a * b) ≤ (map h ⟨$⟩ a) + (map h ⟨$⟩ b)) →
      Bnd (∫ᴹ {X} Q₁ (mulH {X} p₁ (_∘H_ S h p₁))) → Bnd (∫ᴹ {Y} Q₂ (mulH {Y} p₂ (_∘H_ S h p₂))) →
      Bnd (∫ᴹ {XY} Q₁₂ (mulH {XY} p₁₂ (_∘H_ S h p₁₂)))
    bnd-sub h sub i j = bnd≤ {XY} (≤-trans (∫ᴹ-monoX Q₁₂ {mulH {XY} p₁₂ (_∘H_ S h p₁₂)} {addX Hu Hv} pt)
      (≤-reflexive (trans (∫ᴹ-addX {XY} Q₁₂ Hu Hv) (+-cong (rectL h) (rectR h))))) (Is-+ {_} {_} i j)
      where
        Hu = mulH {XY} p₁₂ (_∘H_ S h u)
        Hv = mulH {XY} p₁₂ (_∘H_ S h v)
        pt = λ z → ≤-trans (*-mono _ (sub _ _ (pos₁ (map (fstQ S {X} {Y}) ⟨$⟩ z)) (pos₂ (map (sndQ S {X} {Y}) ⟨$⟩ z))
          (bnd₁ (map (fstQ S {X} {Y}) ⟨$⟩ z)) (bnd₂ (map (sndQ S {X} {Y}) ⟨$⟩ z)))) (≤-reflexive (distribˡ _ _ _))

    KLInt-⊗ : KLInt Q₁ p₁ → KLInt Q₂ p₂ → KLInt Q₁₂ p₁₂
    KLInt-⊗ i j = bnd≈ {XY} (∫-dens Q₁₂ p₁₂ (_∘H_ S logNH p₁₂)) (bnd-sub logNH logN-sub
      (bnd≈ {X} (sym (∫-dens Q₁ p₁ (_∘H_ S logNH p₁))) i) (bnd≈ {Y} (sym (∫-dens Q₂ p₂ (_∘H_ S logNH p₂))) j))

    KL-⊗ : ∀ (i : KLInt Q₁ p₁) (j : KLInt Q₂ p₂) → KL Q₁₂ p₁₂ (KLInt-⊗ i j) ≃∞ KL Q₁ p₁ i +∞ KL Q₂ p₂ j
    KL-⊗ i j = mk≃∞ 0# Is-0 (trans (+-cong (+-cong (∫-dens Q₁₂ p₁₂ (_∘H_ S logPH p₁₂))
      (+-cong (∫-dens Q₁ p₁ (_∘H_ S logNH p₁)) (∫-dens Q₂ p₂ (_∘H_ S logNH p₂)))) refl)
      (trans (+-identityʳ _) (trans ident (trans (sym (+-identityʳ _)) (+-cong (sym (+-cong (+-cong
        (∫-dens Q₁ p₁ (_∘H_ S logPH p₁)) (∫-dens Q₂ p₂ (_∘H_ S logPH p₂))) (∫-dens Q₁₂ p₁₂ (_∘H_ S logNH p₁₂)))) refl)))))

    EntInt-⊗ : EntInt Q₁ p₁ → EntInt Q₂ p₂ → EntInt Q₁₂ p₁₂
    EntInt-⊗ i j = bnd≈ {XY} (∫-dens Q₁₂ p₁₂ (_∘H_ S logPH p₁₂)) (bnd-sub logPH logP-sub
      (bnd≈ {X} (sym (∫-dens Q₁ p₁ (_∘H_ S logPH p₁))) i) (bnd≈ {Y} (sym (∫-dens Q₂ p₂ (_∘H_ S logPH p₂))) j))

    Ent-⊗ : ∀ (i : EntInt Q₁ p₁) (j : EntInt Q₂ p₂) → Ent Q₁₂ p₁₂ (EntInt-⊗ i j) ≃∞ Ent Q₁ p₁ i +∞ Ent Q₂ p₂ j
    Ent-⊗ i j = mk≃∞ 0# Is-0 (trans (+-cong (+-cong (∫-dens Q₁₂ p₁₂ (_∘H_ S logNH p₁₂))
      (+-cong (∫-dens Q₁ p₁ (_∘H_ S logPH p₁)) (∫-dens Q₂ p₂ (_∘H_ S logPH p₂)))) refl)
      (trans (+-identityʳ _) (trans (+-comm _ _) (trans (sym ident) (trans (+-comm _ _) (trans (sym (+-identityʳ _))
        (+-cong (sym (+-cong (+-cong (∫-dens Q₁ p₁ (_∘H_ S logNH p₁)) (∫-dens Q₂ p₂ (_∘H_ S logNH p₂)))
          (∫-dens Q₁₂ p₁₂ (_∘H_ S logPH p₁₂)))) refl)))))))
