{-# OPTIONS --safe --without-K #-}

-- Additivity of KL divergence and entropy over independent products (plan 03, "Information quantities").  For base
-- measures Q₁ on X and Q₂ on Y and densities p₁, p₂ that are normalised (∫ pᵢ dQᵢ ≈ 1) and pointwise strictly
-- positive and finite (`SignedLog.PosQ`, `BndQ`), with the product density p₁ ⊗ p₂ = (x, y) ↦ p₁ x · p₂ y on
-- Q₁ ⊗ Q₂ (`Product.prodPre`):
--   * KL(p₁ ⊗ p₂) ≃ KL(p₁) + KL(p₂) (`KL-⊗`, with `KLInt-⊗`);
--   * Ent(p₁ ⊗ p₂) ≃ Ent(p₁) + Ent(p₂) (`Ent-⊗`, with `EntInt-⊗`).
-- Route: `SignedLog.log-mul` read on the parts, logP(xy) + (logN x + logN y) ≈ (logP x + logP y) + logN(xy) for
-- positive finite x, y (a helper, from `log-mul` and the cross-added `_≃_`); multiply by p₁ x · p₂ y and integrate
-- over Q₁ ⊗ Q₂ (`Entropy.∫-dens`, `FatouAux.∫ᴹ-addX`, `Product.∫-rect`), where ∫ p₂ dQ₂ ≈ 1 removes the second factor
-- from the terms in p₁ only (and symmetrically); read off `_≃∞_` with witness 0.
--   Skeleton: holes first.
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

    KLInt-⊗ : KLInt Q₁ p₁ → KLInt Q₂ p₂ → KLInt Q₁₂ p₁₂
    KLInt-⊗ = ?

    KL-⊗ : ∀ (i : KLInt Q₁ p₁) (j : KLInt Q₂ p₂) → KL Q₁₂ p₁₂ (KLInt-⊗ i j) ≃∞ KL Q₁ p₁ i +∞ KL Q₂ p₂ j
    KL-⊗ = ?

    EntInt-⊗ : EntInt Q₁ p₁ → EntInt Q₂ p₂ → EntInt Q₁₂ p₁₂
    EntInt-⊗ = ?

    Ent-⊗ : ∀ (i : EntInt Q₁ p₁) (j : EntInt Q₂ p₂) → Ent Q₁₂ p₁₂ (EntInt-⊗ i j) ≃∞ Ent Q₁ p₁ i +∞ Ent Q₂ p₂ j
    Ent-⊗ = ?
