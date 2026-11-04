{-# OPTIONS --safe --without-K #-}

-- Kullback–Leibler divergence (plan 03, "Information quantities").  For a base measure Q and a density p : X ⇒ WQ,
-- P = p·Q (`Entropy.densPre`) and
--   * `KL Q p i = E_P[log p] = ∫ p log p dQ ∈ (−∞, ∞]` (`SignedExpect.Ex∞` of `Entropy.logT p`), defined when
--     ∫ p log⁻ p dQ is finite (`KLInt`); this holds whenever Q has finite mass (`KLInt-fin`), since
--     x log(1/x) ≤ 1 pointwise (`xlogN-le`);
--   * Gibbs' inequality: KL ≥ 0 when Q and P are probability measures (`KL-nonneg`), from the pointwise
--     x + x log⁻ x ≤ x log⁺ x + 1, i.e. x log x ≥ x − 1 (`gibbs-pt`);
--   * `KL-one`: the density 1 has divergence 0; `KL-cong`: pointwise equal densities have equal divergence.
-- Route for `xlogN-le` and `gibbs-pt`: by cases x ≤ 1 or 1 ≤ x (`MonusAlg.cut-total`).  For x ≤ 1, log⁺ x ≈ 0 and
-- e^{log⁻ x} ≥ 1 + log⁻ x (`ExpLower.1+≤expC`) with x · e^{log⁻ x} ≈ 1 (`LogNeg.UD`), so x log⁻ x ≤ 1 − x.  For
-- 1 ≤ x, log⁻ x ≈ 0 and x ≤ x log⁺ x + 1 from e^{−y} ≥ 1 − y at y = log⁺ x (or directly from `LogCore`).
-- `KL-nonneg`: integrate `gibbs-pt` against Q (`∫ᴹ-addX`, `∫ᴹ-monoX`, `Entropy.∫-dens`), use ∫ p dQ ≈ 1 and
-- ∫ 1 dQ ≈ 1, and read off the cross-added `_≤∞_` with witness 1.
--   Skeleton: holes first.
module QBS.Continuous.KLDiv where

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SignedInf using (module SignedInf)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.Entropy using (module Entropy)
open import Function.Bundles using (_⟨$⟩_)

module KLDiv (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SignedInf lem₁ using (Sg∞; _≃∞_; _≤∞_; fromPos)
  open SignedExpect lem₁ using (Int⁻; Ex∞)
  open SignedLog lem₁ using (logP; logN)
  open Entropy lem₁ using (logT; densPre)
  open QBS
  open Hom

  -- pointwise facts about x log x
  xlogN-le : ∀ x → x * logN x ≤ 1#
  xlogN-le = ?

  gibbs-pt : ∀ x → x + x * logN x ≤ x * logP x + 1#
  gibbs-pt = ?

  module _ {X : QBS S} (Q : C.Pre (XW X)) where

    -- KL (p·Q ‖ Q) = E_{p·Q}[log p]
    KLInt : Hom S X WQ → Set₁
    KLInt p = Int⁻ (densPre Q p) (logT p)

    KL : ∀ p → KLInt p → Sg∞
    KL p i = Ex∞ (densPre Q p) (logT p) i

    KLInt-fin : ∀ p → Bnd (∫ᴹ {X} Q (constW {X} 1#)) → KLInt p
    KLInt-fin = ?

    -- Gibbs' inequality
    KL-nonneg : ∀ p (i : KLInt p) → ∫ᴹ {X} Q (constW {X} 1#) ≈ 1# → ∫ᴹ {X} Q p ≈ 1# → fromPos 0# ≤∞ KL p i
    KL-nonneg = ?

    KL-one : ∀ (i : KLInt (constW {X} 1#)) → KL (constW {X} 1#) i ≃∞ fromPos 0#
    KL-one = ?

    KL-cong : ∀ p q (i : KLInt p) (j : KLInt q) → (∀ x → map p ⟨$⟩ x ≈ map q ⟨$⟩ x) → KL p i ≃∞ KL q j
    KL-cong = ?
