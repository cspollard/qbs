{-# OPTIONS --safe --without-K #-}

-- Log tests and entropy relative to a base measure.
--   * `logPH`, `logNH : WQ ⇒ WQ`, the parts of the logarithm (`SignedLog.logP`, `logN`) as morphisms
--     (`MonoTest.monoH`, `antiH`), and for a density p : X ⇒ WQ the signed tests `logT p = log p` and
--     `nlogT p = −log p`;
--   * `densPre μ p`, the measure with density p w.r.t. μ (`SFiniteReweight.reweightPre`), with `∫-dens`;
--   * the entropy of p·μ relative to μ, `Ent μ p i = E_{p·μ}[−log p] ∈ (−∞, ∞]` (`SignedExpect.Ex∞`), defined when
--     ∫ p log⁺ p dμ is finite (`EntInt`);
--   * densities at most 1 (the discrete case, μ a counting measure): −log p ≥ 0, so `EntInt` holds (`EntInt-le1`) and
--     the entropy is the value `ent μ p = ∫ p log⁻ p dμ ∈ [0, ∞]` (`Ent-le1`); a constant density c gives
--     c log(1/c) times the mass of μ (`ent-const`), so a uniform density 1/n on n points gives log n.
-- Route: `∫ᴹ-reweight` turns integrals under p·μ into ∫ p · (−) dμ; for p ≤ 1, `SignedLog.logP-le` gives log⁺ p ≈ 0.
module QBS.Continuous.Entropy where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_)
open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.LowerReals using (⊑-refl)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.MonoTest using (module MonoTest)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedInf using (module SignedInf)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SignedLog using (module SignedLog)

module Entropy (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _*_; 0#; 1#; refl; sym; trans; zeroˡ; *-identityʳ; *-comm; +-cong; *-cong)
  open OmegaSemiring A using () renaming (Carrier to ∣A∣)
  open Bounded A using (finite)
  open SubSemiring finite using (Is-0)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open Product (lemOf lem₁) using (cmul)
  open MonoTest lem₁ using (monoH; antiH)
  open SignedTest lem₁ using (SgT; -T_)
  open SignedInf lem₁ using (Sg∞; _≃∞_; fromPos; mk≃∞)
  open SignedExpect lem₁ using (Int⁻; Ex∞; bnd≈)
  open SignedLog lem₁ using (logP-le; logN-ge; logP; logN; logP-cong; logN-cong; logP-mono; logN-anti)
  open QBS
  open Hom

  -- the parts of the logarithm as morphisms
  logPH logNH : Hom S WQ WQ
  logPH = monoH logP logP-cong logP-mono
  logNH = antiH logN logN-cong logN-anti

  module _ {X : QBS S} where

    -- log p and −log p
    logT nlogT : Hom S X WQ → SgT X
    logT p = _∘H_ S logPH p , _∘H_ S logNH p
    nlogT p = -T logT p

    -- the measure with density p w.r.t. μ
    densPre : C.Pre (XW X) → Hom S X WQ → C.Pre (XW X)
    densPre μ p = reweightPre {X} p μ

    ∫-dens : ∀ μ p (f : Hom S X WQ) → ∫ᴹ {X} (densPre μ p) f ≈ ∫ᴹ {X} μ (mulH {X} p f)
    ∫-dens μ p f = ∫ᴹ-reweight {X} p μ f

    -- entropy relative to μ: E_{p·μ}[−log p]
    EntInt : C.Pre (XW X) → Hom S X WQ → Set₁
    EntInt μ p = Int⁻ (densPre μ p) (nlogT p)

    Ent : ∀ μ p → EntInt μ p → Sg∞
    Ent μ p i = Ex∞ (densPre μ p) (nlogT p) i

    -- densities at most 1
    Le1 : Hom S X WQ → Set₁
    Le1 p = ∀ x → map p ⟨$⟩ x ≤ 1#

    -- p log⁺ p ≈ 0, pointwise and under the integral
    plog0 : ∀ μ (p : Hom S X WQ) → Le1 p → ∫ᴹ {X} μ (mulH {X} p (_∘H_ S logPH p)) ≈ 0#
    plog0 μ p l = trans (∫ᴹ-cong {X} μ {mulH {X} p (_∘H_ S logPH p)} {mulH {X} (constW {X} 0#) p}
      (λ x → trans (*-cong refl (logP-le (map p ⟨$⟩ x) (l x))) (*-comm _ _))) (trans (cmul μ 0# p) (zeroˡ _))

    EntInt-le1 : ∀ μ p → Le1 p → EntInt μ p
    EntInt-le1 μ p l = bnd≈ {X} (trans (∫-dens μ p (_∘H_ S logPH p)) (plog0 μ p l)) Is-0

    ent : C.Pre (XW X) → Hom S X WQ → ∣A∣
    ent μ p = ∫ᴹ {X} μ (mulH {X} p (_∘H_ S logNH p))

    Ent-le1 : ∀ μ p (l : Le1 p) → Ent μ p (EntInt-le1 μ p l) ≃∞ fromPos (ent μ p)
    Ent-le1 μ p l = mk≃∞ 0# Is-0 (trans (+-cong (+-cong (∫-dens μ p (_∘H_ S logNH p)) refl) refl)
      (sym (+-cong (+-cong refl (trans (∫-dens μ p (_∘H_ S logPH p)) (plog0 μ p l))) refl)))

    ent-const : ∀ μ c → ent μ (constW {X} c) ≈ (c * logN c) * ∫ᴹ {X} μ (constW {X} 1#)
    ent-const μ c = trans (∫ᴹ-cong {X} μ {mulH {X} (constW {X} c) (_∘H_ S logNH (constW {X} c))}
      {mulH {X} (constW {X} (c * logN c)) (constW {X} 1#)} (λ x → sym (*-identityʳ _))) (cmul μ (c * logN c) (constW {X} 1#))

    ent-one : ∀ μ → ent μ (constW {X} 1#) ≈ 0#
    ent-one μ = trans (ent-const μ 1#) (trans (*-cong (trans (*-cong refl (logN-ge 1# ⊑-refl))
      (trans (*-comm _ _) (zeroˡ 1#))) refl) (zeroˡ (∫ᴹ {X} μ (constW {X} 1#))))
