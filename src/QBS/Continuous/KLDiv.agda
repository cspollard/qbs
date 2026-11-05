{-# OPTIONS --safe --without-K #-}

-- Kullback–Leibler divergence (plan 03, "Information quantities").  For a base measure Q and a density p : X ⇒ WQ,
-- P = p·Q (`Entropy.densPre`) and
--   * `KL Q p i = E_P[log p] = ∫ p log p dQ ∈ (−∞, ∞]` (`SignedExpect.Ex∞` of `Entropy.logT p`), defined when
--     ∫ p log⁻ p dQ is finite (`KLInt`); this holds whenever Q has finite mass (`KLInt-fin`), since
--     x log(1/x) ≤ 1 pointwise (`xlogN-le`);
--   * Gibbs' inequality: KL ≥ 0 when Q and P are probability measures (`KL-nonneg`), from the pointwise
--     x + x log⁻ x ≤ x log⁺ x + 1, i.e. x log x ≥ x − 1 (`gibbs-pt`);
--   * `KL-one`: the density 1 has divergence 0; `KL-cong`: pointwise equal densities have equal divergence.
-- Route for `xlogN-le` and `gibbs-pt`: by cases x ≤ 1 or 1 ≤ x (`MonusAlg.cut-total`), with the two bounds x + x log⁻ x ≤ 1
-- (x ≤ 1) and x ≤ x log⁺ x + 1 (1 ≤ x) in the helper `XLog`: the second from e^y ≤ 1 + (y + y²) (`ExpLower.expC≤quad`) and
-- 1 + y ≤ e^y at y = log⁺ x (no e^{−y} ≥ 1 − y needed), and 1 ≤ log⁺ x for unbounded x.
-- `KL-nonneg`: integrate `gibbs-pt` against Q (`∫ᴹ-addX`, `∫ᴹ-monoX`, `Entropy.∫-dens`), use ∫ p dQ ≈ 1 and
-- ∫ 1 dQ ≈ 1, and read off the cross-added `_≤∞_` with witness 1.
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
open import QBS.Continuous.XLog using (module XLog)
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.FatouAux using (module FatouAux)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Analysis.LowerReals using (⊑-refl)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Base using (case_of_)

module KLDiv (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; +-comm; *-comm; zeroˡ; *-identityʳ;
    +-identityˡ; +-identityʳ; ≤-trans; ≤-reflexive; ≤-+ʳ; +-mono; 0-least)
  open OmegaSemiring A using () renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; finite)
  open import QBS.Analysis.Signed using (SubSemiring)
  open SubSemiring finite using (Is-0; Is-1)
  open MonusAlg lem₁ using (cut-total)
  open XLog lem₁ using (small; big)
  open FatouAux lem₁ using (addX; ∫ᴹ-addX)
  open SupTest (lemOf lem₁) using (∫ᴹ-monoX)
  open Product (lemOf lem₁) using (cmul)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; module C)
  open SignedInf lem₁ using (Sg∞; _≃∞_; _≤∞_; fromPos; mk≃∞; mk≤∞)
  open SignedExpect lem₁ using (Int⁻; Ex∞; bnd≤)
  open SignedLog lem₁ using (logP; logN; logP-le; logN-ge; logP-cong; logN-cong)
  open Entropy lem₁ using (logT; densPre; logPH; logNH; ∫-dens)
  open QBS
  open Hom

  -- pointwise facts about x log x
  xlogN-le : ∀ x → x * logN x ≤ 1#
  xlogN-le x = case cut-total x 1# of λ
    { (inj₁ x1) → ≤-trans (≤-trans (≤-+ʳ {x * logN x} {x}) (≤-reflexive (+-comm (x * logN x) x))) (small x x1)
    ; (inj₂ 1x) → ≤-trans (≤-reflexive (trans (*-cong refl (logN-ge x 1x)) (trans (*-comm x 0#) (zeroˡ x)))) 0-least }

  gibbs-pt : ∀ x → x + x * logN x ≤ x * logP x + 1#
  gibbs-pt x = case cut-total x 1# of λ
    { (inj₁ x1) → ≤-trans (small x x1) (≤-reflexive (sym (trans (+-cong (trans (*-cong refl (logP-le x x1))
        (trans (*-comm x 0#) (zeroˡ x))) refl) (+-identityˡ 1#))))
    ; (inj₂ 1x) → ≤-trans (≤-reflexive (trans (+-cong refl (trans (*-cong refl (logN-ge x 1x)) (trans (*-comm x 0#) (zeroˡ x))))
        (+-identityʳ x))) (big x 1x) }

  module _ {X : QBS S} (Q : C.Pre (XW X)) where

    -- KL (p·Q ‖ Q) = E_{p·Q}[log p]
    KLInt : Hom S X WQ → Set₁
    KLInt p = Int⁻ (densPre Q p) (logT p)

    KL : ∀ p → KLInt p → Sg∞
    KL p i = Ex∞ (densPre Q p) (logT p) i

    KLInt-fin : ∀ p → Bnd (∫ᴹ {X} Q (constW {X} 1#)) → KLInt p
    KLInt-fin p fin = bnd≤ {X} (≤-trans (≤-reflexive (∫-dens Q p (_∘H_ S logNH p)))
      (∫ᴹ-monoX Q {mulH {X} p (_∘H_ S logNH p)} {constW {X} 1#} (λ x → xlogN-le (map p ⟨$⟩ x)))) fin

    -- an integral of a pointwise null function
    ∫0 : ∀ (f : Hom S X WQ) → (∀ x → map f ⟨$⟩ x ≈ 0#) → ∫ᴹ {X} Q f ≈ 0#
    ∫0 f e = trans (∫ᴹ-cong {X} Q {f} {mulH {X} (constW {X} 0#) f} (λ x → trans (e x) (sym (zeroˡ _))))
      (trans (cmul Q 0# f) (zeroˡ _))

    -- the integrals of the parts against Q
    dens-cong : ∀ (h : Hom S WQ WQ) p q → (∀ x → map p ⟨$⟩ x ≈ map q ⟨$⟩ x) →
      ∫ᴹ {X} (densPre Q p) (_∘H_ S h p) ≈ ∫ᴹ {X} (densPre Q q) (_∘H_ S h q)
    dens-cong h p q e = trans (∫-dens Q p (_∘H_ S h p)) (trans (∫ᴹ-cong {X} Q {mulH {X} p (_∘H_ S h p)} {mulH {X} q (_∘H_ S h q)}
      (λ x → *-cong (e x) (Func.cong (map h) (e x)))) (sym (∫-dens Q q (_∘H_ S h q))))

    -- Gibbs' inequality
    KL-nonneg : ∀ p (i : KLInt p) → ∫ᴹ {X} Q (constW {X} 1#) ≈ 1# → ∫ᴹ {X} Q p ≈ 1# → fromPos 0# ≤∞ KL p i
    KL-nonneg p i Q1 p1 = mk≤∞ 1# Is-1 (≤-trans (≤-reflexive (trans (+-cong (+-identityˡ _) refl)
      (trans (+-comm _ 1#) (+-cong (sym p1) (∫-dens Q p (_∘H_ S logNH p)))))) (≤-trans G
      (≤-reflexive (trans (+-cong (sym (∫-dens Q p (_∘H_ S logPH p))) Q1) (sym (+-cong (+-identityʳ _) refl))))))
      where
        gp = λ x → gibbs-pt (map p ⟨$⟩ x)
        G = ≤-trans (≤-reflexive (sym (∫ᴹ-addX {X} Q p (mulH {X} p (_∘H_ S logNH p)))))
          (≤-trans (∫ᴹ-monoX Q {addX p (mulH {X} p (_∘H_ S logNH p))} {addX (mulH {X} p (_∘H_ S logPH p)) (constW {X} 1#)} gp)
            (≤-reflexive (∫ᴹ-addX {X} Q (mulH {X} p (_∘H_ S logPH p)) (constW {X} 1#))))

    KL-one : ∀ (i : KLInt (constW {X} 1#)) → KL (constW {X} 1#) i ≃∞ fromPos 0#
    KL-one i = mk≃∞ 0# Is-0 (trans (+-cong (+-cong (trans (∫-dens Q one (_∘H_ S logPH one)) (∫0 _ z⁺)) refl) refl)
      (sym (+-cong (+-cong refl (trans (∫-dens Q one (_∘H_ S logNH one)) (∫0 _ z⁻))) refl)))
      where
        one = constW {X} 1#
        z⁺ : ∀ x → map (mulH {X} one (_∘H_ S logPH one)) ⟨$⟩ x ≈ 0#
        z⁺ x = trans (*-cong refl (logP-le 1# ⊑-refl)) (trans (*-comm _ _) (zeroˡ _))
        z⁻ : ∀ x → map (mulH {X} one (_∘H_ S logNH one)) ⟨$⟩ x ≈ 0#
        z⁻ x = trans (*-cong refl (logN-ge 1# ⊑-refl)) (trans (*-comm _ _) (zeroˡ _))

    KL-cong : ∀ p q (i : KLInt p) (j : KLInt q) → (∀ x → map p ⟨$⟩ x ≈ map q ⟨$⟩ x) → KL p i ≃∞ KL q j
    KL-cong p q i j e = mk≃∞ 0# Is-0 (+-cong (+-cong (dens-cong logPH p q e) (sym (dens-cong logNH p q e))) refl)
