{-# OPTIONS --safe --without-K #-}

-- Dyadic scaling of Lebesgue measure on [0,∞), for every measurable test h : [0,∞] ⇒ [0,∞] (the first step of the change of
-- variables, item B of `plans/03`).  With `dblH = scaleH 2 idW` the doubling `x ↦ 2x`:
--   * `∫-dbl`:  ∫ h(2x) dλ ≈ ½ ∫ h dλ;
--   * `∫-half`: ∫ h(x/2) dλ ≈ 2 ∫ h dλ  (the test `h ∘ scaleH ½ idW`);
--   * `∫-tw k`: ∫ h(2ᵏx) dλ ≈ ½ᵏ ∫ h dλ, and `∫-tw′ k`: 2ᵏ · ∫ h(2ᵏx) dλ ≈ ∫ h dλ  (`tw k = 2ᵏ`).
-- Proof of `∫-dbl`.  By `HalfLine.∫ᴹ-leb`, ∫ h(2x) = ∑ₙ ∫₀¹ h(2n + 2u) du.  The first bit of u splits the unit interval
-- (`FirstBitInf.firstBit-J`), `expansion (b :: r) = [b]/2 + expansion r / 2` doubles to `(2n + b) + expansion r`
-- (`DyadicAlg.cons-alg`), so the n-th term is ½ (a₂ₙ + a₂ₙ₊₁) with aₘ the terms of h; regrouping the series over
-- ℕ × Bool ≅ ℕ (`DyadicAlg.∑ᶠ-dbl`) gives ½ ∑ aₘ.
module QBS.Continuous.HalfLineScale where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (true; false)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Cons using (consR)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.FirstBitInf using (module FirstBitInf)

module HalfLineScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; sym; trans; +-cong; *-cong; +-comm; distribˡ; *-assoc; *-identityˡ; *-identityʳ)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open AlgDy A half hh using (two; ix; dbl; cons-alg; ∑ᶠ-dbl; unhalf; mulswap; tw; tw-hp)
  open ExpansionCons A half hh using (expansion-cons)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineRate lem₁ using (scaleH)
  open ExpDist lem₁ using (idW)
  open FirstBitInf lem₁ using (firstBit-J)
  open QBS
  open Hom

  -- the doubling `x ↦ 2x`
  dblH : Hom S WQ WQ
  dblH = scaleH two idW

  -- ∫ h(2x) dλ = ½ ∫ h dλ
  ∫-dbl : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h dblH) ≈ half * ∫ᴹ {WQ} lebPre h
  ∫-dbl h = trans (∫ᴹ-leb g) (trans (∑ᶠ-cong pairTerm)
    (trans (sym (∑ᶠ-scale half _)) (trans (*-cong refl (sym (∑ᶠ-dbl a))) (*-cong refl (sym (∫ᴹ-leb h))))))
    where
    g : Hom S WQ WQ
    g = _∘H_ S h dblH

    a : ℕ → _
    a m = J fairCoin (λ r → map h ⟨$⟩ shiftPt m r) (Meas-hshift m h)

    -- the doubled point is a point of h on the half
    pt : ∀ b n x → map g ⟨$⟩ shiftPt n (consR b x) ≈ map h ⟨$⟩ shiftPt (ix b n) x
    pt b n x = Func.cong (map h) (cons-alg b n (expansion-cons b x))

    pairTerm : ∀ n → J fairCoin (λ r → map g ⟨$⟩ shiftPt n r) (Meas-hshift n g) ≈ half * (a (dbl n) + a (suc (dbl n)))
    pairTerm n = trans (firstBit-J (Meas-hshift n g))
      (trans (+-cong (*-cong refl (J-cong fairCoin _ (Meas-hshift (ix true n) h) (pt true n)))
                     (*-cong refl (J-cong fairCoin _ (Meas-hshift (ix false n) h) (pt false n))))
        (trans (+-comm _ _) (sym (distribˡ half _ _))))

  -- ½(2x) = x
  half-two : ∀ x → half * (two * x) ≈ x
  half-two x = trans (sym (*-assoc half two x))
    (trans (*-cong (trans (distribˡ half 1# 1#) (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh)) refl) (*-identityˡ x))

  -- ∫ h(x/2) dλ = 2 ∫ h dλ
  ∫-half : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH half idW)) ≈ two * ∫ᴹ {WQ} lebPre h
  ∫-half h = unhalf _ _ (trans (sym (∫-dbl g)) (∫ᴹ-cong {WQ} lebPre {_∘H_ S g dblH} {h} pt))
    where
    g : Hom S WQ WQ
    g = _∘H_ S h (scaleH half idW)

    pt : ∀ x → map (_∘H_ S g dblH) ⟨$⟩ x ≈ map h ⟨$⟩ x
    pt x = Func.cong (map h) (half-two x)

  -- iterated: ∫ h(2ᵏx) dλ = ½ᵏ ∫ h dλ
  ∫-tw : ∀ k (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH (tw k) idW)) ≈ hp k * ∫ᴹ {WQ} lebPre h
  ∫-tw zero h = trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S h (scaleH (tw zero) idW)} {h} (λ x → Func.cong (map h) (*-identityˡ x)))
    (sym (*-identityˡ _))
  ∫-tw (suc k) h = trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S h (scaleH (tw (suc k)) idW)} {_∘H_ S (_∘H_ S h (scaleH (tw k) idW)) dblH}
      (λ x → Func.cong (map h) (mulswap (tw k) x)))
    (trans (∫-dbl (_∘H_ S h (scaleH (tw k) idW))) (trans (*-cong refl (∫-tw k h)) (sym (*-assoc half (hp k) _))))

  -- 2ᵏ · ∫ h(2ᵏx) dλ = ∫ h dλ
  ∫-tw′ : ∀ k (h : Hom S WQ WQ) → tw k * ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH (tw k) idW)) ≈ ∫ᴹ {WQ} lebPre h
  ∫-tw′ k h = trans (*-cong refl (∫-tw k h)) (trans (sym (*-assoc (tw k) (hp k) _)) (trans (*-cong (tw-hp k) refl) (*-identityˡ _)))
