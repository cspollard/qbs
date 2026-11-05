{-# OPTIONS --safe --without-K #-}

-- Translation of Lebesgue measure on [0,∞) by every finite cut (plan 03, "Uniqueness on the half-line").
-- With `shiftH t` the map x ↦ x + t, for every test h,
--   `∫-shift : ∫ h(x + t) dx + ∫_{[0,t)} h dx ≈ ∫ h dx`.
-- Route: `shiftedLeb t`, the measure h ↦ ∫ h(x + t) dx + ∫_{[0,t)} h dx, gives [a,b) the mass b − a (`shifted-Iv`: the
-- first part is λ([a,b) ∩ [t,∞)) translated, the second λ([a,b) ∩ [0,t))), and nothing to ∞, so it is Lebesgue measure
-- (`LebesgueInterval.leb-unique`).  Integer t is `HalfLine.shiftPre`.
module QBS.Continuous.LebesgueShift where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using ([_,_]′)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Analysis.Series using (module Series)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.LebesgueShiftCut using (module LebesgueShiftCut)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)

module LebesgueShift (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; sym; trans; +-cong; +-identityˡ; +-identityʳ; zeroˡ; 0-least; ≤-trans; ≤-reflexive; ≤-+ʳ; +-comm)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ; constW)
  open Series A using (∑ᶠ; ∑ᶠ-shift; ∑ᶠ-zero)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; mapM; ∫ᴹ-map; ∫ᴹ-cong; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open SFiniteSum (lemOf lem₁) using (sumPre; scalePre; ∫ᴹ-sum; ∫ᴹ-scale)
  open HalfLine lem₁ using (lebPre)
  open ExpDist lem₁ using (idW)
  open Domination lem₁ using (addH)
  open Intervals (lemOf lem₁) using (χIv; χInf)
  open LebesgueDyadic lem₁ using (leb-inf)
  open LebesgueInterval lem₁ using (leb-Iv; leb-unique)
  open LebesgueIntervalAlg (lemOf lem₁) using (F; ∫ᴹ-zero′)
  open LebesgueShiftCut (lemOf lem₁) using (diffC; diff-sum)
  open LebesgueShiftAlg (lemOf lem₁) using (Iv-from-F; below-zero; prod-≤; prod-≥; prod-inf; inf-shift; shift-eq; bnd-rat; total)
  open QBS
  open Hom

  -- x ↦ x + t
  shiftH : ∣A∣ → Hom S WQ WQ
  shiftH t = addH idW (constW {WQ} t)

  -- the three summands: the pushforward along `shiftH t`, lebPre on [0,t), and nothing
  fam : ∣A∣ → ℕ → Pre (XW WQ)
  fam t zero = mapM {WQ} {WQ} (shiftH t) lebPre
  fam t (suc zero) = reweightPre {WQ} (χIv 0# t) lebPre
  fam t (suc (suc _)) = scalePre {WQ} 0# lebPre

  -- the measure h ↦ ∫ h(x + t) dx + ∫_{[0,t)} h dx
  shiftedLeb : ∣A∣ → Pre (XW WQ)
  shiftedLeb t = sumPre {WQ} (fam t)

  ∫ᴹ-shiftedLeb : ∀ t (h : Hom S WQ WQ) →
    ∫ᴹ {WQ} (shiftedLeb t) h ≈ ∫ᴹ {WQ} lebPre (_∘H_ S h (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
  ∫ᴹ-shiftedLeb t h = trans (∫ᴹ-sum {WQ} (fam t) h) (trans (∑ᶠ-shift a) (+-cong (∫ᴹ-map {WQ} {WQ} (shiftH t) lebPre h) rest))
    where
      a = λ n → ∫ᴹ {WQ} (fam t n) h
      tail₂ : ∑ᶠ (λ n → a (suc (suc n))) ≈ 0#
      tail₂ = ∑ᶠ-zero (λ n → trans (∫ᴹ-scale {WQ} 0# lebPre h) (zeroˡ _))
      rest : ∑ᶠ (λ n → a (suc n)) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h)
      rest = trans (∑ᶠ-shift (λ n → a (suc n))) (trans (+-cong (∫ᴹ-reweight {WQ} (χIv 0# t) lebPre h) tail₂) (+-identityʳ _))

  -- the mass of [0,b), for t ≤ b: [0,b) = [0,d) + t with t + d = b
  F-above : ∀ t → Bnd t → ∀ b → Bnd b → (tb : t ≤ b) →
    ∫ᴹ {WQ} lebPre (_∘H_ S (χIv 0# b) (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (χIv 0# b)) ≈ b
  F-above t bt b bb tb = trans (+-cong first second) (trans (+-comm _ _) (diff-sum t b tb (proj₁ M) (proj₂ M)))
    where
      M = bnd-rat t bt
      d = diffC t b tb
      bd : Bnd d
      bd = proj₁ bb , ≤-trans (≤-trans (≤-+ʳ {d} {t}) (≤-reflexive (+-comm d t)))
             (≤-trans (proj₁ (diff-sum t b tb (proj₁ M) (proj₂ M))) (proj₂ bb))
      first : ∫ᴹ {WQ} lebPre (_∘H_ S (χIv 0# b) (shiftH t)) ≈ d
      first = trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S (χIv 0# b) (shiftH t)} {χIv 0# d} (shift-eq t b tb bt))
        (trans (sym (+-identityˡ _)) (leb-Iv 0# d 0-least bd))
      second : ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (χIv 0# b)) ≈ t
      second = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# t) (χIv 0# b)} {χIv 0# t} (λ x → prod-≥ b t x tb))
        (trans (sym (+-identityˡ _)) (leb-Iv 0# t 0-least bt))

  -- for b ≤ t: the translated part vanishes
  F-below : ∀ t → Bnd t → ∀ b → Bnd b → b ≤ t →
    ∫ᴹ {WQ} lebPre (_∘H_ S (χIv 0# b) (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (χIv 0# b)) ≈ b
  F-below t bt b bb bt′ = trans (+-cong first second) (+-identityˡ _)
    where
      first : ∫ᴹ {WQ} lebPre (_∘H_ S (χIv 0# b) (shiftH t)) ≈ 0#
      first = ∫ᴹ-zero′ lebPre (_∘H_ S (χIv 0# b) (shiftH t)) (λ x → below-zero b t x bt′)
      second : ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) (χIv 0# b)) ≈ b
      second = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (χIv 0# t) (χIv 0# b)} {χIv 0# b} (λ x → prod-≤ b t x bt′))
        (trans (sym (+-identityˡ _)) (leb-Iv 0# b 0-least bb))

  shifted-F : ∀ t → Bnd t → ∀ b → Bnd b → F (shiftedLeb t) b ≈ b
  shifted-F t bt b bb = trans (∫ᴹ-shiftedLeb t (χIv 0# b))
    ([ F-above t bt b bb , F-below t bt b bb ]′ (total t b))

  shifted-Iv : ∀ t → Bnd t → ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} (shiftedLeb t) (χIv a b) ≈ b
  shifted-Iv t bt = Iv-from-F (shiftedLeb t) (shifted-F t bt)

  ∫-shift : ∀ t → Bnd t → ∀ (h : Hom S WQ WQ) →
    ∫ᴹ {WQ} lebPre (_∘H_ S h (shiftH t)) + ∫ᴹ {WQ} lebPre (mulH {WQ} (χIv 0# t) h) ≈ ∫ᴹ {WQ} lebPre h
  ∫-shift t bt h = trans (sym (∫ᴹ-shiftedLeb t h)) (leb-unique (shiftedLeb t) (shifted-Iv t bt) inf-zero h)
    where
      inf-zero : ∫ᴹ {WQ} (shiftedLeb t) χInf ≈ 0#
      inf-zero = trans (∫ᴹ-shiftedLeb t χInf) (trans
        (+-cong (trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S χInf (shiftH t)} {χInf} (inf-shift t bt)) leb-inf)
                (∫ᴹ-zero′ lebPre (mulH {WQ} (χIv 0# t) χInf) (prod-inf t bt))) (+-identityˡ 0#))
