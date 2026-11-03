{-# OPTIONS --safe --without-K #-}

-- Scaling of Lebesgue measure on [0,∞) by every finite positive constant (plan 03, "Uniqueness on the half-line").
-- For c with an inverse c′ (both finite) and every test h,
--   `∫-scale : c · ∫ h(cx) dx ≈ ∫ h dx`.
-- Route: `scaledLeb c`, the measure h ↦ c · ∫ h(cx) dx, gives [a,b) the mass c · (b c′ − a c′) = b − a
-- (`scaled-Iv`, from `LebesgueInterval.leb-Iv` at the endpoints a c′, b c′), and nothing to ∞, so it is Lebesgue measure
-- (`LebesgueInterval.leb-unique`).  This generalises the dyadic `Continuous/HalfLineScale`.
module QBS.Continuous.LebesgueScale where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueScaleAlg using (module LebesgueScaleAlg)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)

module LebesgueScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open OmegaSemiring A using (refl; sym; trans; *-cong; +-cong; *-comm; *-mono; distribˡ; zeroʳ; ≤-trans; ≤-reflexive)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-cong; mapM; ∫ᴹ-map; module C)
  open C using (Pre)
  open SFiniteSum (lemOf lem₁) using (scalePre; ∫ᴹ-scale)
  open LebesgueInterval lem₁ using (leb-Iv; leb-unique)
  open LebesgueDyadic lem₁ using (leb-inf)
  open LebesgueScaleAlg (lemOf lem₁) using (χIv-scale; χInf-scale; cancelˡ)
  open Bounded A using (finite)
  open HalfLine lem₁ using (lebPre)
  open HalfLineRate lem₁ using (scaleH)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χIv; χInf)
  open QBS
  open Hom

  -- the measure h ↦ c · ∫ h(cx) dx
  scaledLeb : ∣A∣ → Pre (XW WQ)
  scaledLeb c = scalePre {WQ} c (mapM {WQ} {WQ} (scaleH c idW) lebPre)

  ∫ᴹ-scaledLeb : ∀ c (h : Hom S WQ WQ) → ∫ᴹ {WQ} (scaledLeb c) h ≈ c * ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH c idW))
  ∫ᴹ-scaledLeb c h = trans (∫ᴹ-scale {WQ} c (mapM {WQ} {WQ} (scaleH c idW) lebPre) h)
    (*-cong refl (∫ᴹ-map {WQ} {WQ} (scaleH c idW) lebPre h))

  scaled-Iv : ∀ c c′ → c * c′ ≈ 1# → Bnd c → Bnd c′ → ∀ a b → a ≤ b → Bnd b →
    a + ∫ᴹ {WQ} (scaledLeb c) (χIv a b) ≈ b
  scaled-Iv c c′ e bc bc′ a b a≤b bb = trans (+-cong (sym ca) (trans (∫ᴹ-scaledLeb c (χIv a b)) (*-cong refl tl)))
    (trans (sym (distribˡ c (a * c′) L)) (trans (*-cong refl (leb-Iv (a * c′) (b * c′) le (SubSemiring.Is-* finite bb bc′))) cb))
    where
    e′ : c′ * c ≈ 1#
    e′ = trans (*-comm c′ c) e
    L : ∣A∣
    L = ∫ᴹ {WQ} lebPre (χIv (a * c′) (b * c′))
    ca : c * (a * c′) ≈ a
    ca = trans (*-cong refl (*-comm a c′)) (cancelˡ c′ c a e′)
    cb : c * (b * c′) ≈ b
    cb = trans (*-cong refl (*-comm b c′)) (cancelˡ c′ c b e′)
    le : a * c′ ≤ b * c′
    le = ≤-trans (≤-reflexive (*-comm a c′)) (≤-trans (*-mono c′ a≤b) (≤-reflexive (*-comm c′ b)))
    tl : ∫ᴹ {WQ} lebPre (_∘H_ S (χIv a b) (scaleH c idW)) ≈ L
    tl = ∫ᴹ-cong {WQ} lebPre {_∘H_ S (χIv a b) (scaleH c idW)} {χIv (a * c′) (b * c′)} (λ x → χIv-scale c c′ a b x e)

  ∫-scale : ∀ c c′ → c * c′ ≈ 1# → Bnd c → Bnd c′ → ∀ (h : Hom S WQ WQ) →
    c * ∫ᴹ {WQ} lebPre (_∘H_ S h (scaleH c idW)) ≈ ∫ᴹ {WQ} lebPre h
  ∫-scale c c′ e bc bc′ h = trans (sym (∫ᴹ-scaledLeb c h)) (leb-unique (scaledLeb c) (scaled-Iv c c′ e bc bc′) inf h)
    where
    inf : ∫ᴹ {WQ} (scaledLeb c) χInf ≈ 0#
    inf = trans (∫ᴹ-scaledLeb c χInf) (trans (*-cong refl (trans
      (∫ᴹ-cong {WQ} lebPre {_∘H_ S χInf (scaleH c idW)} {χInf} (λ x → χInf-scale c c′ x e bc bc′)) leb-inf)) (zeroʳ c))
