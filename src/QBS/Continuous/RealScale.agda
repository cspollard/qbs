{-# OPTIONS --safe --without-K #-}

-- Scaling and reflection of the whole real line `RQ = WQ +Q WQ` (plan 03, "Tests and the real line").
--   * `scaleRH c : RQ ⇒ RQ`, x ↦ c x on each summand (`[inl ∘ (c ·) , inr ∘ (c ·)]`), and `reflRH = [inr , inl]`, x ↦ −x;
--   * `∫-scaleR : c ∫ h(c x) dx ≈ ∫ h`  for finite c, c′ with c c′ ≈ 1 (`LebesgueScale.∫-scale` on each half);
--   * `∫-reflR : ∫ h(−x) dx ≈ ∫ h` (the halves swap, `+-comm`).
-- Route: `RealLine.∫ᴹ-lebR` splits both sides; `h ∘ scaleRH c ∘ inl` is `(h ∘ inl) ∘ (c ·)` pointwise (`copair` computes
-- on `inl`), and the same on `inr`.
module QBS.Continuous.RealScale where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Colimits using (copair)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.LebesgueScale using (module LebesgueScale)

module RealScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; sym; trans; +-cong; *-cong; +-comm; distribˡ)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLineRate lem₁ using (scaleH)
  open LebesgueScale lem₁ using (∫-scale)
  open ExpDist lem₁ using (idW)
  open RealLine lem₁ using (RQ; inlH; inrH; lebR; ∫ᴹ-lebR)
  open QBS
  open Hom

  -- x ↦ c x and x ↦ −x
  scaleRH : ∣A∣ → Hom S RQ RQ
  scaleRH c = copair S (_∘H_ S inlH (scaleH c idW)) (_∘H_ S inrH (scaleH c idW))

  reflRH : Hom S RQ RQ
  reflRH = copair S inrH inlH

  open HalfLine lem₁ using (lebPre)

  -- the two halves of `h ∘ scaleRH c`, and of `h ∘ reflRH`, are pointwise the expected maps
  scl : ∀ c (h : Hom S RQ WQ) → let g = _∘H_ S h (scaleRH c) in
    ∫ᴹ {WQ} lebPre (_∘H_ S g inlH) ≈ ∫ᴹ {WQ} lebPre (_∘H_ S (_∘H_ S h inlH) (scaleH c idW)) ×
    ∫ᴹ {WQ} lebPre (_∘H_ S g inrH) ≈ ∫ᴹ {WQ} lebPre (_∘H_ S (_∘H_ S h inrH) (scaleH c idW))
  scl c h = ∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S h (scaleRH c)) inlH}
              {_∘H_ S (_∘H_ S h inlH) (scaleH c idW)} (λ x → refl) ,
            ∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S h (scaleRH c)) inrH}
              {_∘H_ S (_∘H_ S h inrH) (scaleH c idW)} (λ x → refl)

  ∫-scaleR : ∀ c c′ → c * c′ ≈ 1# → Bnd c → Bnd c′ → ∀ (h : Hom S RQ WQ) →
    c * ∫ᴹ {RQ} lebR (_∘H_ S h (scaleRH c)) ≈ ∫ᴹ {RQ} lebR h
  ∫-scaleR c c′ e bc bc′ h = trans (*-cong refl (∫ᴹ-lebR (_∘H_ S h (scaleRH c)))) (trans (distribˡ c _ _)
    (trans (+-cong (trans (*-cong refl (proj₁ (scl c h))) (∫-scale c c′ e bc bc′ (_∘H_ S h inlH)))
                   (trans (*-cong refl (proj₂ (scl c h))) (∫-scale c c′ e bc bc′ (_∘H_ S h inrH))))
           (sym (∫ᴹ-lebR h))))

  ∫-reflR : ∀ (h : Hom S RQ WQ) → ∫ᴹ {RQ} lebR (_∘H_ S h reflRH) ≈ ∫ᴹ {RQ} lebR h
  ∫-reflR h = trans (∫ᴹ-lebR (_∘H_ S h reflRH)) (trans (+-cong
    (∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S h reflRH) inlH} {_∘H_ S h inrH} (λ x → refl))
    (∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S h reflRH) inrH} {_∘H_ S h inlH} (λ x → refl)))
    (trans (+-comm _ _) (sym (∫ᴹ-lebR h))))
