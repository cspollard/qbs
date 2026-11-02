{-# OPTIONS --safe --without-K #-}

-- The whole real line as two half-lines, `RQ = WQ +Q WQ` (a QBS coproduct): `inl x` stands for `+x` and `inr x` for `−x`
-- (zero appears twice, which is harmless: it has measure zero), and Lebesgue measure on it.
--   * `inlH inrH : WQ ⇒ RQ` and `copairH d e : RQ ⇒ WQ` (`[d , e]`, computing as `d` on `inl x` and `e` on `inr x`);
--   * `lebR : Pre (XW RQ)`, `sumPre` of `mapM inlH lebPre`, `mapM inrH lebPre` and (to fill the ℕ-indexed family) zero measures;
--   * `∫ᴹ-lebR f : ∫ᴹ lebR f ≈ ∫ᴹ lebPre (f ∘ inl) + ∫ᴹ lebPre (f ∘ inr)`.
module QBS.Continuous.RealLine where

open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Colimits using (_+Q_; copair; coproduct)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Series using (module Series)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import Categories.Object.Coproduct using (Coproduct)

module RealLine (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; 0#; refl; sym; trans; +-cong; +-identityʳ; zeroˡ)
  open Series A using (∑ᶠ; ∑ᶠ-shift; ∑ᶠ-zero)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; mapM; ∫ᴹ-map; module C)
  open SFiniteSum (lemOf lem₁) using (sumPre; ∫ᴹ-sum; scalePre; ∫ᴹ-scale)
  open HalfLine lem₁ using (lebPre)

  RQ : QBS S
  RQ = _+Q_ S WQ WQ

  inlH inrH : Hom S WQ RQ
  inlH = Coproduct.i₁ (coproduct S {WQ} {WQ})
  inrH = Coproduct.i₂ (coproduct S {WQ} {WQ})

  copairH : Hom S WQ WQ → Hom S WQ WQ → Hom S RQ WQ
  copairH d e = copair S d e

  -- the two halves, and the zero measures filling the rest of the family
  tsR : ℕ → C.Pre (XW RQ)
  tsR zero = mapM {WQ} {RQ} inlH lebPre
  tsR (suc zero) = mapM {WQ} {RQ} inrH lebPre
  tsR (suc (suc n)) = scalePre {RQ} 0# (mapM {WQ} {RQ} inlH lebPre)

  lebR : C.Pre (XW RQ)
  lebR = sumPre {RQ} tsR

  tsR-zero : ∀ n (f : Hom S RQ WQ) → ∫ᴹ {RQ} (tsR (suc (suc n))) f ≈ 0#
  tsR-zero n f = trans (∫ᴹ-scale {RQ} 0# (mapM {WQ} {RQ} inlH lebPre) f) (zeroˡ _)

  sum-two : ∀ a → (∀ n → a (suc (suc n)) ≈ 0#) → ∑ᶠ a ≈ a 0 + a 1
  sum-two a z = trans (∑ᶠ-shift a) (+-cong refl (trans (∑ᶠ-shift (λ n → a (suc n)))
    (trans (+-cong refl (∑ᶠ-zero {λ n → a (suc (suc n))} z)) (+-identityʳ (a 1)))))

  ∫ᴹ-lebR : ∀ (f : Hom S RQ WQ) →
    ∫ᴹ {RQ} lebR f ≈ ∫ᴹ {WQ} lebPre (_∘H_ S f inlH) + ∫ᴹ {WQ} lebPre (_∘H_ S f inrH)
  ∫ᴹ-lebR f = trans (∫ᴹ-sum {RQ} tsR f) (trans (sum-two (λ n → ∫ᴹ {RQ} (tsR n) f) (λ n → tsR-zero n f))
    (+-cong (∫ᴹ-map {WQ} {RQ} inlH lebPre f) (∫ᴹ-map {WQ} {RQ} inrH lebPre f)))
