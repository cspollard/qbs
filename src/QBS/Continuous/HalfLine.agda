{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure on [0,∞) as an s-finite measure: the countable sum of the unit intervals shifted
-- to n, `λ = ∑ₙ (n + U)` with `U` uniform on [0,1] (`Continuous/Uniform`).
--   * `shiftPre n` is the measure on the weight space `WQ = [0,∞]` with probe `r ↦ (1, n + expansion r)`
--     over the fair coin, and `lebPre = sumPre shiftPre` (`Continuous/SFiniteSum`);
--   * `∫ᴹ-shift`: `∫ h d(n + U) = J fairCoin (r ↦ h (n + expansion r))`;
--   * `∫ᴹ-leb`: `∫ h dλ ≈ ∑ᶠ n. J fairCoin (r ↦ h (n + expansion r))` for every measurable
--     `h : WQ ⇒ WQ` (an unbounded `[0,∞]`-valued test), the decomposition of the integral over [0,∞)
--     into the unit-interval integrals of the shifted test.
-- The coordinate test is the identity of `WQ`; no subtraction or division is needed.
module QBS.Continuous.HalfLine where

open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Source using (R₁)
open import QBS.Limits using (_×Q_)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)

module HalfLine (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; trans; sym; *-identityˡ; +-cong)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-cong)
  open Meas (lemOf lem₁) using (Meas; Meas-⊕; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh using (expansion; Fun-expansion)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ψ; mψ; module C)
  open SFiniteSum (lemOf lem₁) using (sumPre; ∫ᴹ-sum)
  open C using (Pre; mk)
  open Daniell lem₁ using (L-one)
  open RandomSource S using (Rˢ)
  open QBS
  open Hom

  -- the shifted unit interval `n + U` (a probability measure on [n,n+1])
  shiftPt : ℕ → R₁ → ∣ WQ ∣
  shiftPt n r = natE n + expansion r

  Meas-shift : ∀ n → Meas (shiftPt n)
  Meas-shift n = Meas-⊕ {λ _ → natE n} {expansion} (Meas-const (natE n)) (LS Fun-expansion)

  shiftF : ℕ → Func Rˢ (Carrier WQ)
  shiftF n = record
    { to = shiftPt n
    ; cong = λ e → +-cong refl (Measurable.Fun-resp A (lemOf lem₁) Fun-expansion (lower e)) }

  shiftProbe : ℕ → Func Rˢ (Carrier (XW WQ))
  shiftProbe n = record { to = λ r → 1# , shiftPt n r ; cong = λ e → refl , Func.cong (shiftF n) e }

  shiftPre : ℕ → Pre (XW WQ)
  shiftPre n = mk (shiftProbe n) (Meas-const 1# , Meas-shift n) fairCoin L-one

  -- Lebesgue measure on [0,∞)
  lebPre : Pre (XW WQ)
  lebPre = sumPre {WQ} shiftPre

  -- the integral of a test `h : [0,∞] ⇒ [0,∞]` against `n + U`
  Meas-hshift : ∀ n (h : Hom S WQ WQ) → Meas (λ r → map h ⟨$⟩ shiftPt n r)
  Meas-hshift n h = map-random h {shiftF n} (Meas-shift n)

  ∫ᴹ-shift : ∀ n (h : Hom S WQ WQ) → ∫ᴹ {WQ} (shiftPre n) h ≈ J fairCoin (λ r → map h ⟨$⟩ shiftPt n r) (Meas-hshift n h)
  ∫ᴹ-shift n h = J-cong fairCoin (mψ {WQ} (shiftPre n) h) (Meas-hshift n h) (λ r → *-identityˡ (map h ⟨$⟩ shiftPt n r))

  -- the decomposition of the integral over [0,∞) into unit intervals
  ∫ᴹ-leb : ∀ (h : Hom S WQ WQ) →
    ∫ᴹ {WQ} lebPre h ≈ ∑ᶠ (λ n → J fairCoin (λ r → map h ⟨$⟩ shiftPt n r) (Meas-hshift n h))
  ∫ᴹ-leb h = trans (∫ᴹ-sum {WQ} shiftPre h) (∑ᶠ-cong (λ n → ∫ᴹ-shift n h))
