{-# OPTIONS --safe --without-K #-}

-- The fundamental theorem of calculus on every dyadic interval, from `Deriv` data (plan 03, "Change of variables").
-- For G : [0,∞) → [0,∞) and tests h, k with `dv : ∀ N → Deriv (N+1) G h k` (G′ = k − h on every [0, N+1]),
--   `ftc-dy : ∫_{[m/2ⁿ,(m+1)/2ⁿ)} h + G((m+1)/2ⁿ) ≈ G(m/2ⁿ) + ∫_{[m/2ⁿ,(m+1)/2ⁿ)} k`.
-- Route: the rescaled data Gₙ(t) = G(t/2ⁿ), hₙ(t) = h(t/2ⁿ)/2ⁿ, kₙ(t) = k(t/2ⁿ)/2ⁿ satisfy `Deriv (N+1)` too (`dv-resc`,
-- from `Analysis/Deriv.DFaff` with slope ½ⁿ ≤ 1), so `DerivBridge.OnHalfLine.unit m` gives the identity on the unit
-- piece [m, m+1) of Gₙ, in the fair-coin form `J (hₙ ∘ shiftPt m)`.  `piece` turns that into a Lebesgue integral against
-- `χ[m, m+1)` (the only null set is the all-true point, `LebesgueDyadic.fair-top`), and `resc` moves it back to
-- `χ[m/2ⁿ, (m+1)/2ⁿ)` (`LebesgueScale.∫-scale` at c = 2ⁿ, `LebesgueScaleAlg.χIv-scale`).
--   Skeleton: holes first.
module QBS.Continuous.FTCDyadic where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc; _^_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.DerivBridge using (module DerivBridge)

module FTCDyadic (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open Exp A using (natE)
  open AlgD A R using (Deriv)
  open Lebesgue (lemOf lem₁) using (J)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift)
  open HalfLineRate lem₁ using (scaleH)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χI; dy)
  open DerivBridge lem₁ using (module OnHalfLine)
  open QBS
  open Hom

  -- ½ⁿ and its inverse 2ⁿ
  hp-inv : ∀ n → natE (2 ^ n) * hp n ≈ 1#
  hp-inv = ?

  -- the dyadic point m/2ⁿ of `Intervals`, as ½ⁿ · m
  hp-dy : ∀ n m → hp n * natE m ≈ dy n m
  hp-dy = ?

  -- the rescaled test t ↦ ½ⁿ f(½ⁿ t)
  rescH : ℕ → Hom S WQ WQ → Hom S WQ WQ
  rescH n f = scaleH (hp n) (_∘H_ S f (scaleH (hp n) idW))

  -- the unit piece [j, j+1) of the half-line as a fair-coin integral (the all-true point is null)
  piece : ∀ (f : Hom S WQ WQ) j →
    ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI 0 j)) ≈ J fairCoin (λ r → map f ⟨$⟩ shiftPt j r) (Meas-hshift j f)
  piece = ?

  -- rescaling [j, j+1) to [j/2ⁿ, (j+1)/2ⁿ)
  resc : ∀ (f : Hom S WQ WQ) n j → ∫ᴹ {WQ} lebPre (mulH {WQ} (rescH n f) (χI 0 j)) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI n j))
  resc = ?

  module _ (G : ∣A∣ → ∣A∣) (h k : Hom S WQ WQ)
           (dv : ∀ N → Deriv (natE (suc N)) G (λ x → map h ⟨$⟩ x) (λ x → map k ⟨$⟩ x)) where

    -- the data of G(t/2ⁿ)
    dv-resc : ∀ n N → Deriv (natE (suc N)) (λ t → G (hp n * t)) (λ x → map (rescH n h) ⟨$⟩ x) (λ x → map (rescH n k) ⟨$⟩ x)
    dv-resc = ?

    -- the FTC on [m/2ⁿ, (m+1)/2ⁿ)
    ftc-dy : ∀ n m → ∫ᴹ {WQ} lebPre (mulH {WQ} h (χI n m)) + G (dy n (suc m))
      ≈ G (dy n m) + ∫ᴹ {WQ} lebPre (mulH {WQ} k (χI n m))
    ftc-dy = ?
