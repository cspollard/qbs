{-# OPTIONS --safe --without-K #-}

-- Monotone change of variables on the half-line with a derivative certificate (plan 03, "Change of variables").
-- Data: an increasing bijection φ of [0,∞] with inverse ψ (both morphisms; `gc-to`, `gc-from`: a ≤ ψ y ↔ φ a ≤ y, and
-- `φψ : φ (ψ y) ≈ y`), ψ finite on finite points, and a derivative φ′ with `dv : ∀ N → Deriv (N+1) φ 0 φ′`.  Then
--   `cov : ∫ g(φ x) φ′(x) dx ≈ ∫ g(y) dy`   for every test g,
-- and `cov-inv : ∫ h(ψ y) dy ≈ ∫ h(x) φ′(x) dx`.  Route: the pushforward `lebψ = mapM ψ lebPre` and the reweighted
-- `lebφ′ = reweightPre φ′ lebPre` are equal (`push-eq`, `UniquenessWQ.uniqWQ`):
--   * on a dyadic interval [d, d′): lebψ gives it φ d′ − φ d (`χIv-ψ`, then `LebesgueInterval.leb-Iv` at φ d ≤ φ d′), and
--     so does lebφ′ (`FTCDyadic.ftc-dy` with h = 0); cancel the finite φ d (`agreeI`);
--   * lebψ is finite on [k, k+1) (`finI`), and neither measure charges ∞ (`χInf-ψ`, `LebesgueDyadic.leb-inf`).
-- No interval FTC at non-dyadic points is needed: the arbitrary endpoints φ d are handled by `leb-Iv`.
--   Skeleton: holes first.
module QBS.Continuous.ChangeOfVariables where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.FTCDyadic using (module FTCDyadic)

module ChangeOfVariables (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd)
  open AlgD A R using (Deriv)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (χIv; χInf; χI; dy)
  open FTCDyadic lem₁ using (ftc-dy)
  open QBS
  open Hom

  module _ (φ ψ φ′ : Hom S WQ WQ)
           (dv : ∀ N → Deriv (natE (suc N)) (λ x → map φ ⟨$⟩ x) (λ _ → 0#) (λ x → map φ′ ⟨$⟩ x))
           (gc-to : ∀ a y → a ≤ map ψ ⟨$⟩ y → map φ ⟨$⟩ a ≤ y)
           (gc-from : ∀ a y → map φ ⟨$⟩ a ≤ y → a ≤ map ψ ⟨$⟩ y)
           (φψ : ∀ y → map φ ⟨$⟩ (map ψ ⟨$⟩ y) ≈ y)
           (ψ-fin : ∀ y → Bnd y → Bnd (map ψ ⟨$⟩ y)) where

    Φ : ∣A∣ → ∣A∣
    Φ x = map φ ⟨$⟩ x

    -- φ is monotone, sends 0 to 0 and finite points to finite points
    Φ-mono : ∀ a b → a ≤ b → Φ a ≤ Φ b
    Φ-mono = ?

    Φ-zero : Φ 0# ≈ 0#
    Φ-zero = ?

    Φ-fin : ∀ a → Bnd a → Bnd (Φ a)
    Φ-fin = ?

    -- ψ pulls intervals back to intervals, and ∞ back to ∞
    χIv-ψ : ∀ a b y → map (χIv a b) ⟨$⟩ (map ψ ⟨$⟩ y) ≈ map (χIv (Φ a) (Φ b)) ⟨$⟩ y
    χIv-ψ = ?

    χInf-ψ : ∀ y → map χInf ⟨$⟩ (map ψ ⟨$⟩ y) ≈ map χInf ⟨$⟩ y
    χInf-ψ = ?

    -- the two measures on the source side
    lebψ : Pre (XW WQ)
    lebψ = mapM {WQ} {WQ} ψ lebPre

    lebφ′ : Pre (XW WQ)
    lebφ′ = reweightPre {WQ} φ′ lebPre

    -- interval masses
    massψ : ∀ a b → a ≤ b → Bnd b → Φ a + ∫ᴹ {WQ} lebψ (χIv a b) ≈ Φ b
    massψ = ?

    massφ′ : ∀ n m → Φ (dy n m) + ∫ᴹ {WQ} lebφ′ (χI n m) ≈ Φ (dy n (suc m))
    massφ′ = ?

    -- the hypotheses of `uniqWQ`
    agreeI : ∀ n m → ∫ᴹ {WQ} lebψ (χI n m) ≈ ∫ᴹ {WQ} lebφ′ (χI n m)
    agreeI = ?

    finI : ∀ k → Bnd (∫ᴹ {WQ} lebψ (χI 0 k))
    finI = ?

    inf-ψ : ∫ᴹ {WQ} lebψ χInf ≈ 0#
    inf-ψ = ?

    inf-φ′ : ∫ᴹ {WQ} lebφ′ χInf ≈ 0#
    inf-φ′ = ?

    push-eq : _≈ᴹ_ {WQ} lebψ lebφ′
    push-eq = ?

    -- the change of variables, both ways round
    cov-inv : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h ψ) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} φ′ h)
    cov-inv = ?

    cov : ∀ (g : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} φ′ (_∘H_ S g φ)) ≈ ∫ᴹ {WQ} lebPre g
    cov = ?
