{-# OPTIONS --safe --without-K #-}

-- Scaled symmetric distributions on the real line, and N(0, s²) (plan 03, "Tests and the real line").
-- For s, l finite with s l ≈ 1 (l = 1/s):
--   * `push-sym`: the pushforward of `RealDensity.Sym.symDist d` along x ↦ s x (`RealScale.scaleRH s`) integrates every
--     test like the symmetric distribution with the scaled density `scD d = y ↦ l d(l y)` (`ScaleDensity.scD`), with the
--     same mass c (`scD-int`) and normaliser n;
--   * `gaussσ = mapPre (scaleRH s) gaussR`, the Gaussian of standard deviation s, with its density form (`gauss-dens`)
--     and second moment `second : ∫ x² dN(0, s²) ≈ s²`.
-- Route for `push-sym`: `SFiniteIncl.ι-nat` and `SFinite.∫ᴹ-map` move the scaling into the test, `Sym.∫-sym` gives two
-- half-line integrals, and on each half ∫ d(x) f(s x) dx = s ∫ l d(l s x) f(s x) dx = ∫ l d(l y) f(y) dy
-- (`LebesgueScale.∫-scale`, as in `ScaleDensity.push-dens`).  `second`: x² ∘ (s ·) = s² x² and `GaussReal.sqint`.
--   Skeleton: holes first.
module QBS.Inference.GaussScale where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealDensity using (module RealDensity)
open import QBS.Continuous.RealScale using (module RealScale)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Inference.ScaleDensity using (module ScaleDensity)
open import QBS.Inference.GaussReal using (module GaussReal)

module GaussScale (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH)
  open RealDensity lem₁ using (module Sym)
  open RealScale lem₁ using (scaleRH)
  open GaussHalfLine lem₁ using (phiH)
  open ScaleDensity lem₁ using (scD)
  open GaussReal lem₁ using (gaussR; n′; Q2)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  module _ (s l : ∣A∣) (sl : s * l ≈ 1#) (sB : Bnd s) (lB : Bnd l) where

    -- the density y ↦ l d(l y) of the scaled variable
    scDs : Hom S WQ WQ → Hom S WQ WQ
    scDs = scD s l sl sB lB

    scD-int : ∀ (d : Hom S WQ WQ) c → ∫ᴹ {WQ} lebPre d ≈ c → ∫ᴹ {WQ} lebPre (scDs d) ≈ c
    scD-int = ?

    push-sym : ∀ (d : Hom S WQ WQ) c (hc : ∫ᴹ {WQ} lebPre d ≈ c) n (nn : (c + c) * n ≈ 1#) (f : Hom S RQ WQ) →
      ∫ᴹ {RQ} (ιPre {RQ} (C.mapPre {RQ} {RQ} (scaleRH s) (Sym.symDist d c hc n nn))) f
        ≈ ∫ᴹ {RQ} (ιPre {RQ} (Sym.symDist (scDs d) c (scD-int d c hc) n nn)) f
    push-sym = ?

    -- the Gaussian with standard deviation s
    gaussσ : Pre RQ
    gaussσ = C.mapPre {RQ} {RQ} (scaleRH s) gaussR

    gauss-dens : ∀ (f : Hom S RQ WQ) → ∫ᴹ {RQ} (ιPre {RQ} gaussσ) f
      ≈ n′ * (∫ᴹ {WQ} lebPre (mulH {WQ} (scDs phiH) (_∘H_ S f inlH))
            + ∫ᴹ {WQ} lebPre (mulH {WQ} (scDs phiH) (_∘H_ S f inrH)))
    gauss-dens = ?

    second : ∫ᴹ {RQ} (ιPre {RQ} gaussσ) Q2 ≈ s * s
    second = ?
