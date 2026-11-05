{-# OPTIONS --safe --without-K #-}

-- Every moment of the exponential distribution through the expectation API: `E[Xⁿ] ≃ n!` under `densDist negExpH`.
-- `powD n : ITest (densDist negExpH expNrm)` has parts `xⁿ` and `0`, finite because `∫ xⁿ e^{−x} = n!`
-- (`Continuous/HalfLineMomentFact`); `E-atᴵ-powD n` is `E-atᴵ-dens` rewritten to the value `n! − 0`.  The cases n = 1, 2
-- recover `Inference/DensityExpectation.E-atᴵ-idD` and `E-atᴵ-sqD` (mean 1, second moment 2).
module QBS.Inference.ExpMomentN where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
import QBS.Inference.ExpectationInt as EI

module ExpMomentN (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-comm; +-identityʳ; +-mono; ≤-refl; ≤-reflexive)
  open Exp A using (natE)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_]; ≃-trans)
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+; Is-*)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open DensityDist lem₁ using (densDist)
  open HalfLineMomentN lem₁ using (pwNegExpH; pw-cong; Meas-pw)
  open HalfLineMomentFact lem₁ using (fact; ∫ᴹ-pw-moment)
  open DensityExpectation lem₁ using (E-atᴵ-dens; densI; expNrm; zeroB; zero-integral)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open import QBS.Analysis.PolyExpCert using (module AlgP)
  open AlgP A R using (pw)
  open QBS
  open Hom

  -- the test `x ↦ xⁿ`
  powH : ℕ → Hom S WQ WQ
  powH n = record { map = record { to = pw n ; cong = pw-cong n } ; map-random = λ {γ} m → Meas-pw n {γ ⟨$⟩_} m }

  -- `∫ e^{−x} xⁿ = n!`
  pow-integral : ∀ n → ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (powH n)) ≈ fact n
  pow-integral n = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH (powH n)} {pwNegExpH n} (λ x → *-comm _ _)) (∫ᴹ-pw-moment n)

  natB : ∀ n → Bnd (natE n)
  natB zero = Is-0 finite
  natB (suc n) = Is-+ finite (natB n) (Is-1 finite)

  factB : ∀ n → Bnd (fact n)
  factB zero = Is-1 finite
  factB (suc n) = Is-* finite (natB (suc n)) (factB n)

  powB : ∀ n → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (powH n)))
  powB n = Is-resp finite (sym (pow-integral n)) (factB n)

  powD : ∀ n → ITest (densDist negExpH expNrm)
  powD n = densI negExpH expNrm (powH n) (constW 0#) (powB n) zeroB

  -- E[Xⁿ] ≃ n!
  E-atᴵ-powD : ∀ n → E-atᴵ (densDist negExpH expNrm) (powD n) ≃ (fact n − 0# [ factB n , Is-0 finite ])
  E-atᴵ-powD n = ≃-trans (E-atᴵ-dens negExpH expNrm (powH n) (constW 0#) (powB n) zeroB)
    (mk≃ 0# (Is-0 finite) (+-cong (+-cong (pow-integral n) (sym (zero-integral negExpH expNrm))) refl))
