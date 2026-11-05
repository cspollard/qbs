{-# OPTIONS --safe --without-K #-}

-- The mean of the exponential distribution through the expectation API of `Inference/ExpectationInt`.
-- The identity statistic (`pos = id`, `neg = 0`) is an integrable test `idI : ITest expDist`: its parts have
-- finite integrals `1` and `0`, as `∫ᴹ (ιPre expDist) id ≈ 1` (`Continuous/ExpDist`) and the pulled-back integral
-- `J (m expDist) (id ∘ α expDist)` is that integral (the weight of `ιPre` is `1`).  Hence
-- `E-atᴵ-idI : E-atᴵ expDist idI ≃ 1`, so the general laws (`E-atᴵ-map`, `E-respᴵ`, linearity) apply to the exponential.
module QBS.Inference.ExpDistMean where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
import QBS.Inference.ExpectationInt as EI

module ExpDistMean (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; 0#; 1#; refl; sym; trans; +-cong; *-identityˡ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Meas (lemOf lem₁) using (Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ψ; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open ExpDist lem₁ using (expDist; ∫-expDist-id; idW)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open QBS using (∣_∣)
  open Hom

  -- the identity of `WQ` as a `CutQ`-valued test, and the zero test
  idC zeroC : Hom S WQ CutQ
  idC = record { map = map idW ; map-random = λ {γ} mγ → map-random idW {γ} mγ }
  zeroC = record { map = record { to = λ _ → 0# ; cong = λ _ → refl } ; map-random = λ _ → Meas-const 0# }

  -- the pulled-back integrals
  J-pos : J (m expDist) (λ r → map idC ⟨$⟩ (α expDist ⟨$⟩ r)) (map-random idC {α expDist} (α-random expDist)) ≈ 1#
  J-pos = trans (J-cong (m expDist) {λ r → map idC ⟨$⟩ (α expDist ⟨$⟩ r)} {ψ {WQ} (ιPre {WQ} expDist) idW}
    (map-random idC {α expDist} (α-random expDist)) (mψ {WQ} (ιPre {WQ} expDist) idW) (λ r → sym (*-identityˡ _))) ∫-expDist-id

  J-neg : J (m expDist) (λ r → map zeroC ⟨$⟩ (α expDist ⟨$⟩ r)) (map-random zeroC {α expDist} (α-random expDist)) ≈ 0#
  J-neg = trans (J-irrel (m expDist) (map-random zeroC {α expDist} (α-random expDist)) (Meas-const 0#)) (J-const (ok expDist) 0#)

  -- the identity statistic is integrable
  idI : ITest expDist
  idI = record
    { pos = idC ; neg = zeroC
    ; pos-int = Is-resp finite (sym J-pos) (Is-1 finite)
    ; neg-int = Is-resp finite (sym J-neg) (Is-0 finite) }

  -- the mean: `E-atᴵ expDist idI ≃ 1`
  E-atᴵ-idI : E-atᴵ expDist idI ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  E-atᴵ-idI = mk≃ 0# (Is-0 finite)
    (trans (+-cong (+-cong J-pos refl) refl) (sym (+-cong (+-cong refl J-neg) refl)))
