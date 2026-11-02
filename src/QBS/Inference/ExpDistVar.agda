{-# OPTIONS --safe --without-K #-}

-- The second moment and the variance of the exponential distribution through the expectation API of
-- `Inference/ExpectationInt` (continuing `Inference/ExpDistMean`).
-- The squaring statistic (`pos = x ↦ x²`, `neg = 0`) is an integrable test `sqI : ITest expDist`, as
-- `∫ᴹ (ιPre expDist) sq ≈ 1 + 1` (`Continuous/ExpDistSq`).  Hence `E-atᴵ-sqI : E-atᴵ expDist sqI ≃ 2` and, with the mean
-- `E-atᴵ expDist idI ≃ 1`, the variance `E[X²] − (E X)² ≃ 1`:
--   `var-expDist : E-atᴵ expDist sqI +S (-S (E-atᴵ expDist idI *S E-atᴵ expDist idI)) ≃ 1`.
-- The variance of `Analysis/Variance` (`Var f = E[f²] − (E f)²`) is stated for bounded `SF` and does not apply to the unbounded
-- exponential, so the difference is stated directly as a signed value (`Sg`).
module QBS.Inference.ExpDistVar where

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
open import QBS.Inference.ExpDistMean using (module ExpDistMean)
import QBS.Inference.ExpectationInt as EI

module ExpDistVar (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-identityˡ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; ≃-trans; _+S_; _*S_; -S_; +S-cong; -S-cong; *S-cong; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (ψ; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open ExpDist lem₁ using (expDist)
  open ExpDistSq lem₁ using (sqW; ∫-expDist-sq)
  open ExpDistMean lem₁ using (idI; E-atᴵ-idI; zeroC; J-neg)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)
    using (solve; _:+_; _:*_; _:=_; con)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open Hom

  -- the squaring statistic as a `CutQ`-valued test
  sqC : Hom S WQ CutQ
  sqC = record { map = map sqW ; map-random = λ {γ} mγ → map-random sqW {γ} mγ }

  -- the pulled-back integral of the positive part
  J-pos-sq : J (m expDist) (λ r → map sqC ⟨$⟩ (α expDist ⟨$⟩ r)) (map-random sqC {α expDist} (α-random expDist)) ≈ 1# + 1#
  J-pos-sq = trans (J-cong (m expDist) {λ r → map sqC ⟨$⟩ (α expDist ⟨$⟩ r)} {ψ {WQ} (ιPre {WQ} expDist) sqW}
    (map-random sqC {α expDist} (α-random expDist)) (mψ {WQ} (ιPre {WQ} expDist) sqW) (λ r → sym (*-identityˡ _))) ∫-expDist-sq

  two-fin : Bnd (1# + 1#)
  two-fin = Is-+ finite (Is-1 finite) (Is-1 finite)

  -- the squaring statistic is integrable
  sqI : ITest expDist
  sqI = record
    { pos = sqC ; neg = zeroC
    ; pos-int = Is-resp finite (sym J-pos-sq) two-fin
    ; neg-int = Is-resp finite (sym J-neg) (Is-0 finite) }

  -- the second moment: `E-atᴵ expDist sqI ≃ 2`
  E-atᴵ-sqI : E-atᴵ expDist sqI ≃ ((1# + 1#) − 0# [ two-fin , Is-0 finite ])
  E-atᴵ-sqI = mk≃ 0# (Is-0 finite)
    (trans (+-cong (+-cong J-pos-sq refl) refl) (sym (+-cong (+-cong refl J-neg) refl)))

  -- `2 − 1 = 1` at the level of signed values: the arithmetic of the variance
  var-arith : (((1# + 1#) − 0# [ two-fin , Is-0 finite ]) +S
      (-S ((1# − 0# [ Is-1 finite , Is-0 finite ]) *S (1# − 0# [ Is-1 finite , Is-0 finite ]))))
    ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-arith = mk≃ 0# (Is-0 finite) (solve 0 (((con 1 :+ con 1) :+ (con 1 :* con 0 :+ con 0 :* con 1)) :+ con 0 :+ con 0
    := (con 1 :+ (con 0 :+ (con 1 :* con 1 :+ con 0 :* con 0))) :+ con 0) refl)

  -- the variance: `E[X²] − (E X)² ≃ 1`
  var-expDist : (E-atᴵ expDist sqI +S (-S (E-atᴵ expDist idI *S E-atᴵ expDist idI))) ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-expDist = ≃-trans (+S-cong E-atᴵ-sqI (-S-cong (*S-cong E-atᴵ-idI E-atᴵ-idI))) var-arith
