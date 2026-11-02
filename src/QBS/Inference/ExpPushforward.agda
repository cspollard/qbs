{-# OPTIONS --safe --without-K #-}

-- The exponential distribution with scale `c` as a pushforward of Exp(1), with no new integral (item B of `plans/03`).
-- For any finite `c` (`cB : Bnd c`; no positivity, rationality or reciprocal needed), `expPush c = mapPre (x ↦ c·x) expDist`, where
-- `expDist = densDist negExpH expNrm` and `x ↦ c·x` is `HalfLineRate.scaleH c idW`.  By `Inference/PushforwardExpectation`,
--   * `powPushD n : ITest (expPush c)` with parts `xⁿ` and `0`, built from the composite `x ↦ (c·x)ⁿ` against Exp(1) (finite since
--     `∫ e^{−x} (c·x)ⁿ = cⁿ ∫ xⁿ e^{−x} = cⁿ n!`, from `Continuous/HalfLineMomentFact` and `HalfLineRate.∫-scaleH`);
--   * `E-atᴵ-powPush n : E[Xⁿ] ≃ cⁿ n!` (`pw n c * fact n`);
--   * `mean-push : E[X] ≃ c`, `second-push : E[X²] ≃ 2c²` and `var-push : E[X²] − (E X)² ≃ c²`;
--   * `Rate l lc lB`, for a rate `l` with `l c ≈ 1`: `mean-rate : E[X]·λ ≃ 1` and `var-rate : Var·λ² ≃ 1`, the statements of
--     `Inference/ExpRateDist` for the density `λ e^{−λx}` (`l = 1/c`), here for the pushforward.
module QBS.Inference.ExpPushforward where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.AffineAlg using (module AlgAff)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
open import QBS.Inference.ExpMomentN using (module ExpMomentN)
open import QBS.Inference.PushforwardExpectation using (module PushforwardExpectation)
import QBS.Inference.ExpectationInt as EI

module ExpPushforward (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-assoc; *-identityʳ; +-identityˡ; ≤-trans)
  open OmegaSemiring A using () renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open AlgP A R using (pw; pw-mul; pw-one)
  open NegExp (lemOf lem₁) using (negExp)
  open Bounded A using (Bnd; finite; _≃_; mk≃; ≃-trans; _+S_; _*S_; -S_; ι; *S-congˡ)
  open SubSemiring using (Is-0; Is-1; Is-+; Is-*)
  open AlgAff A using (ι-cong; var-core; moment-two; scale-ι)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open DensityDist lem₁ using (densDist)
  open HalfLineMomentN lem₁ using (pwNegExpH; pw-cong)
  open HalfLineMomentFact lem₁ using (fact; fact-1; ∫ᴹ-pw-moment)
  open HalfLineRate lem₁ using (scaleH; ∫-scaleH)
  open ExpDist lem₁ using (idW)
  open DensityExpectation lem₁ using (toC; E-atᴵ-dens; densI; expNrm; zeroB; zero-integral)
  open ExpMomentN lem₁ using (powH; natB; factB)
  open PushforwardExpectation lem₁ using (pushI; E-atᴵ-push)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open QBS
  open Hom

  -- Exp(1)
  expDist : Pre WQ
  expDist = densDist negExpH expNrm

  fact-2 : fact 2 ≈ 1# + 1#
  fact-2 = trans (*-cong refl fact-1) (trans (*-identityʳ _) (+-cong (+-identityˡ 1#) refl))

  module Push (c : ∣A∣) (cB : Bnd c) where

    -- the scaling map `x ↦ c·x` and the pushforward
    sc : Hom S WQ WQ
    sc = scaleH c idW

    expPush : Pre WQ
    expPush = mapPre {WQ} {WQ} sc expDist

    -- the composite `x ↦ (c·x)ⁿ`
    comp : ℕ → Hom S WQ WQ
    comp n = _∘H_ S (powH n) sc

    -- `∫ e^{−x} (c·x)ⁿ = cⁿ n!`
    pow-int : ∀ n → ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (comp n)) ≈ pw n c * fact n
    pow-int n = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH (comp n)} {scaleH (pw n c) (pwNegExpH n)} pt)
      (trans (∫-scaleH (pw n c) (pwNegExpH n)) (*-cong refl (∫ᴹ-pw-moment n)))
      where
      pt : ∀ x → map (mulH {WQ} negExpH (comp n)) ⟨$⟩ x ≈ map (scaleH (pw n c) (pwNegExpH n)) ⟨$⟩ x
      pt x = trans (*-cong refl (pw-mul n c x)) (trans (*-comm _ _) (*-assoc (pw n c) (pw n x) (negExp x)))

    pcB : ∀ n → Bnd (pw n c)
    pcB zero = Is-1 finite
    pcB (suc n) = Is-* finite cB (pcB n)

    vB : ∀ n → Bnd (pw n c * fact n)
    vB n = Is-* finite (pcB n) (factB n)

    compB : ∀ n → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (comp n)))
    compB n = Is-resp′ (sym (pow-int n)) (vB n)
      where Is-resp′ = SubSemiring.Is-resp finite

    -- the integrable test `xⁿ` for the pushforward, from the composite against Exp(1)
    compD : ℕ → ITest expDist
    compD n = densI negExpH expNrm (comp n) (constW 0#) (compB n) zeroB

    powPushD : ℕ → ITest expPush
    powPushD n = pushI {WQ} {WQ} sc expDist (compD n) (toC (powH n)) (toC (constW 0#)) (λ y → refl) (λ y → refl)

    -- E[Xⁿ] ≃ cⁿ n!
    E-atᴵ-powPush : ∀ n → E-atᴵ expPush (powPushD n) ≃ ι (vB n)
    E-atᴵ-powPush n = ≃-trans (E-atᴵ-push {WQ} {WQ} sc expDist (compD n) (toC (powH n)) (toC (constW 0#)) (λ y → refl) (λ y → refl))
      (≃-trans (E-atᴵ-dens negExpH expNrm (comp n) (constW 0#) (compB n) zeroB)
        (mk≃ 0# (Is-0 finite) (+-cong (+-cong (pow-int n) (sym (zero-integral negExpH expNrm))) refl)))

    -- the mean `c`
    mean-push : E-atᴵ expPush (powPushD 1) ≃ ι cB
    mean-push = ≃-trans (E-atᴵ-powPush 1) (ι-cong (vB 1) cB (trans (*-cong (*-identityʳ c) fact-1) (*-identityʳ c)))

    -- the second moment `2c²`
    second-push : E-atᴵ expPush (powPushD 2) ≃ ι (vB 2)
    second-push = E-atᴵ-powPush 2

    -- the variance `c²`
    var-push : (E-atᴵ expPush (powPushD 2) +S (-S (E-atᴵ expPush (powPushD 1) *S E-atᴵ expPush (powPushD 1)))) ≃ ι (pcB 2)
    var-push = var-core (vB 1) (vB 2) (pcB 2) (moment-two c (fact 1) (fact 2) fact-1 fact-2)
      (E-atᴵ expPush (powPushD 1)) (E-atᴵ expPush (powPushD 2)) (E-atᴵ-powPush 1) (E-atᴵ-powPush 2)

    -- for a rate `l` with `l c ≈ 1`: `E[X]·λ ≃ 1` and `Var·λ² ≃ 1`
    module Rate (l : ∣A∣) (lc : l * c ≈ 1#) (lB : Bnd l) where
      plB : ∀ n → Bnd (pw n l)
      plB zero = Is-1 finite
      plB (suc n) = Is-* finite lB (plB n)

      pw-cl : ∀ n → pw n c * pw n l ≈ 1#
      pw-cl n = trans (sym (pw-mul n c l)) (trans (pw-cong n (trans (*-comm c l) lc)) (pw-one n))

      mean-rate : (E-atᴵ expPush (powPushD 1) *S ι lB) ≃ ι (Is-1 finite)
      mean-rate = ≃-trans (*S-congˡ (ι lB) mean-push) (scale-ι cB lB (Is-1 finite) (trans (*-comm c l) lc))

      var-rate : ((E-atᴵ expPush (powPushD 2) +S (-S (E-atᴵ expPush (powPushD 1) *S E-atᴵ expPush (powPushD 1)))) *S ι (plB 2))
        ≃ ι (Is-1 finite)
      var-rate = ≃-trans (*S-congˡ (ι (plB 2)) var-push) (scale-ι (pcB 2) (plB 2) (Is-1 finite) (pw-cl 2))
