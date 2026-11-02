{-# OPTIONS --safe --without-K #-}

-- The exponential distribution with a rate λ, through the expectation API (in the style of `Inference/ExpMomentN`).
-- For a rate `l ≤ 1` with reciprocal `c` (`l c ≈ 1`, `c ≤ natE (suc ν)`; see `Continuous/ExpRateMoment`):
--   * the density `d x = λ e^{−λx}` is normalised (`expNrmλ : ∫ d ≈ 1`, from `λ ∫ e^{−λx} = 1`) and
--     `expDistλ = densDist d expNrmλ`;
--   * `powλD n : ITest expDistλ` has parts `xⁿ` and `0`; `∫ d xⁿ = cⁿ n!` (`pow-int`);
--   * `E-atᴵ-powλD n : E[Xⁿ] ≃ cⁿ n!`, and rescaled `rate-moment n : E[Xⁿ] · λⁿ ≃ n!`;
--   * the mean `E[X] · λ ≃ 1`, the second moment `E[X²] · λ² ≃ 2` and the variance `Var · λ² ≃ 1`
--     (`mean-rate`, `second-rate`, `var-rate`, with `Var = E[X²] − (E X)²` as in `Inference/ExpDistVar`).
-- Positive rationals ≤ 1: `Continuous/ExpRateMoment.Rat` gives the data `(l, c, ν)` for (a+1)/(b+1) with a ≤ b (`DistRat`).
module QBS.Inference.ExpRateDist where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.ExpRate using (module AlgRate)
open import QBS.Analysis.ExpRateSigned using (module AlgSigned)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpRateMoment using (module ExpRateMoment)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
open import QBS.Inference.ExpMomentN using (module ExpMomentN)
import QBS.Inference.ExpectationInt as EI

module ExpRateDist (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-assoc; *-identityʳ; +-identityˡ; +-identityʳ; ≤-trans; ≤-reflexive)
  open OmegaSemiring A using () renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open AlgP A R using (pw)
  open NegExp (lemOf lem₁) using (negExp)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_]; ≃-trans; _+S_; _*S_; -S_; ι; +S-cong; -S-cong; *S-cong; *S-congˡ)
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+; Is-*)
  open AlgRate A R using (module Sc)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open DensityDist lem₁ using (densDist)
  open HalfLineMomentFact lem₁ using (fact; fact-1)
  open HalfLineRate lem₁ using (negExpRH; pwRH; scaleH; ∫-scaleH)
  open ExpRateMoment lem₁ using (module Mom; module Rat)
  open DensityExpectation lem₁ using (E-atᴵ-dens; densI; zero-integral)
  open ExpMomentN lem₁ using (powH; natB; factB)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open QBS
  open Hom

  module Dist (l c : ∣A∣) (ν : ℕ) (lc : l * c ≈ 1#) (l1 : l ≤ 1#) (cν : c ≤ natE (suc ν)) where
    module M = Mom l c ν lc l1 cν
    open Sc l c lc using (l-step; pw-lc; rate-eq)
    open AlgSigned A R l c lc using (var-gen)

    -- the density `λ e^{−λx}`
    d : Hom S WQ WQ
    d = scaleH l (negExpRH l)

    expNrmλ : ∫ᴹ {WQ} lebPre d ≈ 1#
    expNrmλ = trans (∫-scaleH l (negExpRH l)) (trans (*-cong refl M.I.∫-negExpR) lc)

    expDistλ = densDist d expNrmλ

    fact-2 : fact 2 ≈ 1# + 1#
    fact-2 = trans (*-cong refl fact-1) (trans (*-identityʳ _) (+-cong (+-identityˡ 1#) refl))

    -- ∫ d xⁿ = cⁿ n!
    pow-int : ∀ n → ∫ᴹ {WQ} lebPre (mulH {WQ} d (powH n)) ≈ pw n c * fact n
    pow-int n = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (powH n)} {scaleH l (pwRH l n)}
        (λ x → trans (*-assoc l (negExp (l * x)) (pw n x)) (*-cong refl (*-comm _ _))))
      (trans (∫-scaleH l (pwRH l n)) (trans (*-cong refl (M.moment n)) (l-step (pw n c) (fact n))))

    -- the bounds
    cB : Bnd c
    cB = proj₁ (natB (suc ν)) , ≤-trans cν (proj₂ (natB (suc ν)))

    lB : Bnd l
    lB = 1 , ≤-trans l1 (≤-reflexive (sym (+-identityʳ 1#)))

    pcB : ∀ n → Bnd (pw n c)
    pcB zero = Is-1 finite
    pcB (suc n) = Is-* finite cB (pcB n)

    plB : ∀ n → Bnd (pw n l)
    plB zero = Is-1 finite
    plB (suc n) = Is-* finite lB (plB n)

    vB : ∀ n → Bnd (pw n c * fact n)
    vB n = Is-* finite (pcB n) (factB n)

    powB : ∀ n → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d (powH n)))
    powB n = Is-resp finite (sym (pow-int n)) (vB n)

    zeroB : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d (constW 0#)))
    zeroB = Is-resp finite (sym (zero-integral d expNrmλ)) (Is-0 finite)

    -- the test `x ↦ xⁿ`
    powλD : ℕ → ITest expDistλ
    powλD n = densI d expNrmλ (powH n) (constW 0#) (powB n) zeroB

    -- E[Xⁿ] ≃ cⁿ n!
    E-atᴵ-powλD : ∀ n → E-atᴵ expDistλ (powλD n) ≃ ((pw n c * fact n) − 0# [ vB n , Is-0 finite ])
    E-atᴵ-powλD n = ≃-trans (E-atᴵ-dens d expNrmλ (powH n) (constW 0#) (powB n) zeroB)
      (mk≃ 0# (Is-0 finite) (+-cong (+-cong (pow-int n) (sym (zero-integral d expNrmλ))) refl))

    -- E[Xⁿ] · λⁿ ≃ n!
    rate-moment : ∀ n → (E-atᴵ expDistλ (powλD n) *S ι (plB n)) ≃ ι (factB n)
    rate-moment n = ≃-trans (*S-congˡ (ι (plB n)) (E-atᴵ-powλD n)) (mk≃ 0# (Is-0 finite) (rate-eq n (fact n)))

    -- the mean: E[X] · λ ≃ 1
    mean-rate : (E-atᴵ expDistλ (powλD 1) *S ι (plB 1)) ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
    mean-rate = ≃-trans (rate-moment 1) (mk≃ 0# (Is-0 finite) (+-cong (+-cong fact-1 refl) refl))

    -- the second moment: E[X²] · λ² ≃ 2
    second-rate : (E-atᴵ expDistλ (powλD 2) *S ι (plB 2)) ≃ ((1# + 1#) − 0# [ Is-+ finite (Is-1 finite) (Is-1 finite) , Is-0 finite ])
    second-rate = ≃-trans (rate-moment 2) (mk≃ 0# (Is-0 finite) (+-cong (+-cong fact-2 refl) refl))

    -- the variance: `(E[X²] − (E X)²) · λ² ≃ 1`
    var-rate : ((E-atᴵ expDistλ (powλD 2) +S (-S (E-atᴵ expDistλ (powλD 1) *S E-atᴵ expDistλ (powλD 1)))) *S ι (plB 2))
      ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
    var-rate = var-gen (fact 1) (fact 2) (vB 1) (vB 2) (plB 2) (E-atᴵ expDistλ (powλD 1)) (E-atᴵ expDistλ (powλD 2))
      (E-atᴵ-powλD 1) (E-atᴵ-powλD 2) fact-1 fact-2

  -- the rate (a+1)/(b+1) ≤ 1
  module DistRat (a b : ℕ) (ab : a ℕ.≤ b) where
    open Rat a b ab using (ratL; ratC; ratLC; ratL1; ratCν)
    open Dist ratL ratC b ratLC ratL1 ratCν public
