{-# OPTIONS --safe --without-K #-}

-- Validation of the dyadic scaling (`Continuous/HalfLineScale`): the pushforward Exp(c = ½) of `Inference/ExpPushforward` and the
-- density distribution of `2 e^{−2x}` have the same integral for every non-negative test `f : [0,∞] ⇒ [0,∞]`.
--   * `dens2 = scaleH 2 (negExpRH 2)`, the density `x ↦ 2 e^{−2x}`; `nrm2 : ∫ dens2 dλ ≈ 1` from `∫-dbl`;
--   * `agree : ∫ (ι expPush½) f ≈ ∫ (ι (densDist dens2 nrm2)) f`, the first case of density/pushforward agreement beyond
--     rate 1 (compare `ExpRateOne` at rate 1).  Proof: `∫ e^{−y} f(y/2) dy = 2 ∫ e^{−2x} f(x) dx` is `∫-dbl` for the test
--     `y ↦ e^{−y} f(y/2)`.
module QBS.Inference.ExpPushforwardAgree where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import Data.Product.Base using (_,_)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.HalfLineScale using (module HalfLineScale)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
open import QBS.Inference.ExpPushforward using (module ExpPushforward)

module ExpPushforwardAgree (lem₁ : LEM₁) where
  open ExpPushforward lem₁ using (module Push; expDist)
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; 1#; _*_; refl; sym; trans; *-cong; *-assoc; ≤-trans; ≤-reflexive; ≤-refl; +-identityˡ; +-identityʳ; +-mono; 0-least; *-identityˡ)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open AlgDy A half hh using (two; two-half; unhalf)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong; ∫ᴹ-map)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-nat)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineNorm lem₁ using (∫ᴹ-leb-negExp-norm)
  open HalfLineRate lem₁ using (negExpRH; scaleH; ∫-scaleH)
  open HalfLineScale lem₁ using (dblH; ∫-dbl; half-two)
  open DensityDist lem₁ using (densDist; ∫-dens)
  open DensityExpectation lem₁ using (expNrm)
  open ExpDist lem₁ using (idW)
  open QBS
  open Hom

  -- ½ ≤ 1 ≈ nat 1
  half-bnd : Bnd half
  half-bnd = 1 , ≤-trans (≤-trans (≤-reflexive (sym (+-identityʳ half))) (≤-trans (+-mono ≤-refl 0-least) (≤-reflexive hh)))
                         (≤-reflexive (sym (+-identityʳ 1#)))

  module P = Push half half-bnd

  -- the density `x ↦ 2 e^{−2x}`
  dens2 : Hom S WQ WQ
  dens2 = scaleH two (negExpRH two)

  -- ∫ e^{−2x} dλ = ½
  ∫-negExp2 : ∫ᴹ {WQ} lebPre (negExpRH two) ≈ half * 1#
  ∫-negExp2 = trans (∫ᴹ-cong {WQ} lebPre {negExpRH two} {_∘H_ S negExpH dblH} (λ x → refl))
    (trans (∫-dbl negExpH) (*-cong refl ∫ᴹ-leb-negExp-norm))

  -- ∫ 2 e^{−2x} dλ = 1
  nrm2 : ∫ᴹ {WQ} lebPre dens2 ≈ 1#
  nrm2 = trans (∫-scaleH two (negExpRH two)) (trans (*-cong refl ∫-negExp2)
    (trans (sym (*-assoc two half 1#)) (trans (*-cong two-half refl) (*-identityˡ 1#))))

  -- the pushforward Exp(½) and the density 2e^{−2x} have the same integrals
  agree : ∀ (f : Hom S WQ WQ) →
    ∫ᴹ {WQ} (ιPre {WQ} P.expPush) f ≈ ∫ᴹ {WQ} (ιPre {WQ} (densDist dens2 nrm2)) f
  agree f = trans (ι-nat {WQ} {WQ} P.sc expDist f)
    (trans (∫ᴹ-map {WQ} {WQ} P.sc (ιPre {WQ} expDist) f)
      (trans (∫-dens negExpH expNrm (_∘H_ S f P.sc))
        (trans (unhalf _ _ (sym (∫-dbl g)))
          (trans (*-cong refl (∫ᴹ-cong {WQ} lebPre {_∘H_ S g dblH} {mulH {WQ} (negExpRH two) f}
                                (λ x → *-cong refl (Func.cong (map f) (half-two x)))))
            (trans (sym (∫-scaleH two (mulH {WQ} (negExpRH two) f)))
              (trans (∫ᴹ-cong {WQ} lebPre {scaleH two (mulH {WQ} (negExpRH two) f)} {mulH {WQ} dens2 f}
                       (λ x → sym (*-assoc two _ _)))
                (sym (∫-dens dens2 nrm2 f))))))))
    where
    g : Hom S WQ WQ
    g = mulH {WQ} negExpH (_∘H_ S f P.sc)
