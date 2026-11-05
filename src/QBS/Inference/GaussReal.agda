{-# OPTIONS --safe --without-K #-}

-- The standard Gaussian on the whole real line `RQ = WQ +Q WQ` (`Continuous/RealLine`), with `E[X] ≃ 0` and `E[X²] ≃ 1`,
-- and no value for `π` (nor for `Z = ∫₀^∞ e^{−x²/2}`): the density is the symmetric `[φ , φ]`, `φ = GaussHalfLine.phiH`, with total
-- mass `Z + Z`, normalised by `n′ = n · ½` where `Z · n ≈ 1#` (`GaussInverse.Z-inv`).  Through `Inference/SymExpectation`:
--   * `gaussR : Pre RQ`;
--   * the identity statistic `xI : ITest gaussR` (`inl x ↦ pos x`, `inr x ↦ neg x`), integrable since `x ≤ 1 + x²`
--     (`Analysis/CutSplit.split1`) and `∫ x² φ = Z` (`GaussMoment.∫-x²φ`), with `E-atᴵ-X : E-atᴵ gaussR xI ≃ 0`, by oddness;
--   * the square `sqI` (`pos = x²`, `neg = 0`) with `E-atᴵ-X² : E-atᴵ gaussR sqI ≃ 1`, from `∫ x² φ = Z` on each half;
--   * the variance `var-gaussR : E[X²] − (E X)² ≃ 1`.
module QBS.Inference.GaussReal where

open import Data.Product.Base using (proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.CutSplit using (split1)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.GaussInverse using (module GaussInverse)
open import QBS.Inference.Domination using (module Domination)
open import QBS.Inference.SymExpectation using (module SymExpectation)
import QBS.Inference.ExpectationInt as EI

module GaussReal (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
    using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; *-comm; *-assoc; *-identityˡ; *-identityʳ;
           +-identityʳ; +-identityˡ; +-comm; zeroˡ; zeroʳ; distribʳ; ≤-trans; ≤-reflexive; ≤-+ʳ; +-mono; *-mono)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Bounded A using (Bnd; finite; _≃_; mk≃; ≃-trans; _+S_; _*S_; -S_; +S-cong; -S-cong; *S-cong; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0; Is-1)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH; copairH)
  open ExpDist lem₁ using (idW)
  open ExpDistSq lem₁ using (sqW)
  open GaussHalfLine lem₁ using (phiH; gMomH; gh)
  open GaussMoment lem₁ using (Z; ∫-x²φ)
  open GaussInverse lem₁ using (Z-inv)
  open Domination lem₁ using (addH; ∫ᴹ-mono; ∫ᴹ-add; ∫ᴹ-scale; Bnd-≤)
  open SymExpectation lem₁ using (≃-≈; module SymE)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)
    using (solve; _:+_; _:*_; _:=_; con)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open Hom

  ----------------------------------------------------------------------------
  -- the normalisation: `(Z + Z) · n′ ≈ 1`

  n′ : ∣A∣
  n′ = proj₁ Z-inv * half

  nn : (Z + Z) * n′ ≈ 1#
  nn = trans (distribʳ n′ Z Z) (trans (+-cong e e) (trans (+-cong (*-identityˡ half) (*-identityˡ half)) hh))
    where e : Z * n′ ≈ 1# * half
          e = trans (sym (*-assoc Z (proj₁ Z-inv) half)) (*-cong (proj₂ Z-inv) refl)

  module G = SymE phiH Z refl n′ nn

  gaussR : Pre RQ
  gaussR = G.symDist

  ----------------------------------------------------------------------------
  -- the statistics

  zeroW : Hom S WQ WQ
  zeroW = constW 0#

  Xp Xn Q2 zeroR : Hom S RQ WQ
  Xp = copairH idW zeroW
  Xn = copairH zeroW idW
  Q2 = copairH sqW sqW
  zeroR = constW 0#

  -- the half-line integrals
  zint : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH zeroW) ≈ 0#
  zint = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH zeroW} {mulH {WQ} (constW 0#) phiH} (λ x → *-comm _ _))
    (trans (∫ᴹ-scale lebPre 0# phiH) (zeroˡ _))

  sq-eq : ∀ x → map (mulH {WQ} phiH sqW) ⟨$⟩ x ≈ map (gMomH 2) ⟨$⟩ x
  sq-eq x = trans (*-comm _ _) (*-cong (sym (*-cong refl (*-identityʳ x))) refl)

  sqint : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH sqW) ≈ Z
  sqint = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH sqW} {gMomH 2} sq-eq) ∫-x²φ

  -- `p x ≤ p + x² p`, for `x ≤ 1` and for `1 ≤ x`
  key-lo : ∀ p x → x ≤ 1# → p * x ≤ p + (x * (x * 1#)) * p
  key-lo p x le = ≤-trans (*-mono p le) (≤-trans (≤-reflexive (*-identityʳ p)) ≤-+ʳ)

  key-hi : ∀ p x → 1# ≤ x → p * x ≤ p + (x * (x * 1#)) * p
  key-hi p x le = ≤-trans (*-mono p x≤xx)
    (≤-trans (≤-reflexive (*-comm p _)) (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ p))))
    where
      x≤xx : x ≤ x * (x * 1#)
      x≤xx = ≤-trans (≤-reflexive (sym (*-identityʳ x)))
        (*-mono x (≤-trans le (≤-reflexive (sym (*-identityʳ x)))))

  key : ∀ p x → p * x ≤ p + (x * (x * 1#)) * p
  key p x = key-cases p x (split1 (lemOf lem₁) x)
    where
      key-cases : ∀ p x → x ≤ 1# ⊎ 1# ≤ x → p * x ≤ p + (x * (x * 1#)) * p
      key-cases p x (inj₁ lo) = key-lo p x lo
      key-cases p x (inj₂ hi) = key-hi p x hi

  A1 : ∣A∣
  A1 = ∫ᴹ {WQ} lebPre (mulH {WQ} phiH idW)

  A1-le : A1 ≤ Z + Z
  A1-le = ≤-trans (∫ᴹ-mono lebPre {mulH {WQ} phiH idW} {addH phiH (gMomH 2)} (λ x → key _ x))
    (≤-reflexive (trans (∫ᴹ-add lebPre phiH (gMomH 2)) (+-cong refl ∫-x²φ)))

  ----------------------------------------------------------------------------
  -- the mean

  -- the two halves of the integrals of `Xp`
  Xp-l : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S Xp inlH)) ≈ A1
  Xp-l = ∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S Xp inlH)} {mulH {WQ} phiH idW} (λ x → refl)

  Xp-r : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S Xp inrH)) ≈ 0#
  Xp-r = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S Xp inrH)} {mulH {WQ} phiH zeroW} (λ x → refl)) zint

  halves-le : ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S Xp inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S Xp inrH))
    ≤ (Z + Z) + 0#
  halves-le = +-mono (≤-trans (≤-reflexive Xp-l) A1-le) (≤-reflexive Xp-r)

  one-eq : n′ * ((Z + Z) + 0#) ≈ 1#
  one-eq = trans (*-cong refl (+-identityʳ _)) (trans (*-comm _ _) nn)

  RHXp-le : G.RH Xp ≤ 1#
  RHXp-le = ≤-trans (*-mono n′ halves-le) (≤-reflexive one-eq)

  bXp : Bnd (G.RH Xp)
  bXp = Bnd-≤ RHXp-le (Is-1 finite)

  RH-X : G.RH Xp ≈ G.RH Xn
  RH-X = G.RH-odd Xp Xn (λ x → refl) (λ x → refl)

  bXn : Bnd (G.RH Xn)
  bXn = Is-resp finite RH-X bXp

  xI : ITest gaussR
  xI = G.symI Xp Xn bXp bXn

  -- E[X] ≃ 0, by oddness
  E-atᴵ-X : E-atᴵ gaussR xI ≃ (0# − 0# [ Is-0 finite , Is-0 finite ])
  E-atᴵ-X = G.E-atᴵ-odd Xp Xn bXp bXn (λ x → refl) (λ x → refl)

  ----------------------------------------------------------------------------
  -- the second moment

  Q2-half : ∀ (h : Hom S WQ RQ) → (∀ x → map (_∘H_ S Q2 h) ⟨$⟩ x ≈ map sqW ⟨$⟩ x) →
    ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S Q2 h)) ≈ Z
  Q2-half h e = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S Q2 h)} {mulH {WQ} phiH sqW} (λ x → *-cong refl (e x))) sqint

  RH-Q2 : G.RH Q2 ≈ 1#
  RH-Q2 = trans (*-cong refl (+-cong (Q2-half inlH (λ x → refl)) (Q2-half inrH (λ x → refl)))) (trans (*-comm _ _) nn)

  Z-half : ∀ (h : Hom S WQ RQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (_∘H_ S zeroR h)) ≈ 0#
  Z-half h = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (_∘H_ S zeroR h)} {mulH {WQ} phiH zeroW} (λ x → refl)) zint

  RH-zero : G.RH zeroR ≈ 0#
  RH-zero = trans (*-cong refl (trans (+-cong (Z-half inlH) (Z-half inrH)) (+-identityˡ 0#))) (zeroʳ n′)

  bQ2 : Bnd (G.RH Q2)
  bQ2 = Is-resp finite (sym RH-Q2) (Is-1 finite)

  bZero : Bnd (G.RH zeroR)
  bZero = Is-resp finite (sym RH-zero) (Is-0 finite)

  sqI : ITest gaussR
  sqI = G.symI Q2 zeroR bQ2 bZero

  -- E[X²] ≃ 1
  E-atᴵ-X² : E-atᴵ gaussR sqI ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  E-atᴵ-X² = ≃-trans (G.E-atᴵ-sym Q2 zeroR bQ2 bZero) (≃-≈ RH-Q2 RH-zero)

  ----------------------------------------------------------------------------
  -- the variance

  var-arith : (((1# − 0# [ Is-1 finite , Is-0 finite ]) +S
      (-S ((0# − 0# [ Is-0 finite , Is-0 finite ]) *S (0# − 0# [ Is-0 finite , Is-0 finite ])))))
    ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-arith = mk≃ 0# (Is-0 finite) (solve 0 (((con 1 :+ (con 0 :* con 0 :+ con 0 :* con 0)) :+ con 0 :+ con 0)
    := ((con 1 :+ (con 0 :+ (con 0 :* con 0 :+ con 0 :* con 0))) :+ con 0)) refl)

  -- the variance: `E[X²] − (E X)² ≃ 1`
  var-gaussR : (E-atᴵ gaussR sqI +S (-S (E-atᴵ gaussR xI *S E-atᴵ gaussR xI))) ≃ (1# − 0# [ Is-1 finite , Is-0 finite ])
  var-gaussR = ≃-trans (+S-cong E-atᴵ-X² (-S-cong (*S-cong E-atᴵ-X E-atᴵ-X))) var-arith
