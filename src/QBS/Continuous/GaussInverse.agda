{-# OPTIONS --safe --without-K #-}

-- The Gaussian normaliser `Z = ∫₀^∞ e^{−x²/2} dλ` is invertible: `Z · n ≈ 1#` for some `n` (`Z-inv`), so that the half-normal
-- distribution can be normalised without ever computing Z (`Inference/HalfNormal`).  Classically a lower real is invertible
-- when it has a positive member and a non-member (`SFiniteNorm.inv-ok`, with `LowerInverse.invC` the inverse):
--   * `finZ`: `Z ≤ 4` (`GaussFinite.Z-le`), and `natE 4` has the non-member given by `inv-fin` from `4 · ¼ = 1` (`ExpLower.inv-ok`);
--   * `posZ`: `Z ≥ ∫₀¹ Φ ≥ Φ(1) ≥ ½`: from `1 ≤ Φ(1) + ½` (`GaussHalfLine.E-c`) and cancelling `½`.  If Z had no positive
--     member it would be `≤ 0`, hence `1 = ½ + ½ ≤ 0`, impossible (`zero≉one`).
module QBS.Continuous.GaussInverse where

open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
import QBS.Analysis.LowerReals as LR
open LR.Cut using () renaming (mem to memC; open′ to openC)
open LR._⊑_ using () renaming (ap to apC)
open import QBS.Analysis.ExpLower using (qinvC; inv-ok)
import QBS.Analysis.RationalLemmas as RL
import QBS.Analysis.LowerInverse as LI
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.CoinIndep using (module CoinIndep)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussFinite using (module GaussFinite)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.TailFTC using (module TailFTC)

module GaussInverse (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half+half; cancel≤)
  open Exp A using (natE)
  open HalfOrder A R using (half≤1)
  open Series A using (∑ᶠ; ≤-∑ᶠ)
  open Expansion A half half+half using (expansion; expansion≤1)
  open Lebesgue (lemOf lem₁) using (J; J-mono)
  open Meas (lemOf lem₁) using (Meas-const)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open CoinIndep lem₁ using (fairCoin-prob)
  open FairCoin lem₁ using (fairCoin)
  open SFiniteNorm (lemOf lem₁) using (PosC; FinC; inv-fin; zero≉one) renaming (inv-ok to inv-okN)
  open HalfLine lem₁ using (shiftPt; Meas-hshift; ∫ᴹ-leb)
  open GaussHalfLine lem₁ using (Φ; phiH; E-c)
  open GaussFinite lem₁ using (Φ-anti; Z-le)
  open GaussMoment lem₁ using (Z)

  ----------------------------------------------------------------------------
  -- finite

  -- (1 + 1) + (1 + 1) = natE 4
  four-eq : (1# + 1#) + (1# + 1#) ≈ natE 4
  four-eq = trans (sym (+-assoc (1# + 1#) 1# 1#)) (sym (+-cong (+-cong (+-cong (+-identityˡ 1#) refl) refl) refl))

  fin4 : FinC (natE 4)
  fin4 = inv-fin (natE 4) (qinvC (lemOf lem₁) 3) (trans (*-comm _ _) (inv-ok (lemOf lem₁) 3))

  finZ : FinC Z
  finZ = proj₁ fin4 , (λ mz → proj₂ fin4 (apC (≤-trans Z-le (≤-reflexive four-eq)) (proj₁ fin4) mz))

  ----------------------------------------------------------------------------
  -- positive

  -- Φ(1) ≥ ½
  u-half : half * (natE 1 * natE 1) ≈ half
  u-half = trans (*-cong refl (trans (*-cong (+-identityˡ 1#) (+-identityˡ 1#)) (*-identityˡ 1#))) (*-identityʳ half)

  half≤Φ1 : half ≤ Φ (natE 1)
  half≤Φ1 = cancel≤ half≤1 (≤-trans (≤-reflexive half+half)
    (≤-trans (E-c {half * (natE 1 * natE 1)})
      (≤-trans (+-mono ≤-refl (≤-reflexive u-half)) (≤-reflexive (+-comm _ _)))))

  -- Z ≥ the integral over [0,1] ≥ Φ(1)
  Φ1≤Z : Φ (natE 1) ≤ Z
  Φ1≤Z = ≤-trans (≤-reflexive (sym (J-const fairCoin-prob (Φ (natE 1)))))
    (≤-trans (J-mono fairCoin (Meas-const (Φ (natE 1))) (Meas-hshift 0 phiH)
        (λ r → Φ-anti (+-mono (≤-refl {natE 0}) (expansion≤1 r))))
      (≤-trans (≤-∑ᶠ _ 0) (≤-reflexive (sym (∫ᴹ-leb phiH)))))

  -- a lower real has a positive member or is ≤ 0
  posOrZero : ∀ c → PosC c ⊎ c ≤ 0#
  posOrZero c with lemOf lem₁ (PosC c)
  ... | inj₁ p = inj₁ p
  ... | inj₂ no = inj₂ (LR.mk⊑ (λ q mq → bound q mq))
    where
    bound : ∀ q → memC c q → q RL.<ᵘ RL.0ℚᵘ
    bound q mq with openC c mq
    ... | q′ , q<q′ , mq′ with RL.pos-or-nonpos q′
    ...   | inj₁ 0<q′ = ⊥-elim (no (q′ , 0<q′ , mq′))
    ...   | inj₂ q′≤0 = RL.<-≤-trans q<q′ q′≤0

  -- no positive member would make Z ≤ 0, hence 1 = ½ + ½ ≤ 0
  not-zero : Z ≤ 0# → ⊥
  not-zero z≤0 = zero≉one (≤-antisym 0-least one≤0)
    where
    h0 : half ≤ 0#
    h0 = ≤-trans half≤Φ1 (≤-trans Φ1≤Z z≤0)
    one≤0 : 1# ≤ 0#
    one≤0 = ≤-trans (≤-reflexive (sym half+half)) (≤-trans (+-mono h0 h0) (≤-reflexive (+-identityˡ 0#)))

  posZ-from : PosC Z ⊎ Z ≤ 0# → PosC Z
  posZ-from (inj₁ p) = p
  posZ-from (inj₂ z≤0) = ⊥-elim (not-zero z≤0)

  posZ : PosC Z
  posZ = posZ-from (posOrZero Z)

  ----------------------------------------------------------------------------
  -- the inverse

  Z-inv : Σ ∣A∣ (λ n → Z * n ≈ 1#)
  Z-inv = LI.invC Z , inv-okN Z posZ finZ
