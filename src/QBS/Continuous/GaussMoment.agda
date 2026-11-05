{-# OPTIONS --safe --without-K #-}

-- Gaussian moments on the half-line, without π (part 2): `∫₀^∞ xʲ⁺² e^{−x²/2} = (j+1) ∫₀^∞ xʲ e^{−x²/2}`.
-- The normaliser `Z = ∫₀^∞ e^{−x²/2} dλ` stays abstract (its value `√(π/2)` is never used).
--   * `moment-succ j : ∫ᴹ lebPre (gMomH (j+2)) ≈ (j+1) · ∫ᴹ lebPre (gMomH j)`: integration by parts on the half-line,
--     `TailFTCLipHalf.glue` applied to the unit-interval identities of `GaussHalfLine` with `G = xʲ⁺¹ e^{−x²/2}`;
--     `G 0 = 0`, and `G(N) → 0` along the multiples of j+2 because `e^{−N²/2} ≤ e^{−N}` for N ≥ 2 (`Analysis/GaussTail.big`)
--     and `Nʲ⁺¹ e^{−N} → 0` (`Analysis/ExpTail`);
--   * `∫-x²φ : ∫ x² e^{−x²/2} ≈ ∫ e^{−x²/2}` (j = 0: so `Var = 1` for the half-normal);
--   * `even-moment n : ∫ x²ⁿ e^{−x²/2} ≈ (2n−1)‼ · Z`, with `dfac n = (2n−1)‼` (`dfac 0 = 1`, `dfac (n+1) = (2n+1) dfac n`).
module QBS.Continuous.GaussMoment where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussTail using (module AlgGT)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipHalf using (module TailFTCLipHalf)

module GaussMoment (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgP A R using (pw)
  open AlgGT A R using (big)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-cong; ∑ᶠ-scale)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineMomentFact lem₁ using (module T)
  open GaussHalfLine lem₁ using (Φ; phiH; gh; gMomH; gKH; module AtInterval)
  open TailFTCLipHalf lem₁ using (module Glue)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- ∫ k = (j+1) ∫ xʲ e^{−x²/2}

  k-scale : ∀ j → ∫ᴹ {WQ} lebPre (gKH j) ≈ natE (suc j) * ∫ᴹ {WQ} lebPre (gMomH j)
  k-scale j = trans (∫ᴹ-leb (gKH j)) (trans (∑ᶠ-cong term) (trans (sym (∑ᶠ-scale (natE (suc j)) _))
    (*-cong refl (sym (∫ᴹ-leb (gMomH j))))))
    where
    term : ∀ n → J fairCoin (λ r → map (gKH j) ⟨$⟩ shiftPt n r) (Meas-hshift n (gKH j))
      ≈ natE (suc j) * J fairCoin (λ r → map (gMomH j) ⟨$⟩ shiftPt n r) (Meas-hshift n (gMomH j))
    term n = trans (J-irrel fairCoin (Meas-hshift n (gKH j))
        (Meas-⊗ {λ _ → natE (suc j)} {λ r → map (gMomH j) ⟨$⟩ shiftPt n r} (Meas-const (natE (suc j))) (Meas-hshift n (gMomH j))))
      (J-scale fairCoin (natE (suc j)) {λ r → map (gMomH j) ⟨$⟩ shiftPt n r} (Meas-hshift n (gMomH j)))

  ----------------------------------------------------------------------------
  -- G = xʲ⁺¹ e^{−x²/2}: G 0 = 0 and G(N) → 0 along a subsequence

  G0 : ∀ j → gh (suc j) 0# ≈ 0#
  G0 j = trans (*-cong (zeroˡ (pw j 0#)) refl) (zeroˡ (Φ 0#))

  gtail : ∀ j m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × gh (suc j) (natE N) ≤ hp m)
  gtail j m N₀ = N , ℕ.≤-trans (ℕ.m≤m+n N₀ 2) le , ≤-trans (*-mono (pw (suc j) (natE N)) Φ≤E) b
    where
    t = T.tail (suc j) m (N₀ ℕ.+ 2)
    N : ℕ
    N = proj₁ t
    le : N₀ ℕ.+ 2 ℕ.≤ N
    le = proj₁ (proj₂ t)
    b : pw (suc j) (natE N) * negExp (natE N) ≤ hp m
    b = proj₂ (proj₂ t)
    Φ≤E : Φ (natE N) ≤ negExp (natE N)
    Φ≤E = negExp-anti (big N (ℕ.≤-trans (ℕ.m≤n+m 2 N₀) le))

  ----------------------------------------------------------------------------
  -- ∫ xʲ⁺² e^{−x²/2} = (j+1) ∫ xʲ e^{−x²/2}

  moment-succ : ∀ j → ∫ᴹ {WQ} lebPre (gMomH (suc (suc j))) ≈ natE (suc j) * ∫ᴹ {WQ} lebPre (gMomH j)
  moment-succ j = trans (Glue.glue (gMomH (suc (suc j))) (gKH j) (gh (suc j)) (λ n → AtInterval.ibp-unit n j) (G0 j) (gtail j))
    (k-scale j)

  -- Z = ∫ e^{−x²/2}, and j = 0: ∫ x² e^{−x²/2} = Z
  Z : ∣A∣
  Z = ∫ᴹ {WQ} lebPre phiH

  ∫-gMom0 : ∫ᴹ {WQ} lebPre (gMomH 0) ≈ Z
  ∫-gMom0 = ∫ᴹ-cong lebPre {gMomH 0} {phiH} (λ x → *-identityˡ (Φ x))

  ∫-x²φ : ∫ᴹ {WQ} lebPre (gMomH 2) ≈ Z
  ∫-x²φ = trans (moment-succ 0) (trans (*-cong (trans (+-identityˡ 1#) refl) ∫-gMom0) (*-identityˡ Z))

  ----------------------------------------------------------------------------
  -- the even moments

  ev : ℕ → ℕ
  ev zero = 0
  ev (suc n) = suc (suc (ev n))

  -- (2n−1)‼
  dfac : ℕ → ∣A∣
  dfac zero = 1#
  dfac (suc n) = natE (suc (ev n)) * dfac n

  even-moment : ∀ n → ∫ᴹ {WQ} lebPre (gMomH (ev n)) ≈ dfac n * Z
  even-moment zero = trans ∫-gMom0 (sym (*-identityˡ Z))
  even-moment (suc n) = trans (moment-succ (ev n))
    (trans (*-cong refl (even-moment n)) (sym (*-assoc (natE (suc (ev n))) (dfac n) Z)))
