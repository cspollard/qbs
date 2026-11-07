{-# OPTIONS --safe --without-K #-}

-- Gaussian first moment on the half-line: `∫₀^∞ x e^{−x²/2} dx = 1` (no π, no abstract normaliser).
-- With `G = e^{−x²/2}` and `G′ = −x e^{−x²/2}` the unit-interval identities of `Continuous/GaussMeanUnit` are
--     aₙ + φ(n+1) = φ(n) + bₙ,    aₙ = ∫₀¹ xφ(n+u) du,   bₙ = ∫₀¹ 0 du = 0,
-- so the partial sums satisfy `∑_{n<N} aₙ + φ(N) = φ(0) = 1` (`TailFTCLipHalf.tele-ibp`).  Since φ(N) → 0 along the
-- integers N ≥ 2 (φ(N) ≤ e^{−N}, `Analysis/GaussTail.big`, and `Continuous/HalfLineMomentFact.T.tail` at j = 0),
-- `∑ aₙ ≤ 1` (every partial sum) and `1 ≤ ∑ aₙ + ½ᵐ` (a far-out partial sum).  Then `∫ᴹ-leb` gives
--   `∫-xφ : ∫ᴹ lebPre (gMomH 1) ≈ 1`.
-- (`TailFTCLipHalf.Glue` assumes `G 0 = 0`, which fails for G = φ, so the sums are handled directly.)
module QBS.Continuous.GaussMean where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)

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
open import QBS.Continuous.GaussMeanUnit using (module GaussMeanUnit)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipHalf using (module TailFTCLipHalf)

module GaussMean (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; arch; hp)
  open AlgP A R using (pw)
  open AlgGT A R using (big)
  open Exp A using (natE)
  open Series A using (psum; ∑ᶠ; ∑ᶠ-lub; psum≤∑ᶠ)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp-zero; negExp-cong)
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineMomentFact lem₁ using (module T)
  open GaussHalfLine lem₁ using (Φ; Φ-cong; gMomH)
  open GaussMeanUnit lem₁ using (kzH; module AtInterval1)
  open TailFTCLipHalf lem₁ using (tele-ibp)
  open QBS
  open Hom

  -- the unit integrals of h = x φ and of the zero test
  a b : ℕ → ∣A∣
  a n = J fairCoin (λ r → map (gMomH 1) ⟨$⟩ shiftPt n r) (Meas-hshift n (gMomH 1))
  b n = J fairCoin (λ r → map kzH ⟨$⟩ shiftPt n r) (Meas-hshift n kzH)

  b0 : ∀ n → b n ≈ 0#
  b0 n = trans (J-irrel fairCoin (Meas-hshift n kzH)
      (Meas-⊗ {λ _ → 0#} {λ r → map (gMomH 0) ⟨$⟩ shiftPt n r} (Meas-const 0#) (Meas-hshift n (gMomH 0))))
    (trans (J-scale fairCoin 0# {λ r → map (gMomH 0) ⟨$⟩ shiftPt n r} (Meas-hshift n (gMomH 0)))
      (zeroˡ _))

  psum-b0 : ∀ N → psum b N ≈ 0#
  psum-b0 zero = refl
  psum-b0 (suc N) = trans (+-cong (psum-b0 N) (b0 N)) (+-identityˡ 0#)

  Φ0 : Φ 0# ≈ 1#
  Φ0 = trans (negExp-cong (trans (*-cong refl (zeroˡ 0#)) (zeroʳ half))) negExp-zero

  -- ∑_{n<N} aₙ + φ(N) = 1
  tele : ∀ N → psum a N + Φ (natE N) ≈ 1#
  tele N = trans (tele-ibp a b (λ n → Φ (natE n)) (λ n → AtInterval1.ibp-unit1 n) N)
    (trans (+-cong refl (psum-b0 N)) (trans (+-identityʳ _) Φ0))

  -- φ(N) ≤ ½ᵐ for some N
  gtail : ∀ m → Σ ℕ (λ N → Φ (natE N) ≤ hp m)
  gtail m = N , ≤-trans (negExp-anti (big N le)) (≤-trans (≤-reflexive (sym (*-identityˡ _))) bnd)
    where
    t = T.tail 0 m 2
    N : ℕ
    N = proj₁ t
    le : 2 ℕ.≤ N
    le = proj₁ (proj₂ t)
    bnd : pw 0 (natE N) * negExp (natE N) ≤ hp m
    bnd = proj₂ (proj₂ t)

  sum-a : ∑ᶠ a ≈ 1#
  sum-a = ≤-antisym
    (∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (tele N))))
    (arch (λ m → ≤-trans (≤-reflexive (sym (tele (proj₁ (gtail m)))))
      (+-mono (psum≤∑ᶠ a (proj₁ (gtail m))) (proj₂ (gtail m)))))

  -- ∫₀^∞ x e^{−x²/2} dx = 1
  ∫-xφ : ∫ᴹ {WQ} lebPre (gMomH 1) ≈ 1#
  ∫-xφ = trans (∫ᴹ-leb (gMomH 1)) sum-a
