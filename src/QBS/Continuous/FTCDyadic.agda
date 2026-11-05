{-# OPTIONS --safe --without-K #-}

-- The fundamental theorem of calculus on every dyadic interval, from `Deriv` data (plan 03, "Change of variables").
-- For G : [0,∞) → [0,∞) and tests h, k with `dv : ∀ N → Deriv (N+1) G h k` (G′ = k − h on every [0, N+1]),
--   `ftc-dy : ∫_{[m/2ⁿ,(m+1)/2ⁿ)} h + G((m+1)/2ⁿ) ≈ G(m/2ⁿ) + ∫_{[m/2ⁿ,(m+1)/2ⁿ)} k`.
-- Route: the rescaled data Gₙ(t) = G(t/2ⁿ), hₙ(t) = h(t/2ⁿ)/2ⁿ, kₙ(t) = k(t/2ⁿ)/2ⁿ satisfy `Deriv (N+1)` too (`dv-resc`,
-- from `Analysis/Deriv.DFaff` with slope ½ⁿ ≤ 1), so `DerivBridge.OnHalfLine.unit m` gives the identity on the unit
-- piece [m, m+1) of Gₙ, in the fair-coin form `J (hₙ ∘ shiftPt m)`.  `piece` turns that into a Lebesgue integral against
-- `χ[m, m+1)` (the only null set is the all-true point, `LebesgueDyadic.fair-top`), and `resc` moves it back to
-- `χ[m/2ⁿ, (m+1)/2ⁿ)` (`LebesgueScale.∫-scale` at c = 2ⁿ, `LebesgueScaleAlg.χIv-scale`).
module QBS.Continuous.FTCDyadic where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc; _^_)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_,_; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.DerivBridge using (module DerivBridge)
open import QBS.Continuous.FTCDyadicPiece using (module FTCDyadicPiece)
open import QBS.Continuous.LebesgueScale using (module LebesgueScale)
open import QBS.Continuous.LebesgueScaleAlg using (module LebesgueScaleAlg)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)

module FTCDyadic (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; *-comm; *-assoc; *-identityʳ;
    *-mono; ≤-trans; ≤-reflexive) renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero) renaming (half+half to hh)
  open AlgDigit A half hh using (dy-dbl; dbl-*2)
  open AlgT A R using (hp≤1)
  open Bounded A using (Bnd)
  open Exp A using (natE)
  open AlgD A R using (Deriv; D-cG; DFaff)
  open Lebesgue (lemOf lem₁) using (J)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift)
  open HalfLineRate lem₁ using (scaleH; ∫-scaleH)
  open ExpDist lem₁ using (idW)
  open Intervals (lemOf lem₁) using (χI; dy; χIv; χIv-cong)
  open DerivBridge lem₁ using (module OnHalfLine)
  open LebesgueScale lem₁ using (∫-scale)
  open LebesgueScaleAlg (lemOf lem₁) using (χIv-scale)
  open LebesgueDyadicAlg (lemOf lem₁) using (bnd-natE)
  module P = FTCDyadicPiece lem₁
  open QBS
  open Hom

  -- ½ⁿ and its inverse 2ⁿ
  hp-inv : ∀ n → natE (2 ^ n) * hp n ≈ 1#
  hp-inv zero = trans (*-cong (OmegaSemiring.+-identityˡ A 1#) refl) (OmegaSemiring.*-identityˡ A 1#)
  hp-inv (suc n) = ≡.subst (λ k → natE k * hp (suc n) ≈ 1#) (≡.trans (dbl-*2 (2 ^ n)) (ℕ.*-comm (2 ^ n) 2))
    (trans (dy-dbl (2 ^ n) n) (hp-inv n))

  -- the dyadic point m/2ⁿ of `Intervals`, as ½ⁿ · m
  hp-dy : ∀ n m → hp n * natE m ≈ dy n m
  hp-dy n m = *-comm (hp n) (natE m)

  -- the rescaled test t ↦ ½ⁿ f(½ⁿ t)
  rescH : ℕ → Hom S WQ WQ → Hom S WQ WQ
  rescH n f = scaleH (hp n) (_∘H_ S f (scaleH (hp n) idW))

  -- the unit piece [j, j+1) of the half-line as a fair-coin integral (the all-true point is null)
  piece : ∀ (f : Hom S WQ WQ) j →
    ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI 0 j)) ≈ J fairCoin (λ r → map f ⟨$⟩ shiftPt j r) (Meas-hshift j f)
  piece = P.piece

  -- 2ⁿ ½ⁿ = 1 in the order used by `∫-scale`, and the dyadic point at the scale 2ⁿ
  hp-inv′ : ∀ n → hp n * natE (2 ^ n) ≈ 1#
  hp-inv′ n = trans (*-comm _ _) (hp-inv n)

  dy-sc : ∀ n m → dy n m * natE (2 ^ n) ≈ dy 0 m
  dy-sc n m = trans (*-assoc (natE m) (hp n) (natE (2 ^ n))) (trans (*-cong refl (hp-inv′ n)) (*-cong refl (sym hp-zero)))

  -- the indicator of [j/2ⁿ, (j+1)/2ⁿ) at ½ⁿ x is that of [j, j+1) at x
  χ-resc : ∀ n j x → map (χI n j) ⟨$⟩ (hp n * x) ≈ map (χI 0 j) ⟨$⟩ x
  χ-resc n j x = trans (χIv-scale (hp n) (natE (2 ^ n)) (dy n j) (dy n (suc j)) x (hp-inv′ n))
    (χIv-cong x (dy-sc n j) (dy-sc n (suc j)))

  -- pointwise: the integrand of the rescaled test on [j, j+1)
  resc-pt : ∀ (f : Hom S WQ WQ) n j x → map (mulH {WQ} (rescH n f) (χI 0 j)) ⟨$⟩ x
    ≈ hp n * (map (mulH {WQ} f (χI n j)) ⟨$⟩ (hp n * x))
  resc-pt f n j x = trans (*-assoc (hp n) _ _) (*-cong refl (*-cong refl (sym (χ-resc n j x))))

  -- rescaling [j, j+1) to [j/2ⁿ, (j+1)/2ⁿ)
  resc : ∀ (f : Hom S WQ WQ) n j → ∫ᴹ {WQ} lebPre (mulH {WQ} (rescH n f) (χI 0 j)) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI n j))
  resc f n j = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} (rescH n f) (χI 0 j)}
      {scaleH (hp n) (_∘H_ S (mulH {WQ} f (χI n j)) (scaleH (hp n) idW))} (resc-pt f n j))
    (trans (∫-scaleH (hp n) (_∘H_ S (mulH {WQ} f (χI n j)) (scaleH (hp n) idW)))
      (∫-scale (hp n) (natE (2 ^ n)) (hp-inv′ n) (1 , ≤-trans (hp≤1 n) (≤-reflexive (sym (OmegaSemiring.+-identityʳ A 1#))))
        (bnd-natE (2 ^ n)) (mulH {WQ} f (χI n j))))

  module _ (G : ∣A∣ → ∣A∣) (h k : Hom S WQ WQ)
           (dv : ∀ N → Deriv (natE (suc N)) G (λ x → map h ⟨$⟩ x) (λ x → map k ⟨$⟩ x)) where

    -- the data of G(t/2ⁿ)
    dv-resc : ∀ n N → Deriv (natE (suc N)) (λ t → G (hp n * t)) (λ x → map (rescH n h) ⟨$⟩ x) (λ x → map (rescH n k) ⟨$⟩ x)
    dv-resc n N = DFaff (hp n) (hp≤1 n) (≤-trans (≤-reflexive (*-comm (hp n) _))
      (≤-trans (*-mono (natE (suc N)) (hp≤1 n)) (≤-reflexive (*-identityʳ _)))) (dv N)

    -- the FTC on [m/2ⁿ, (m+1)/2ⁿ)
    ftc-dy : ∀ n m → ∫ᴹ {WQ} lebPre (mulH {WQ} h (χI n m)) + G (dy n (suc m))
      ≈ G (dy n m) + ∫ᴹ {WQ} lebPre (mulH {WQ} k (χI n m))
    -- G respects ≈
    G-cg : ∀ {x y} → x ≈ y → G x ≈ G y
    G-cg = D-cG (proj₂ (proj₂ (dv 0)))

    -- the integral over the dyadic interval is that of the rescaled test on the unit piece
    int-dy : ∀ (f : Hom S WQ WQ) n m → ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI n m))
      ≈ J fairCoin (λ r → map (rescH n f) ⟨$⟩ shiftPt m r) (Meas-hshift m (rescH n f))
    int-dy f n m = trans (sym (resc f n m)) (piece (rescH n f) m)

    ftc-dy n m = trans (+-cong (int-dy h n m) (sym (G-cg (hp-dy n (suc m)))))
      (trans (OnHalfLine.unit (rescH n h) (rescH n k) (λ t → G (hp n * t)) (dv-resc n) m)
        (+-cong (G-cg (hp-dy n m)) (sym (int-dy k n m))))
