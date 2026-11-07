{-# OPTIONS --safe --without-K #-}

-- Monotone change of variables on the half-line with a derivative certificate.
-- Headline (`push-eq`): the pushforward of Lebesgue measure along ψ is Lebesgue measure with density φ′,
--   `mapM ψ lebPre ≈ reweightPre φ′ lebPre`;  `cov` and `cov-inv` below are its two integral forms (with `∫ᴹ-map`).
-- Scope: only increasing bijections φ of [0,∞] with an inverse ψ are covered.  Decreasing maps (reflection is in
-- `RealScale`) and non-surjective φ have no change-of-variables theorem here.
-- Data: an increasing bijection φ of [0,∞] with inverse ψ (both morphisms; `gc-to`, `gc-from`: a ≤ ψ y ↔ φ a ≤ y, and
-- `φψ : φ (ψ y) ≈ y`), ψ finite on finite points, and a derivative φ′ with `dv : ∀ N → Deriv (N+1) φ 0 φ′`.  Then
--   `cov : ∫ g(φ x) φ′(x) dx ≈ ∫ g(y) dy`   for every test g,
-- and `cov-inv : ∫ h(ψ y) dy ≈ ∫ h(x) φ′(x) dx`.  Route: the pushforward `lebψ = mapM ψ lebPre` and the reweighted
-- `lebφ′ = reweightPre φ′ lebPre` are equal (`push-eq`, `UniquenessWQ.uniqWQ`):
--   * on a dyadic interval [d, d′): lebψ gives it φ d′ − φ d (`χIv-ψ`, then `LebesgueInterval.leb-Iv` at φ d ≤ φ d′), and
--     so does lebφ′ (`FTCDyadic.ftc-dy` with h = 0); cancel the finite φ d (`agreeI`);
--   * lebψ is finite on [k, k+1) (`finI`), and neither measure charges ∞ (`χInf-ψ`, `LebesgueDyadic.leb-inf`).
-- No interval FTC at non-dyadic points is needed: the arbitrary endpoints φ d are handled by `leb-Iv`.
module QBS.Continuous.ChangeOfVariables where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.FTCDyadic using (module FTCDyadic)
open import QBS.Continuous.LebesgueInterval using (module LebesgueInterval)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.UniquenessWQ using (module UniquenessWQ)
open import QBS.Continuous.ChangeOfVariablesAlg using (module ChangeOfVariablesAlg)

module ChangeOfVariables (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; ≤-trans; ≤-reflexive; ≤-refl; ≤-antisym;
    0-least; zeroˡ; +-identityˡ; ≤-+ʳ) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd; nat; nat-+)
  open AlgD A R using (Deriv; DFresp; D-bG)
  open AlgT A R using (P)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; ∫ᴹ-map; ∫ᴹ-cong; module C)
  open C using (Pre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (χIv; χInf; χI; dy)
  open FTCDyadic lem₁ using (ftc-dy)
  open LebesgueInterval lem₁ using (leb-Iv; dy-bnd)
  open LebesgueDyadic lem₁ using (leb-inf)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat; natE-mono)
  open LebesgueIntervalAlg (lemOf lem₁) using (∫ᴹ-zero′)
  open UniquenessWQ (lemOf lem₁) using (uniqWQ)
  open ChangeOfVariablesAlg lem₁ using (inf-null; module Pull)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open AlgDigit A half hh using (dy-mono)
  open BoundedCancel A half hh using (cancel-bnd)
  open QBS
  open Hom

  bnd-P : ∀ j → Bnd (P j)
  bnd-P ℕ.zero = 1 , ≤-reflexive (sym (OmegaSemiring.+-identityʳ A 1#))
  bnd-P (suc j) = let (n , h) = bnd-P j in n ℕ.+ n , ≤-trans (OmegaSemiring.+-mono A h h) (≤-reflexive (sym (nat-+ n n)))

  -- a summand of a bounded sum is bounded
  bnd-tail : ∀ a {x b} → Bnd b → a + x ≈ b → Bnd x
  bnd-tail a {x} (j , bj) e = j , ≤-trans (≤-+ʳ {x} {a}) (≤-trans (≤-reflexive (trans (OmegaSemiring.+-comm A x a) e)) bj)

  module _ (φ ψ φ′ : Hom S WQ WQ)
           (dv : ∀ N → Deriv (natE (suc N)) (λ x → map φ ⟨$⟩ x) (λ _ → 0#) (λ x → map φ′ ⟨$⟩ x))
           (gc-to : ∀ a y → a ≤ map ψ ⟨$⟩ y → map φ ⟨$⟩ a ≤ y)
           (gc-from : ∀ a y → map φ ⟨$⟩ a ≤ y → a ≤ map ψ ⟨$⟩ y)
           (φψ : ∀ y → map φ ⟨$⟩ (map ψ ⟨$⟩ y) ≈ y)
           (ψ-fin : ∀ y → Bnd y → Bnd (map ψ ⟨$⟩ y)) where

    Φ : ∣A∣ → ∣A∣
    Φ x = map φ ⟨$⟩ x

    module PL = Pull Φ (λ y → map ψ ⟨$⟩ y) gc-to gc-from

    le-M : ∀ a m → a ≤ nat m → a ≤ natE (suc m)
    le-M a m am = ≤-trans am (≤-trans (≤-reflexive (sym (natE≈nat m))) (natE-mono (ℕ.n≤1+n m)))

    -- the certificate bounds Φ on [0, M]
    bnd-cert : ∀ {a m} → Deriv (natE (suc m)) Φ (λ _ → 0#) (λ x → map φ′ ⟨$⟩ x) → a ≤ natE (suc m) → Bnd (Φ a)
    bnd-cert (c , (j , cP) , d) le = let (n , h) = bnd-P j in n , ≤-trans (D-bG d le) (≤-trans cP h)

    -- φ is monotone, sends 0 to 0 and finite points to finite points
    Φ-mono : ∀ a b → a ≤ b → Φ a ≤ Φ b
    Φ-mono a b ab = gc-to a (Φ b) (≤-trans ab (gc-from b (Φ b) ≤-refl))

    Φ-zero : Φ 0# ≈ 0#
    Φ-zero = ≤-antisym (gc-to 0# 0# 0-least) 0-least

    Φ-fin : ∀ a → Bnd a → Bnd (Φ a)
    Φ-fin a (m , am) = bnd-cert (dv m) (le-M a m am)

    -- ψ pulls intervals back to intervals, and ∞ back to ∞
    χIv-ψ : ∀ a b y → map (χIv a b) ⟨$⟩ (map ψ ⟨$⟩ y) ≈ map (χIv (Φ a) (Φ b)) ⟨$⟩ y
    χIv-ψ = PL.χIv-pull

    χInf-ψ : ∀ y → map χInf ⟨$⟩ (map ψ ⟨$⟩ y) ≈ map χInf ⟨$⟩ y
    χInf-ψ = PL.χInf-pull Φ-fin ψ-fin

    -- the two measures on the source side
    lebψ : Pre (XW WQ)
    lebψ = mapM {WQ} {WQ} ψ lebPre

    lebφ′ : Pre (XW WQ)
    lebφ′ = reweightPre {WQ} φ′ lebPre

    int-ψ : ∀ a b → ∫ᴹ {WQ} lebψ (χIv a b) ≈ ∫ᴹ {WQ} lebPre (χIv (Φ a) (Φ b))
    int-ψ a b = trans (∫ᴹ-map {WQ} {WQ} ψ lebPre (χIv a b))
      (∫ᴹ-cong {WQ} lebPre {_∘H_ S (χIv a b) ψ} {χIv (Φ a) (Φ b)} (χIv-ψ a b))

    zero-int : ∀ f → ∫ᴹ {WQ} lebPre (mulH {WQ} (constW {WQ} 0#) f) ≈ 0#
    zero-int f = ∫ᴹ-zero′ lebPre (mulH {WQ} (constW {WQ} 0#) f) (λ x → zeroˡ _)

    dv′ : ∀ N → Deriv (natE (suc N)) Φ (λ x → map (constW {WQ} 0#) ⟨$⟩ x) (λ x → map φ′ ⟨$⟩ x)
    dv′ N = DFresp (λ _ → refl) (λ _ → refl) (λ _ → refl) (dv N)

    -- interval masses
    massψ : ∀ a b → a ≤ b → Bnd b → Φ a + ∫ᴹ {WQ} lebψ (χIv a b) ≈ Φ b
    massψ a b ab bb = trans (+-cong refl (int-ψ a b)) (leb-Iv (Φ a) (Φ b) (Φ-mono a b ab) (Φ-fin b bb))

    massφ′ : ∀ n m → Φ (dy n m) + ∫ᴹ {WQ} lebφ′ (χI n m) ≈ Φ (dy n (suc m))
    massφ′ n m = trans (+-cong refl (∫ᴹ-reweight {WQ} φ′ lebPre (χI n m)))
      (trans (sym (ftc-dy Φ (constW {WQ} 0#) φ′ dv′ n m)) (trans (+-cong (zero-int (χI n m)) refl) (+-identityˡ _)))

    -- the hypotheses of `uniqWQ`
    agreeI : ∀ n m → ∫ᴹ {WQ} lebψ (χI n m) ≈ ∫ᴹ {WQ} lebφ′ (χI n m)
    agreeI n m = cancel-bnd (Φ-fin (dy n m) (dy-bnd n m)) (trans (massψ (dy n m) (dy n (suc m))
      (dy-mono n (ℕ.n≤1+n m)) (dy-bnd n (suc m))) (sym (massφ′ n m)))

    finI : ∀ k → Bnd (∫ᴹ {WQ} lebψ (χI 0 k))
    finI k = bnd-tail (Φ (dy 0 k)) (Φ-fin (dy 0 (suc k)) (dy-bnd 0 (suc k)))
      (massψ (dy 0 k) (dy 0 (suc k)) (dy-mono 0 (ℕ.n≤1+n k)) (dy-bnd 0 (suc k)))

    inf-ψ : ∫ᴹ {WQ} lebψ χInf ≈ 0#
    inf-ψ = trans (∫ᴹ-map {WQ} {WQ} ψ lebPre χInf) (trans (∫ᴹ-cong {WQ} lebPre {_∘H_ S χInf ψ} {χInf} χInf-ψ) leb-inf)

    inf-φ′ : ∫ᴹ {WQ} lebφ′ χInf ≈ 0#
    inf-φ′ = trans (∫ᴹ-reweight {WQ} φ′ lebPre χInf) (inf-null φ′)

    push-eq : _≈ᴹ_ {WQ} lebψ lebφ′
    push-eq = uniqWQ lebψ lebφ′ agreeI finI (trans inf-ψ (sym inf-φ′))

    -- the change of variables, both ways round
    cov-inv : ∀ (h : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (_∘H_ S h ψ) ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} φ′ h)
    cov-inv h = trans (sym (∫ᴹ-map {WQ} {WQ} ψ lebPre h)) (trans (push-eq h) (∫ᴹ-reweight {WQ} φ′ lebPre h))

    cov : ∀ (g : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} φ′ (_∘H_ S g φ)) ≈ ∫ᴹ {WQ} lebPre g
    cov g = trans (sym (cov-inv (_∘H_ S g φ))) (∫ᴹ-cong {WQ} lebPre {_∘H_ S (_∘H_ S g φ) ψ} {g}
      (λ y → Func.cong (map g) (φψ y)))
