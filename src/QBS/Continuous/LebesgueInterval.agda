{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure of every interval, and the characterisation of Lebesgue measure by its interval masses (plan 03,
-- "Uniqueness on the half-line").   No subtraction: "λ[a,b) = b − a" is stated as
-- `a + λ[a,b) ≈ b`.
--   * `leb-Iv`: for cuts a ≤ b with b finite, `a + ∫ lebPre χ[a,b) ≈ b`.  Approximate [a,b) from inside by unions of
--     dyadic intervals (`LebesgueDyadic.leb-χI`) and pass to the limit (`J-⨆`).
--   * `leb-unique`: a measure with these interval masses and no mass at ∞ is Lebesgue measure
--     (`UniquenessWQ.uniqWQ`; the dyadic masses follow by cancelling the finite left endpoint).  This is the tool for
--     scaling, translation and change of variables: compute interval masses only.
module QBS.Continuous.LebesgueInterval where

open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import Data.Product.Base using (_,_)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueIntervalAlg using (module LebesgueIntervalAlg)
open import QBS.Continuous.UniquenessWQ using (module UniquenessWQ)

module LebesgueInterval (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; sym; trans; ≤-trans; ≤-reflexive; *-mono; *-identityʳ; 1#; ≤-refl) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; module C)
  open C using (Pre)
  open HalfLine lem₁ using (lebPre)
  open Intervals (lemOf lem₁) using (χIv; χInf; χI; dy)
  open LebesgueDyadic lem₁ using (leb-χI; leb-inf; leb-fin)
  open LebesgueIntervalAlg (lemOf lem₁) using (Iv-eq)
  open UniquenessWQ (lemOf lem₁) using (uniqWQ)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp; hp-zero; hp-≤)
  open AlgDigit A half hh using (dy-mono)
  open Exp A using (natE)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat)
  open BoundedCancel A half hh using (cancel-bnd)
  open QBS
  open Hom

  hp≤1 : ∀ n → hp n ≤ 1#
  hp≤1 zero = ≤-reflexive hp-zero
  hp≤1 (suc n) = ≤-trans (hp-≤ n) (hp≤1 n)

  -- the dyadic points are bounded
  dy-bnd : ∀ n m → Bnd (dy n m)
  dy-bnd n m = m , ≤-trans (*-mono (natE m) (hp≤1 n)) (≤-trans (≤-reflexive (*-identityʳ (natE m))) (≤-reflexive (natE≈nat m)))

  leb-Iv : ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} lebPre (χIv a b) ≈ b
  leb-Iv = Iv-eq lebPre leb-χI

  leb-unique : ∀ (μ : Pre (XW WQ)) → (∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} μ (χIv a b) ≈ b) →
    ∫ᴹ {WQ} μ χInf ≈ 0# → _≈ᴹ_ {WQ} μ lebPre
  leb-unique μ h hinf = uniqWQ μ lebPre agreeI finI (trans hinf (sym leb-inf))
    where
      agreeI : ∀ n m → ∫ᴹ {WQ} μ (χI n m) ≈ ∫ᴹ {WQ} lebPre (χI n m)
      agreeI n m = cancel-bnd (dy-bnd n m)
        (trans (h (dy n m) (dy n (suc m)) (dy-mono n (ℕ.n≤1+n m)) (dy-bnd n (suc m)))
               (sym (leb-Iv (dy n m) (dy n (suc m)) (dy-mono n (ℕ.n≤1+n m)) (dy-bnd n (suc m)))))
      finI : ∀ k → Bnd (∫ᴹ {WQ} μ (χI 0 k))
      finI k = let (j , le) = leb-fin k in j , ≤-trans (≤-reflexive (agreeI 0 k)) le
