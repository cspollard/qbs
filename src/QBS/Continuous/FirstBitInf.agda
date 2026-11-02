{-# OPTIONS --safe --without-K #-}

-- The first-bit split of the fair coin for unbounded measurable tests (`Continuous/FirstBit` has it for bounded `Fun`s):
--   J fairCoin φ ≈ ½ J fairCoin (φ ∘ (true ::)) + ½ J fairCoin (φ ∘ (false ::))
-- for every `Meas φ`.  Each truncation `2ᵏ ∫ min(φ, 2ᵏ)/2ᵏ` splits by `FirstBit.firstBit-fun`, and the supremum of the
-- mixtures is the mixture of the suprema (`DyadicAlg.⨆-mix`).
module QBS.Continuous.FirstBitInf where

open import Data.Bool.Base using (Bool; true; false)

open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)

module FirstBitInf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-def; FunInf-Meas; Iinf; Iseq; Iseq-inc; pw)
  open OmegaSemiring A using (_≈_; _+_; _*_; refl; sym; trans; +-cong; *-cong)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Integration A using (I; I-cong)
  open Measurable A using (Fun-pre)
  open Meas (lemOf lem₁) using (Meas; Meas-pre)
  open AlgDy A half hh using (⨆-mix; mix-scale)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)

  -- the test precomposed with `true ::` / `false ::` is measurable
  mp : ∀ b {φ} → Meas φ → Meas (λ x → φ (consR b x))
  mp b mφ = Meas-pre mφ (measurable-cons b)

  -- the k-th truncation splits
  Iseq-split : ∀ {φ} (mφ : Meas φ) k → Iseq fairCoin φ (FunInf-Meas mφ) k ≈
    half * Iseq fairCoin (λ x → φ (consR true x)) (FunInf-Meas (mp true mφ)) k
    + half * Iseq fairCoin (λ x → φ (consR false x)) (FunInf-Meas (mp false mφ)) k
  Iseq-split {φ} mφ k = trans (*-cong refl split) (mix-scale (pw k) _ _)
    where
      f = FunInf-Meas mφ
      split = trans (firstBit-fun (f k))
        (+-cong (*-cong refl (I-cong fairCoin (λ _ → refl) (Fun-pre {f = consR true} (f k) (measurable-cons true))
                                   (FunInf-Meas (mp true mφ) k)))
                (*-cong refl (I-cong fairCoin (λ _ → refl) (Fun-pre {f = consR false} (f k) (measurable-cons false))
                                   (FunInf-Meas (mp false mφ) k))))

  -- ∫ φ = ½ ∫ φ(true :: ·) + ½ ∫ φ(false :: ·)
  firstBit-J : ∀ {φ} (mφ : Meas φ) →
    J fairCoin φ mφ ≈
      half * J fairCoin (λ x → φ (consR true x)) (mp true mφ) + half * J fairCoin (λ x → φ (consR false x)) (mp false mφ)
  firstBit-J {φ} mφ = trans (J-def fairCoin mφ)
    (trans (⨆-mix (Iseq-inc fairCoin φ (FunInf-Meas mφ)) (Iseq-inc fairCoin _ (FunInf-Meas (mp true mφ)))
                  (Iseq-inc fairCoin _ (FunInf-Meas (mp false mφ))) (Iseq-split mφ))
      (+-cong (*-cong refl (sym (J-def fairCoin (mp true mφ)))) (*-cong refl (sym (J-def fairCoin (mp false mφ))))))
