{-# OPTIONS --safe --without-K #-}

-- Truncated subtraction of cuts, x ∸ t, and the tests x ↦ x ∸ t and x ↦ t ∸ x (plan 03, "Translation and products").
--   * `monus x t` is x − t when t ≤ x and 0 otherwise (`monus-add`, `monus-zero`, `monus-+`);
--   * it respects ≈, is increasing in x and decreasing in t, so `subH t = monoH (_∸ t)` and `rsubH t = antiH (t ∸_)` are
--     tests by `MonoTest`.
-- Route: `LebesgueShiftCut.diffC t b` is b − t for t ⊑ b with t bounded by a rational; take b = x ⊔ t (the union of
-- the two lower cuts), so `monus x t = diffC t (x ⊔ t)`, or any other construction with the stated properties.
--   Skeleton: holes first.
module QBS.Continuous.Monus where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.MonoTest using (module MonoTest)

module Monus (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Weights (lemOf lem₁) using (WQ)
  open MonoTest lem₁ using (monoH; antiH)
  open QBS
  open Hom

  -- x ∸ t
  monus : ∣A∣ → ∣A∣ → ∣A∣
  monus = ?

  monus-cong : ∀ {x x′ t t′} → x ≈ x′ → t ≈ t′ → monus x t ≈ monus x′ t′
  monus-cong = ?

  monus-mono : ∀ {x x′} t → x ≤ x′ → monus x t ≤ monus x′ t
  monus-mono = ?

  monus-anti : ∀ x {t t′} → t ≤ t′ → monus x t′ ≤ monus x t
  monus-anti = ?

  monus-add : ∀ x t → Bnd t → t ≤ x → t + monus x t ≈ x
  monus-add = ?

  monus-zero : ∀ x t → x ≤ t → monus x t ≈ 0#
  monus-zero = ?

  monus-+ : ∀ x t → Bnd t → monus (x + t) t ≈ x
  monus-+ = ?

  -- x ↦ x ∸ t and x ↦ t ∸ x
  subH rsubH : ∣A∣ → Hom S WQ WQ
  subH t = monoH (λ x → monus x t) (λ e → monus-cong e (OmegaSemiring.refl A)) (monus-mono t)
  rsubH t = antiH (λ x → monus t x) (λ e → monus-cong (OmegaSemiring.refl A) e) (monus-anti t)
