{-# OPTIONS --safe --without-K #-}

-- Downward monotone convergence and Fatou's lemma in both directions, for tests on any X (plan 03, "Dominated
-- convergence").
--   * `∫ᴹ-inf`: for a decreasing sequence h with ∫ h 0 finite, ∫ ⋂ₙ h n ≈ ⋂ₙ ∫ h n;
--   * `fatou`: ∫ lim inf h ≤ lim inf ∫ h;
--   * `rev-fatou`: if every h n ≤ g with ∫ g finite, lim sup ∫ h ≤ ∫ lim sup h.
-- Route for `∫ᴹ-inf`, by truncation (no pointwise finiteness of h 0 is assumed, so h 0 may be ∞ on a null set):
--   1. `∫ᴹ-inf-fin`: the case h 0 ≤ N pointwise.  Pointwise h 0 ≈ h n + (h 0 ∸ h n) (`Monus.monus-add`, h n x ≤ N is
--      bounded); the differences increase, so `SupTest.∫ᴹ-sup` gives ∫ h 0 ≈ ∫ ⋂ h + ⋃ₙ ∫ (h 0 ∸ h n), and
--      ∫ h 0 ≈ ∫ h n + ∫ (h 0 ∸ h n); cancel the finite ∫ h 0 terms (`BoundedCancel.cancel-bnd`).
--   2. `minH N f = f ⊓ N` (`LowerRealsMin._⊓_`); `min-split`: f ≈ (f ⊓ N) + (f ∸ N) pointwise, so ∫ h n ≤
--      ∫ (h n ⊓ N) + ∫ (h 0 ∸ N).
--   3. `tail-small`: ∫ (f ∸ N) gets below every ½ᵏ for finite ∫ f (∫ (f ⊓ N) increases to ∫ f by `∫ᴹ-sup` and
--      `LowerRealsMin.min-sup`; a finite lower real is approached from below, by excluded middle).
--   4. ⋂ ∫ h n ≤ ∫ ⋂ (h ⊓ N) + ½ᵏ ≤ ∫ ⋂ h + ½ᵏ for every k (`approx`), hence ≤ ∫ ⋂ h; the other direction is
--      monotonicity.
-- `fatou`: n ↦ ⋂ₖ h (n + k) increases, so `∫ᴹ-sup`, then ∫ ⋂ₖ h (n + k) ≤ ⋂ₖ ∫ h (n + k) by monotonicity.
-- `rev-fatou`: n ↦ ⋃ₖ h (n + k) decreases and is ≤ g, so `∫ᴹ-inf`, then ⋃ₖ ∫ h (n + k) ≤ ∫ ⋃ₖ h (n + k).
--   Skeleton: holes first.
module QBS.Continuous.Fatou where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (unionC)
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LowerRealsInf using (interC; liminfC; limsupC)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SupTest using (module SupTest)
open import QBS.Continuous.Monus using (module Monus)

module Fatou (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SupTest (lemOf lem₁) using (supH; infH; liminfH; limsupH)
  open Monus lem₁ using (monus)
  open QBS
  open Hom

  module _ {X : QBS S} where

    Decr : (ℕ → Hom S X WQ) → Set₁
    Decr h = ∀ n x → map (h (suc n)) ⟨$⟩ x ≤ map (h n) ⟨$⟩ x

    -- x ↦ f x ⊓ N
    minH : ℕ → Hom S X WQ → Hom S X WQ
    minH = ?

    minH-pt : ∀ N f x → map (minH N f) ⟨$⟩ x ≈ (map f ⟨$⟩ x) ⊓ nat N
    minH-pt = ?

    -- a ≤ b + ½ᵏ for every k gives a ≤ b
    approx : ∀ {a b} → (∀ k → a ≤ b + hp k) → a ≤ b
    approx = ?

    ∫ᴹ-inf-fin : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) N → Decr h → (∀ x → map (h 0) ⟨$⟩ x ≤ nat N) →
      Bnd (∫ᴹ {X} p (h 0)) → ∫ᴹ {X} p (infH h) ≈ interC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-inf-fin = ?

    tail-small : ∀ (p : C.Pre (XW X)) (f : Hom S X WQ) → Bnd (∫ᴹ {X} p f) →
      ∀ k → Σ ℕ (λ N → ∫ᴹ {X} p f ≤ ∫ᴹ {X} p (minH N f) + hp k)
    tail-small = ?

    -- downward monotone convergence
    ∫ᴹ-inf : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → Decr h → Bnd (∫ᴹ {X} p (h 0)) →
      ∫ᴹ {X} p (infH h) ≈ interC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-inf = ?

    -- Fatou's lemma and its reverse
    fatou : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → ∫ᴹ {X} p (liminfH h) ≤ liminfC (λ n → ∫ᴹ {X} p (h n))
    fatou = ?

    rev-fatou : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) (g : Hom S X WQ) →
      (∀ n x → map (h n) ⟨$⟩ x ≤ map g ⟨$⟩ x) → Bnd (∫ᴹ {X} p g) →
      limsupC (λ n → ∫ᴹ {X} p (h n)) ≤ ∫ᴹ {X} p (limsupH h)
    rev-fatou = ?
