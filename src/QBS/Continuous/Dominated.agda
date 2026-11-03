{-# OPTIONS --safe --without-K #-}

-- Dominated convergence for tests on any X (plan 03, "Dominated convergence").
--   * `Conv a l`: a sequence of values converges to l when lim inf a ≈ l ≈ lim sup a (convergence in [0, ∞]);
--   * `dct`: if h n → f pointwise and every h n ≤ g with ∫ g finite, then ∫ h n → ∫ f;
--   * `mct-conv`: an increasing sequence of tests has ∫ h n → ∫ ⋃ h (no domination needed);
--   * `dct-prob`: under a probability measure (`ιPre`), uniformly bounded h n → f gives E h n → E f.
-- Route: `dct` chains lim sup ∫ h ≤ ∫ lim sup h ≤ ∫ f ≤ ∫ lim inf h ≤ lim inf ∫ h ≤ lim sup ∫ h (`Fatou.rev-fatou`,
-- `SupTest.∫ᴹ-monoX` with `liminfH-pt`/`limsupH-pt`, `Fatou.fatou`, `LowerRealsInf.liminf-limsup`); `mct-conv` from
-- `SupTest.∫ᴹ-sup` (for increasing a, lim inf a ≈ lim sup a ≈ ⋃ a); `dct-prob` is `dct` with g constant (the
-- integral of a constant c is c times the mass 1).
--   Skeleton: holes first.
module QBS.Continuous.Dominated where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (unionC)
open import QBS.Analysis.LowerRealsInf using (liminfC; limsupC)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SupTest using (module SupTest)

module Dominated (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SupTest (lemOf lem₁) using (supH)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  -- convergence in [0, ∞]
  Conv : (ℕ → ∣A∣) → ∣A∣ → Set₁
  Conv a l = liminfC a ≈ l × limsupC a ≈ l

  module _ {X : QBS S} where

    dct : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) (f g : Hom S X WQ) →
      (∀ x → Conv (λ n → map (h n) ⟨$⟩ x) (map f ⟨$⟩ x)) →
      (∀ n x → map (h n) ⟨$⟩ x ≤ map g ⟨$⟩ x) → Bnd (∫ᴹ {X} p g) →
      Conv (λ n → ∫ᴹ {X} p (h n)) (∫ᴹ {X} p f)
    dct = ?

    mct-conv : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → (∀ n x → map (h n) ⟨$⟩ x ≤ map (h (suc n)) ⟨$⟩ x) →
      Conv (λ n → ∫ᴹ {X} p (h n)) (∫ᴹ {X} p (supH h))
    mct-conv = ?

    dct-prob : ∀ (P : Pre X) (h : ℕ → Hom S X WQ) (f : Hom S X WQ) N →
      (∀ x → Conv (λ n → map (h n) ⟨$⟩ x) (map f ⟨$⟩ x)) → (∀ n x → map (h n) ⟨$⟩ x ≤ nat N) →
      Conv (λ n → ∫ᴹ {X} (ιPre {X} P) (h n)) (∫ᴹ {X} (ιPre {X} P) f)
    dct-prob = ?
