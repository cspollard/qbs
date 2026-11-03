{-# OPTIONS --safe --without-K #-}

-- Dominated convergence for signed tests (plan 03, "Signed dominated convergence").  A signed test is a pair (h⁺, h⁻)
-- standing for h⁺ − h⁻, and its expectation the pair of integrals (`SignedIntegral`, `ExpectationInt.E-atᴵ`).
--   * `dct-signed`: if h⁺ n − h⁻ n → f⁺ − f⁻ pointwise wherever g is finite (`ConvEps.SConv`), with h⁺ n + h⁻ n ≤ g,
--     f⁺ + f⁻ ≤ g and ∫ g finite, then ∫ h⁺ n − ∫ h⁻ n → ∫ f⁺ − ∫ f⁻;
--   * `dct-signed-prob`: under a probability measure, with a uniform bound N in place of g.
-- Route: d n = h⁺ n + f⁻ and e n = h⁻ n + f⁺ (`FatouAux.addX`), cut to where g is finite (`NullInf.finχ`, so values are
-- pointwise bounded); `pn n = d n ∸ e n`, `qn n = e n ∸ d n` (`FatouAux.monusH`).  Pointwise d n + qn n ≈ e n + pn n
-- (`Monus.monus-add`/`monus-zero`, excluded middle on d ≤ e), pn n, qn n → 0 pointwise, dominated by g + g, so
-- ∫ pn n, ∫ qn n → 0 (`Dominated.dct`, `ConvEps.conv-econv`).  Integrate, drop the cut (`NullInf.∫-fin-cut`), and
-- rearrange with `ConvEps.sconv-shift`.
--   Skeleton: holes first.
module QBS.Continuous.DominatedSigned where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ConvEps using (module ConvEps)

module DominatedSigned (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _≤_; _+_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open ConvEps lem₁ using (SConv)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open QBS
  open Hom

  module _ {X : QBS S} where

    dct-signed : ∀ (p : C.Pre (XW X)) (h⁺ h⁻ : ℕ → Hom S X WQ) (f⁺ f⁻ g : Hom S X WQ) →
      (∀ x → BndQ (map g ⟨$⟩ x) →
        SConv (λ n → map (h⁺ n) ⟨$⟩ x) (λ n → map (h⁻ n) ⟨$⟩ x) (map f⁺ ⟨$⟩ x) (map f⁻ ⟨$⟩ x)) →
      (∀ n x → (map (h⁺ n) ⟨$⟩ x) + (map (h⁻ n) ⟨$⟩ x) ≤ (map g ⟨$⟩ x)) →
      (∀ x → (map f⁺ ⟨$⟩ x) + (map f⁻ ⟨$⟩ x) ≤ (map g ⟨$⟩ x)) →
      Bnd (∫ᴹ {X} p g) →
      SConv (λ n → ∫ᴹ {X} p (h⁺ n)) (λ n → ∫ᴹ {X} p (h⁻ n)) (∫ᴹ {X} p f⁺) (∫ᴹ {X} p f⁻)
    dct-signed = ?

    dct-signed-prob : ∀ (P : Pre X) (h⁺ h⁻ : ℕ → Hom S X WQ) (f⁺ f⁻ : Hom S X WQ) N →
      (∀ x → SConv (λ n → map (h⁺ n) ⟨$⟩ x) (λ n → map (h⁻ n) ⟨$⟩ x) (map f⁺ ⟨$⟩ x) (map f⁻ ⟨$⟩ x)) →
      (∀ n x → (map (h⁺ n) ⟨$⟩ x) + (map (h⁻ n) ⟨$⟩ x) ≤ nat N) → (∀ x → (map f⁺ ⟨$⟩ x) + (map f⁻ ⟨$⟩ x) ≤ nat N) →
      SConv (λ n → ∫ᴹ {X} (ιPre {X} P) (h⁺ n)) (λ n → ∫ᴹ {X} (ιPre {X} P) (h⁻ n))
        (∫ᴹ {X} (ιPre {X} P) f⁺) (∫ᴹ {X} (ιPre {X} P) f⁻)
    dct-signed-prob = ?
