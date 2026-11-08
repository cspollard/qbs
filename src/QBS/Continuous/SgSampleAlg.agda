{-# OPTIONS --safe --without-K #-}

-- Pointwise identities for sums of products of signed tests (used by `SgSample`).
--   * `dist-eq`, `dist-sums`: h (g + s) ≐ h g + h s, and the sums of the parts agree pointwise;
--   * `zero-eq`, `zero-sums`: h · 0 ≐ 0.
-- Route: parts of signed operations are polynomials in the parts (as in `IndepAlg`), so each is one solver call in
-- `SgSampleRing`, transported by `SignedVarAlg.via-cross` and `via-sums`.
module QBS.Continuous.SgSampleAlg where

import Relation.Binary.PropositionalEquality as ≡
open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import Data.Product.Base using (_,_)
open import QBS.Continuous.SignedVarRing using (module Ring)
open import QBS.Continuous.SgSampleRing using (module DRing)

module SgSampleAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; 0#; commutativeSemiring)
  open Bounded A using (0S)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _≐_; _+T_; _*T_; constT)
  open SignedVarAlg lem₁ using (via-cross; via-sums; ⟦_⟧)
  open Ring commutativeSemiring using (_⊗ᵃ_)
  open DRing commutativeSemiring using (DLᵃ; DRᵃ; dist-cross; zero-cross)
    renaming (dist-sums to dist-sumsᵃ; zero-sums to zero-sumsᵃ)

  dist-eq : ∀ {X : QBS S} (h g s : SgT X) → h *T (g +T s) ≐ (h *T g) +T (h *T s)
  dist-eq h g s x = via-cross {F = h *T (g +T s)} {G = (h *T g) +T (h *T s)}
    {P = DLᵃ (⟦ h ⟧ x) (⟦ g ⟧ x) (⟦ s ⟧ x)} {Q = DRᵃ (⟦ h ⟧ x) (⟦ g ⟧ x) (⟦ s ⟧ x)} ≡.refl ≡.refl
    (dist-cross (at⁺ h x) (at⁻ h x) (at⁺ g x) (at⁻ g x) (at⁺ s x) (at⁻ s x))

  dist-sums : ∀ {X : QBS S} (h g s : SgT X) x → at⁺ (h *T (g +T s)) x + at⁻ (h *T (g +T s)) x
    ≈ at⁺ ((h *T g) +T (h *T s)) x + at⁻ ((h *T g) +T (h *T s)) x
  dist-sums h g s x = via-sums {F = h *T (g +T s)} {G = (h *T g) +T (h *T s)}
    {P = DLᵃ (⟦ h ⟧ x) (⟦ g ⟧ x) (⟦ s ⟧ x)} {Q = DRᵃ (⟦ h ⟧ x) (⟦ g ⟧ x) (⟦ s ⟧ x)} ≡.refl ≡.refl
    (dist-sumsᵃ (at⁺ h x) (at⁻ h x) (at⁺ g x) (at⁻ g x) (at⁺ s x) (at⁻ s x))

  zero-eq : ∀ {X : QBS S} (h : SgT X) → h *T constT {X} 0S ≐ constT {X} 0S
  zero-eq {X} h x = via-cross {F = h *T constT {X} 0S} {G = constT {X} 0S}
    {P = ⟦ h ⟧ x ⊗ᵃ (0# , 0#)} {Q = (0# , 0#)} ≡.refl ≡.refl (zero-cross (at⁺ h x) (at⁻ h x))

  zero-sums : ∀ {X : QBS S} (h : SgT X) x → at⁺ (h *T constT {X} 0S) x + at⁻ (h *T constT {X} 0S) x
    ≈ at⁺ (constT {X} 0S) x + at⁻ (constT {X} 0S) x
  zero-sums {X} h x = via-sums {F = h *T constT {X} 0S} {G = constT {X} 0S}
    {P = ⟦ h ⟧ x ⊗ᵃ (0# , 0#)} {Q = (0# , 0#)} ≡.refl ≡.refl (zero-sumsᵃ (at⁺ h x) (at⁻ h x))
