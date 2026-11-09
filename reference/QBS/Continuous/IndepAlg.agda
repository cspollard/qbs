{-# OPTIONS --safe --without-K #-}

-- Pointwise and ring identities for the variance of a sum of two signed tests (helper for `Independence`).
--   * `sqadd-eq`, `sqadd-sums`: (f + g)² ≐ (f² + f g) + (f g + g²), and the sums of the parts agree pointwise;
--   * `R-var`: ((e₁ + m) + (m + e₂)) − (a + b)² ≃ (e₁ − a²) + (e₂ − b²) when m = a b, in the signed ring.
-- Route: parts of signed operations are polynomials in the parts (as in `SignedVarAlg`), so each identity is one solver
-- call in `IndepRing`, transported by `SignedVarAlg.via-cross`, `via-sums` and `fromCross`.
module QBS.Continuous.IndepAlg where

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
open import QBS.Continuous.IndepRing using (module IRing)

module IndepAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; commutativeSemiring)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_)
  open Sg
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _≐_; _+T_; _*T_)
  open SignedVarAlg lem₁ using (fromCross; via-cross; via-sums; ⟦_⟧)
  open IRing commutativeSemiring using (SAᵃ; SA′ᵃ; sa-cross; sa-sums; VLᵃ; VRᵃ; var-cross)

  sqadd-eq : ∀ {X : QBS S} (f g : SgT X) → (f +T g) *T (f +T g) ≐ ((f *T f) +T (f *T g)) +T ((f *T g) +T (g *T g))
  sqadd-eq f g x = via-cross {F = (f +T g) *T (f +T g)} {G = ((f *T f) +T (f *T g)) +T ((f *T g) +T (g *T g))}
    {P = SAᵃ (⟦ f ⟧ x) (⟦ g ⟧ x)} {Q = SA′ᵃ (⟦ f ⟧ x) (⟦ g ⟧ x)} ≡.refl ≡.refl
    (sa-cross (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x))

  sqadd-sums : ∀ {X : QBS S} (f g : SgT X) x → at⁺ ((f +T g) *T (f +T g)) x + at⁻ ((f +T g) *T (f +T g)) x
    ≈ at⁺ (((f *T f) +T (f *T g)) +T ((f *T g) +T (g *T g))) x + at⁻ (((f *T f) +T (f *T g)) +T ((f *T g) +T (g *T g))) x
  sqadd-sums f g x = via-sums {F = (f +T g) *T (f +T g)} {G = ((f *T f) +T (f *T g)) +T ((f *T g) +T (g *T g))}
    {P = SAᵃ (⟦ f ⟧ x) (⟦ g ⟧ x)} {Q = SA′ᵃ (⟦ f ⟧ x) (⟦ g ⟧ x)} ≡.refl ≡.refl
    (sa-sums (at⁺ f x) (at⁻ f x) (at⁺ g x) (at⁻ g x))

  R-var : ∀ e₁ e₂ a b → ((e₁ +S (a *S b)) +S ((a *S b) +S e₂)) +S -S ((a +S b) *S (a +S b)) ≃
    (e₁ +S -S (a *S a)) +S (e₂ +S -S (b *S b))
  R-var e₁ e₂ a b = fromCross (var-cross (pos e₁) (neg e₁) (pos e₂) (neg e₂) (pos a) (neg a) (pos b) (neg b))
