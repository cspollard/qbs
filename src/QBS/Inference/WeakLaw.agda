{-# OPTIONS --safe --without-K #-}

-- Markov's and Chebyshev's inequalities and the weak law of large numbers (plan 05, item 50).  On a probability P on Ω:
--   * `a ≤ᵛ x`: a value a ∈ [0, ∞] below a signed value x, cross-added (a + x⁻ ≤ x⁺); respects `≃` (`≤ᵛ-cong`);
--   * `geW c`, the indicator of [c, ∞] on [0, ∞] (1 when c ≤ x, 0 otherwise), monotone, so a test `geH c`
--     (`MonoTest.monoH`) with no measurability proof;
--   * Markov: c · ∫ χ ≤ ∫ h whenever c χ ≤ h pointwise (`markov`), in particular c · P{h ≥ c} ≤ E h (`markov-ge`);
--   * Chebyshev: for g with E g² finite and any test χ inside {(g − E g)² ≥ e²} (pointwise e² χ ≤ (g − E g)²,
--     cross-added), e² ∫ χ ≤ Var g (`chebyshev`);
--   * the weak law: for F : Fin n → SgT Ω with `SgMoments.Moments P n F μ σ²` and χ inside {(Sₙ − n μ)² ≥ e²},
--     e² ∫ χ ≤ n σ² (`weak-law`, take e = n ε: n² ε² P{|Sₙ − n μ| ≥ n ε} ≤ n σ²), and the rate form
--     n ε² ∫ χ ≤ σ² for χ inside {(Sₙ − n μ)² ≥ (n ε)²}, n ≥ 1 (`weak-law-rate`, P ≤ σ²/(n ε²)).
-- Only the moment hypotheses are used, so the law applies to every iid family (`IID.IID-moments`) and to uncorrelated
-- families.  Events are given by tests χ (a [0, 1]-valued χ is a sub-event); `geH` gives the indicator of {h ≥ c}.
-- Route: `markov` is `SupTest.∫ᴹ-monoX` with `Product.cmul`; `geW` is the cut {q | q < 0, or c ≤ x and q < 1}, with
-- `geW-0` by excluded middle; `chebyshev` is `SignedExpect.Ex-mono` on fromW (e² χ) and (g − E g)², then
-- `SignedVar.Var-cen`; `weak-law` is `chebyshev` at Sₙ with `SgSample.Ex-sum` (centre ≃ n μ, `SignedSq.sq-cong`) and
-- `SgSample.Var-sum`; `weak-law-rate` cancels the finite nonzero factor n (a helper on lower reals).
--   Skeleton: holes first.
module QBS.Inference.WeakLaw where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin)
open import Data.Empty using (⊥)
open import Data.Product.Base using (proj₁)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.MonoTest using (module MonoTest)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SgMoments using (module SgMoments)

module WeakLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#) renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; _≃_; _*S_; nat)
  open Bounded.Sg A using (pos; neg)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open MonoTest lem₁ using (monoH)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _*T_)
  open SignedExpect lem₁ using (Ex)
  open SignedVar lem₁ using (Int₂; Var; cen)
  open SgMoments lem₁ using (natS; sumT; Moments)
  open QBS
  open Hom

  -- a value below a signed value
  infix 4 _≤ᵛ_
  _≤ᵛ_ : ∣A∣ → Sg → Set₁
  a ≤ᵛ x = a + neg x ≤ pos x

  ≤ᵛ-cong : ∀ {a x y} → a ≤ᵛ x → x ≃ y → a ≤ᵛ y
  ≤ᵛ-cong = ?

  -- the indicator of [c, ∞]
  geW : ∣A∣ → ∣A∣ → ∣A∣
  geW = ?

  geW-cong : ∀ c {x y} → x ≈ y → geW c x ≈ geW c y
  geW-cong = ?

  geW-mono : ∀ c {x y} → x ≤ y → geW c x ≤ geW c y
  geW-mono = ?

  geW-1 : ∀ {c x} → c ≤ x → geW c x ≈ 1#
  geW-1 = ?

  geW-0 : ∀ {c x} → (c ≤ x → ⊥) → geW c x ≈ 0#
  geW-0 = ?

  geH : ∣A∣ → Hom S WQ WQ
  geH c = monoH (geW c) (geW-cong c) (geW-mono c)

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- the squared deviation (g − c)²
    dev : SgT Ω → Sg → SgT Ω
    dev g c = cen P g c *T cen P g c

    -- Markov
    markov : ∀ (h χ : Hom S Ω WQ) c → (∀ ω → c * (map χ ⟨$⟩ ω) ≤ map h ⟨$⟩ ω) →
      c * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ ∫ᴹ {Ω} (ιPre {Ω} P) h
    markov = ?

    markov-ge : ∀ (h : Hom S Ω WQ) c → c * ∫ᴹ {Ω} (ιPre {Ω} P) (_∘H_ S (geH c) h) ≤ ∫ᴹ {Ω} (ιPre {Ω} P) h
    markov-ge = ?

    -- Chebyshev
    chebyshev : ∀ (g : SgT Ω) (ij : Int₂ P g) (χ : Hom S Ω WQ) e →
      (∀ ω → (e * e) * (map χ ⟨$⟩ ω) + at⁻ (dev g (Ex {Ω} (ιPre {Ω} P) g (proj₁ ij))) ω
        ≤ at⁺ (dev g (Ex {Ω} (ιPre {Ω} P) g (proj₁ ij))) ω) →
      (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ Var P g ij
    chebyshev = ?

    -- the weak law of large numbers
    weak-law : ∀ n F μ σ² → Moments P n F μ σ² → ∀ (χ : Hom S Ω WQ) e →
      (∀ ω → (e * e) * (map χ ⟨$⟩ ω) + at⁻ (dev (sumT n F) (natS n *S μ)) ω ≤ at⁺ (dev (sumT n F) (natS n *S μ)) ω) →
      (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ natS n *S σ²
    weak-law = ?

    weak-law-rate : ∀ m (F : Fin (suc m) → SgT Ω) μ σ² → Moments P (suc m) F μ σ² → ∀ (χ : Hom S Ω WQ) e →
      (∀ ω → ((nat (suc m) * e) * (nat (suc m) * e)) * (map χ ⟨$⟩ ω) + at⁻ (dev (sumT (suc m) F) (natS (suc m) *S μ)) ω
        ≤ at⁺ (dev (sumT (suc m) F) (natS (suc m) *S μ)) ω) →
      (nat (suc m) * (e * e)) * ∫ᴹ {Ω} (ιPre {Ω} P) χ ≤ᵛ σ²
    weak-law-rate = ?
