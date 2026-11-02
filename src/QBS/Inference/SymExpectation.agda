{-# OPTIONS --safe --without-K #-}

-- Expectations under a symmetric density on the real line `RQ` (`Continuous/RealDensity`), through the expectation API of
-- `Inference/ExpectationInt`.  In `module SymE d c hc n nn` (the density `[d , d]`, `∫ᴹ lebPre d ≈ c`, `(c + c) · n ≈ 1#`),
-- write `RH g = n · (∫ᴹ lebPre (d · g∘inl) + ∫ᴹ lebPre (d · g∘inr))`.  For two non-negative parts `g⁺ g⁻ : RQ ⇒ WQ`:
--   * `symI g⁺ g⁻ b⁺ b⁻ : ITest symDist`, given `Bnd (RH g⁺)` and `Bnd (RH g⁻)`;
--   * `E-atᴵ-sym : E-atᴵ symDist (symI …) ≃ (RH g⁺ − RH g⁻)`;
--   * the symmetry lemma: if `g⁺ (inl x) ≈ g⁻ (inr x)` and `g⁺ (inr x) ≈ g⁻ (inl x)` (the statistic is odd) then
--     `RH g⁺ ≈ RH g⁻` (`RH-odd`) and `E-atᴵ-odd : E-atᴵ symDist (symI …) ≃ 0`, whatever the density `d` and the value of `c`;
--   * `E-atᴵ-≈`: the expectation of any `ITest p` is `(a − b)` for `a`, `b` the pulled-back integrals of the parts (generic in `p`);
--   * `≃-≈ : a ≈ c → b ≈ d → (a − b) ≃ (c − d)`, to read off values.
module QBS.Inference.SymExpectation where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealDensity using (module RealDensity)
import QBS.Inference.ExpectationInt as EI

module SymExpectation (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; +-comm; +-identityʳ; +-identityˡ)
  open Bounded A using (Bnd; finite; _≃_; mk≃; ≃-trans; _−_[_,_])
  open SubSemiring using (Is-resp; Is-0)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open RealLine lem₁ using (RQ; inlH; inrH)
  open RealDensity lem₁ using (toR; module Sym)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open Hom

  -- reading off values
  ≃-≈ : ∀ {a b c d} {pa : Bnd a} {pb : Bnd b} {pc : Bnd c} {pd : Bnd d} → a ≈ c → b ≈ d →
    (a − b [ pa , pb ]) ≃ (c − d [ pc , pd ])
  ≃-≈ ea eb = mk≃ 0# (Is-0 finite) (+-cong (+-cong ea (sym eb)) refl)

  -- the expectation is the signed value of the two pulled-back integrals (generic in the measure)
  E-atᴵ-≈ : ∀ {X : QBS S} (p : Pre X) (t : ITest p) {a b} →
    J (m p) (λ r → map (pos t) ⟨$⟩ (α p ⟨$⟩ r)) (map-random (pos t) (α-random p)) ≈ a →
    J (m p) (λ r → map (neg t) ⟨$⟩ (α p ⟨$⟩ r)) (map-random (neg t) (α-random p)) ≈ b →
    (pa : Bnd a) (pb : Bnd b) → E-atᴵ p t ≃ (a − b [ pa , pb ])
  E-atᴵ-≈ p t ea eb pa pb = mk≃ 0# (Is-0 finite)
    (trans (+-cong (+-cong ea refl) refl) (sym (+-cong (+-cong refl eb) refl)))

  module SymE (d : Hom S WQ WQ) (c : _) (hc : ∫ᴹ {WQ} lebPre d ≈ c) (n : _) (nn : (c + c) * n ≈ 1#) where
    open Sym d c hc n nn public

    RH : Hom S RQ WQ → ∣A∣
    RH g = n * (∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S g inlH)) + ∫ᴹ {WQ} lebPre (mulH {WQ} d (_∘H_ S g inrH)))

    symI : ∀ (g⁺ g⁻ : Hom S RQ WQ) → Bnd (RH g⁺) → Bnd (RH g⁻) → ITest symDist
    symI g⁺ g⁻ b⁺ b⁻ = record
      { pos = toR g⁺ ; neg = toR g⁻
      ; pos-int = Is-resp finite (sym (J-sym g⁺)) b⁺
      ; neg-int = Is-resp finite (sym (J-sym g⁻)) b⁻ }

    E-atᴵ-sym : ∀ (g⁺ g⁻ : Hom S RQ WQ) (b⁺ : Bnd (RH g⁺)) (b⁻ : Bnd (RH g⁻)) →
      E-atᴵ symDist (symI g⁺ g⁻ b⁺ b⁻) ≃ (RH g⁺ − RH g⁻ [ b⁺ , b⁻ ])
    E-atᴵ-sym g⁺ g⁻ b⁺ b⁻ = E-atᴵ-≈ symDist (symI g⁺ g⁻ b⁺ b⁻) (J-sym g⁺) (J-sym g⁻) b⁺ b⁻

    -- odd statistics
    RH-odd : ∀ (g⁺ g⁻ : Hom S RQ WQ) →
      (∀ x → map g⁺ ⟨$⟩ (map inlH ⟨$⟩ x) ≈ map g⁻ ⟨$⟩ (map inrH ⟨$⟩ x)) →
      (∀ x → map g⁺ ⟨$⟩ (map inrH ⟨$⟩ x) ≈ map g⁻ ⟨$⟩ (map inlH ⟨$⟩ x)) → RH g⁺ ≈ RH g⁻
    RH-odd g⁺ g⁻ e₁ e₂ = *-cong refl (trans
      (+-cong (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S g⁺ inlH)} {mulH {WQ} d (_∘H_ S g⁻ inrH)} (λ x → *-cong refl (e₁ x)))
              (∫ᴹ-cong {WQ} lebPre {mulH {WQ} d (_∘H_ S g⁺ inrH)} {mulH {WQ} d (_∘H_ S g⁻ inlH)} (λ x → *-cong refl (e₂ x))))
      (+-comm _ _))

    E-atᴵ-odd : ∀ (g⁺ g⁻ : Hom S RQ WQ) (b⁺ : Bnd (RH g⁺)) (b⁻ : Bnd (RH g⁻)) →
      (∀ x → map g⁺ ⟨$⟩ (map inlH ⟨$⟩ x) ≈ map g⁻ ⟨$⟩ (map inrH ⟨$⟩ x)) →
      (∀ x → map g⁺ ⟨$⟩ (map inrH ⟨$⟩ x) ≈ map g⁻ ⟨$⟩ (map inlH ⟨$⟩ x)) →
      E-atᴵ symDist (symI g⁺ g⁻ b⁺ b⁻) ≃ (0# − 0# [ Is-0 finite , Is-0 finite ])
    E-atᴵ-odd g⁺ g⁻ b⁺ b⁻ e₁ e₂ = ≃-trans (E-atᴵ-sym g⁺ g⁻ b⁺ b⁻)
      (mk≃ 0# (Is-0 finite) (trans (+-cong (trans (+-identityʳ _) (RH-odd g⁺ g⁻ e₁ e₂)) refl)
        (sym (+-cong (+-identityˡ _) refl))))
