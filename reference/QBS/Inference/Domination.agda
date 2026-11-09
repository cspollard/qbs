{-# OPTIONS --safe --without-K #-}

-- Integrability by domination.  Values are lower reals, so everything is additive: no subtraction, no division.
--   * `Bnd-≤`, `Bnd-add`, `Bnd-scale`: finiteness is downward closed, and closed under sums and products;
--   * `J-Bnd-mono m p q : (∀ x → φ x ≤ ψ x) → Bnd (J m ψ q) → Bnd (J m φ p)`, for any measure `m`;
--   * `ITest-dom p t g⁺ g⁻`: parts of `t : ITest p` dominate those of a new test, which is then integrable;
--   * the integral on `WQ` is monotone (`∫ᴹ-mono`), scales (`∫ᴹ-scale`: `∫ (c · f) ≈ c · ∫ f`) and adds (`∫ᴹ-add`,
--     for the pointwise sum `addH`), so `Bnd (∫ᴹ p b)` and `g ≤ c · b` give `Bnd (∫ᴹ p g)` (`∫ᴹ-Bnd-dom`);
--   * for a density, `densB-dom` and `densI-dom d nrm g⁺ g⁻ b c cB bB dom⁺ dom⁻ : ITest (densDist d nrm)`, given
--     `g± x ≤ c · b x` and `Bnd (∫ᴹ lebPre (mulH d b))`.  This replaces the bespoke `Bnd` proofs of
--     `Inference/DensityExpectation.densI`.
module QBS.Inference.Domination where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
import QBS.Inference.ExpectationInt as EI

module Domination (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-mono; J-add; J-scale)
  open Integration A using (probClass)
  open OmegaSemiring A using (1#; _≈_; _≤_; _+_; _*_; refl; sym; trans; ≤-trans; ≤-refl; ≤-reflexive; *-mono; *-cong; +-cong; *-comm; *-assoc; distribˡ)
  open Bounded A using (Bnd; finite; _≃_; _−_[_,_])
  open SubSemiring using (Is-+; Is-*)
  open Meas (lemOf lem₁) using (Meas; Meas-const; Meas-⊕; Meas-⊗)
  open BoundedSignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ψ; mψ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open DensityDist lem₁ using (densDist)
  open DensityExpectation lem₁ using (densI; E-atᴵ-dens)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open Pre
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open ITest
  open Hom

  ----------------------------------------------------------------------------
  -- finiteness

  Bnd-≤ : ∀ {a b} → a ≤ b → Bnd b → Bnd a
  Bnd-≤ le (n , h) = n , ≤-trans le h

  Bnd-add : ∀ {a b} → Bnd a → Bnd b → Bnd (a + b)
  Bnd-add = Is-+ finite

  Bnd-scale : ∀ {c a} → Bnd c → Bnd a → Bnd (c * a)
  Bnd-scale = Is-* finite

  J-Bnd-mono : ∀ m {φ ψ} (p : Meas φ) (q : Meas ψ) → (∀ x → φ x ≤ ψ x) → Bnd (J m ψ q) → Bnd (J m φ p)
  J-Bnd-mono m {φ} {ψ} p q le = Bnd-≤ (J-mono m {φ} {ψ} p q le)

  -- a test dominated by an integrable one is integrable
  ITest-dom : ∀ {X : QBS S} (p : Pre X) (t : ITest p) (g⁺ g⁻ : Hom S X CutQ) →
    (∀ x → map g⁺ ⟨$⟩ x ≤ map (pos t) ⟨$⟩ x) → (∀ x → map g⁻ ⟨$⟩ x ≤ map (neg t) ⟨$⟩ x) → ITest p
  ITest-dom p t g⁺ g⁻ le⁺ le⁻ = record
    { pos = g⁺ ; neg = g⁻
    ; pos-int = J-Bnd-mono (m p) {λ r → map g⁺ ⟨$⟩ (α p ⟨$⟩ r)} {λ r → map (pos t) ⟨$⟩ (α p ⟨$⟩ r)}
        (map-random g⁺ (α-random p)) (map-random (pos t) (α-random p)) (λ r → le⁺ _) (pos-int t)
    ; neg-int = J-Bnd-mono (m p) {λ r → map g⁻ ⟨$⟩ (α p ⟨$⟩ r)} {λ r → map (neg t) ⟨$⟩ (α p ⟨$⟩ r)}
        (map-random g⁻ (α-random p)) (map-random (neg t) (α-random p)) (λ r → le⁻ _) (neg-int t) }

  ----------------------------------------------------------------------------
  -- the integral of tests on `WQ`

  ∫ᴹ-mono : ∀ (p : Pre (XW WQ)) {f g : Hom S WQ WQ} →
    (∀ x → map f ⟨$⟩ x ≤ map g ⟨$⟩ x) → ∫ᴹ {WQ} p f ≤ ∫ᴹ {WQ} p g
  ∫ᴹ-mono p {f} {g} le = J-mono (m p) {ψ {WQ} p f} {ψ {WQ} p g} (mψ {WQ} p f) (mψ {WQ} p g)
    (λ r → *-mono _ (le _))

  -- pointwise sum of tests
  addH : Hom S WQ WQ → Hom S WQ WQ → Hom S WQ WQ
  addH f g = record
    { map = record { to = λ x → (map f ⟨$⟩ x) + (map g ⟨$⟩ x) ; cong = λ e → +-cong (Func.cong (map f) e) (Func.cong (map g) e) }
    ; map-random = λ {γ} mγ → Meas-⊕ {λ r → map f ⟨$⟩ (γ ⟨$⟩ r)} {λ r → map g ⟨$⟩ (γ ⟨$⟩ r)}
        (map-random f {γ} mγ) (map-random g {γ} mγ) }

  ∫ᴹ-scale : ∀ (p : Pre (XW WQ)) c (f : Hom S WQ WQ) → ∫ᴹ {WQ} p (mulH {WQ} (constW c) f) ≈ c * ∫ᴹ {WQ} p f
  ∫ᴹ-scale p c f = trans (J-cong (m p) {ψ {WQ} p (mulH {WQ} (constW c) f)} {λ r → c * ψ {WQ} p f r}
    (mψ {WQ} p (mulH {WQ} (constW c) f)) (Meas-⊗ {λ _ → c} {ψ {WQ} p f} (Meas-const c) (mψ {WQ} p f))
    (λ r → trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _))))
    (J-scale (m p) c {ψ {WQ} p f} (mψ {WQ} p f))

  ∫ᴹ-add : ∀ (p : Pre (XW WQ)) (f g : Hom S WQ WQ) → ∫ᴹ {WQ} p (addH f g) ≈ ∫ᴹ {WQ} p f + ∫ᴹ {WQ} p g
  ∫ᴹ-add p f g = trans (J-cong (m p) {ψ {WQ} p (addH f g)} {λ r → ψ {WQ} p f r + ψ {WQ} p g r}
    (mψ {WQ} p (addH f g)) (Meas-⊕ {ψ {WQ} p f} {ψ {WQ} p g} (mψ {WQ} p f) (mψ {WQ} p g))
    (λ r → distribˡ _ _ _)) (J-add (m p) {ψ {WQ} p f} {ψ {WQ} p g} (mψ {WQ} p f) (mψ {WQ} p g))

  -- domination: `g ≤ c · b` gives `∫ g ≤ c · ∫ b`, and finiteness
  ∫ᴹ-dom : ∀ (p : Pre (XW WQ)) (g b : Hom S WQ WQ) c →
    (∀ x → map g ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) → ∫ᴹ {WQ} p g ≤ c * ∫ᴹ {WQ} p b
  ∫ᴹ-dom p g b c dom = ≤-trans (∫ᴹ-mono p {g} {mulH {WQ} (constW c) b} dom) (≤-reflexive (∫ᴹ-scale p c b))

  ∫ᴹ-Bnd-dom : ∀ (p : Pre (XW WQ)) (g b : Hom S WQ WQ) c → Bnd c → Bnd (∫ᴹ {WQ} p b) →
    (∀ x → map g ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) → Bnd (∫ᴹ {WQ} p g)
  ∫ᴹ-Bnd-dom p g b c cB bB dom = Bnd-≤ (∫ᴹ-dom p g b c dom) (Bnd-scale cB bB)

  ----------------------------------------------------------------------------
  -- densities

  -- `d · g ≤ c · (d · b)` pointwise
  dens-dom : ∀ (d g b : Hom S WQ WQ) c → (∀ x → map g ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) →
    ∀ x → map (mulH {WQ} d g) ⟨$⟩ x ≤ c * (map (mulH {WQ} d b) ⟨$⟩ x)
  dens-dom d g b c dom x = ≤-trans (*-mono (map d ⟨$⟩ x) (dom x))
    (≤-reflexive (trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _))))

  densB-dom : ∀ (d g b : Hom S WQ WQ) c → Bnd c → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d b)) →
    (∀ x → map g ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d g))
  densB-dom d g b c cB bB dom = ∫ᴹ-Bnd-dom lebPre (mulH {WQ} d g) (mulH {WQ} d b) c cB bB (dens-dom d g b c dom)

  densI-dom : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (g⁺ g⁻ b : Hom S WQ WQ) c → Bnd c →
    Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d b)) →
    (∀ x → map g⁺ ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) → (∀ x → map g⁻ ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) → ITest (densDist d nrm)
  densI-dom d nrm g⁺ g⁻ b c cB bB dom⁺ dom⁻ =
    densI d nrm g⁺ g⁻ (densB-dom d g⁺ b c cB bB dom⁺) (densB-dom d g⁻ b c cB bB dom⁻)

  -- its expectation is the signed value of the two integrals (`E-atᴵ-dens` for the dominated bounds)
  E-atᴵ-dom : ∀ d (nrm : ∫ᴹ {WQ} lebPre d ≈ 1#) (g⁺ g⁻ b : Hom S WQ WQ) c (cB : Bnd c)
    (bB : Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} d b)))
    (dom⁺ : ∀ x → map g⁺ ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) (dom⁻ : ∀ x → map g⁻ ⟨$⟩ x ≤ c * (map b ⟨$⟩ x)) →
    E-atᴵ (densDist d nrm) (densI-dom d nrm g⁺ g⁻ b c cB bB dom⁺ dom⁻)
      ≃ (∫ᴹ {WQ} lebPre (mulH {WQ} d g⁺) − ∫ᴹ {WQ} lebPre (mulH {WQ} d g⁻)
          [ densB-dom d g⁺ b c cB bB dom⁺ , densB-dom d g⁻ b c cB bB dom⁻ ])
  E-atᴵ-dom d nrm g⁺ g⁻ b c cB bB dom⁺ dom⁻ =
    E-atᴵ-dens d nrm g⁺ g⁻ (densB-dom d g⁺ b c cB bB dom⁺) (densB-dom d g⁻ b c cB bB dom⁻)
