{-# OPTIONS --safe --without-K #-}

-- Gaussian moments on the half-line, without π (part 1): the tests and the exponential facts.
--   * `phiH : WQ ⇒ WQ`, the Gaussian `x ↦ e^{−x²/2}` (`negExp` of `½ x²`: `Meas-⊗`, `Meas-negExp`);
--     `gMomH i`, the test `x ↦ xⁱ e^{−x²/2}`, and `gKH j`, the test `x ↦ (j+1) xʲ e^{−x²/2}`;
--   * the first-order exponential facts `negExp u + u negExp u ≤ 1 ≤ negExp u + u` at every bounded u (the second by
--     `Analysis/CutSplit.split1`: for u ≥ 1 it is trivial), in the form `Ea`/`Eb`/`Ec` (bound `P s`) that the Gaussian
--     certificates `Analysis/DerivGauss.Gx` take.
-- (The unit-interval identity that this module used to prove from the hand-written pack `Analysis/GaussCert` is replaced
-- by the `Deriv` route of `GaussMoment` and `GaussMean`.)
module QBS.Continuous.GaussHalfLine where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CutSplit using (split1)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussExp using (bd; module AlgGE)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.TailFTC using (module TailFTC)

module GaussHalfLine (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half)
  open AlgT A R using (P; exp-facts)
  open AlgP A R using (pw; pnat; natE-pnat; P-mono)
  open AlgGE A R using (eb; ec-big)
  open Exp A using (natE; bd1)
  open NegExp (lemOf lem₁) using (negExp; negExp-expC-nat; Meas-negExp; negExp-cong)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open HalfLineNegExp lem₁ using (negExp-add)
  open HalfLineMomentN lem₁ using (pw-cong; Meas-pw)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the exponential facts, at every bounded argument

  P≤natE : ∀ k → P k ≤ natE (pnat k)
  P≤natE k = ≤-reflexive (sym (natE-pnat k))

  E-add : ∀ m {x y} → x ≤ P (bd m) → y ≤ P (bd m) → x + y ≤ P (bd m) → negExp (x + y) ≈ negExp x * negExp y
  E-add m {x} {y} xb yb xyb = negExp-add {x} {y} {pnat (bd m)} {pnat (bd m)} {pnat (bd m)}
    (≤-trans xb (P≤natE _)) (≤-trans yb (P≤natE _)) (≤-trans xyb (P≤natE _))

  E-b : ∀ m {u} → u ≤ P (bd m) → negExp u + u * negExp u ≤ 1#
  E-b m {u} ub = eb {negExp u} {u} {expC (lemOf lem₁) u}
    (negExp-expC-nat u (pnat (bd m)) (≤-trans ub (P≤natE _))) (1+≤expC (lemOf lem₁) u)

  E-c : ∀ {u} → 1# ≤ negExp u + u
  E-c {u} with split1 (lemOf lem₁) u
  ... | inj₁ u1 = proj₂ (exp-facts {negExp u} {u} {expC (lemOf lem₁) u} (negExp-expC-nat u 1 (bd1 u1))
    (1+≤expC (lemOf lem₁) u) (expC≤quad (lemOf lem₁) u1))
  ... | inj₂ 1u = ec-big 1u

  ----------------------------------------------------------------------------
  -- the tests

  Φ : ∣A∣ → ∣A∣
  Φ x = negExp (half * (x * x))

  Φ-cong : ∀ {x y} → x ≈ y → Φ x ≈ Φ y
  Φ-cong e = negExp-cong (*-cong refl (*-cong e e))

  Meas-Φ : ∀ {f : R₁ → ∣A∣} → Meas f → Meas (λ r → Φ (f r))
  Meas-Φ {f} m = Meas-negExp {λ r → half * (f r * f r)}
    (Meas-⊗ {λ _ → half} {λ r → f r * f r} (Meas-const half) (Meas-⊗ {f} {f} m m))

  phiH : Hom S WQ WQ
  phiH = record
    { map = record { to = Φ ; cong = Φ-cong }
    ; map-random = λ {γ} m → Meas-Φ {γ ⟨$⟩_} m }

  gh : ℕ → ∣A∣ → ∣A∣
  gh i x = pw i x * Φ x

  gh-cong : ∀ i {x y} → x ≈ y → gh i x ≈ gh i y
  gh-cong i e = *-cong (pw-cong i e) (Φ-cong e)

  gMomH : ℕ → Hom S WQ WQ
  gMomH i = record
    { map = record { to = gh i ; cong = gh-cong i }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (γ ⟨$⟩ r)} {λ r → Φ (γ ⟨$⟩ r)}
        (Meas-pw i {γ ⟨$⟩_} m) (Meas-Φ {γ ⟨$⟩_} m) }

  kh : ℕ → ∣A∣ → ∣A∣
  kh j x = natE (suc j) * gh j x

  kh-cong : ∀ j {x y} → x ≈ y → kh j x ≈ kh j y
  kh-cong j e = *-cong refl (gh-cong j e)

  gKH : ℕ → Hom S WQ WQ
  gKH j = record
    { map = record { to = kh j ; cong = kh-cong j }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → natE (suc j)} {λ r → gh j (γ ⟨$⟩ r)} (Meas-const (natE (suc j)))
        (map-random (gMomH j) {γ} m) }

  ----------------------------------------------------------------------------
  -- the exponential facts at every bound `P s` (the form of `DerivGauss.Gx`)

  s≤bd : ∀ s → s ℕ.≤ bd s
  s≤bd s = ℕ.≤-trans (ℕ.m≤m+n s s) (ℕ.n≤1+n (s ℕ.+ s))

  Ea : ∀ s {x y} → x ≤ P s → y ≤ P s → x + y ≤ P s → negExp (x + y) ≈ negExp x * negExp y
  Ea s xb yb xyb = E-add s (≤-trans xb (P-mono (s≤bd s))) (≤-trans yb (P-mono (s≤bd s))) (≤-trans xyb (P-mono (s≤bd s)))

  Eb : ∀ s {t} → t ≤ P s → negExp t + t * negExp t ≤ 1#
  Eb s tb = E-b s (≤-trans tb (P-mono (s≤bd s)))

  Ec : ∀ s {t} → t ≤ P s → 1# ≤ negExp t + t
  Ec s _ = E-c
