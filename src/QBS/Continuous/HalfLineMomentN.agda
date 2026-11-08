{-# OPTIONS --safe --without-K #-}

-- All polynomial moments of the exponential: the tests (part 1; part 2 is `HalfLineMomentFact`).
-- Reader: this is the toolbox for `HalfLineMomentFact`; go there for the theorem `∫ xⁿ e^{−x} = n!`.
--   * `pwNegExpH i : WQ ⇒ WQ`, the test `x ↦ xⁱ e^{−x}`, and `kH j`, the test `x ↦ (j+1) xʲ e^{−x}`;
--   * `facts`, `eadd`: the first-order exponential facts `y + w y ≤ 1 ≤ y + w` (from `1 + w ≤ eʷ ≤ 1 + w + w²`) and the
--     addition law of `e^{−x}` on `[0, N]`, the inputs of the certificate calculus `Analysis/Deriv*`.
-- (The unit-interval identity `ibp-unit`, which this module used to prove from the hand-written pack of
-- `Analysis/PolyExpCert`, is replaced by the `Deriv` route of `HalfLineMomentFact`.)
module QBS.Continuous.HalfLineMomentN where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

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
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.TailFTC using (module TailFTC)

module HalfLineMomentN (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgT A R using (exp-facts)
  open AlgP A R using (pw; pw-mono)
  open Exp A using (natE; bd1)
  open NegExp (lemOf lem₁) using (negExp; negExp-expC-nat; Meas-negExp; negExp-cong)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open HalfLineNegExp lem₁ using (negExp-add)
  open QBS
  open Hom

  -- the first-order exponential facts at any width t ≤ 1
  facts : ∀ {t} → t ≤ 1# → (negExp t + t * negExp t ≤ 1#) × (1# ≤ negExp t + t)
  facts {t} t1 = exp-facts {negExp t} {t} {expC (lemOf lem₁) t} (negExp-expC-nat t 1 (bd1 t1))
    (1+≤expC (lemOf lem₁) t) (expC≤quad (lemOf lem₁) t1)

  eadd : ∀ N {a t} → a + t ≤ natE N → t ≤ 1# → negExp (a + t) ≈ negExp a * negExp t
  eadd N {a} {t} at t1 = negExp-add {a} {t} {N} {1} {N} (≤-trans ≤-+ʳ at) (bd1 t1) at

  ----------------------------------------------------------------------------
  -- the tests `xⁱ e^{−x}` and `(j+1) xʲ e^{−x}`

  pw-cong : ∀ i {x y} → x ≈ y → pw i x ≈ pw i y
  pw-cong i e = ≤-antisym (pw-mono i (≤-reflexive e)) (pw-mono i (≤-reflexive (sym e)))

  hx : ℕ → ∣A∣ → ∣A∣
  hx i x = pw i x * negExp x

  hx-cong : ∀ i {x y} → x ≈ y → hx i x ≈ hx i y
  hx-cong i e = *-cong (pw-cong i e) (negExp-cong e)

  Meas-pw : ∀ i {f : R₁ → ∣A∣} → Meas f → Meas (λ r → pw i (f r))
  Meas-pw zero m = Meas-const 1#
  Meas-pw (suc i) {f} m = Meas-⊗ {f} {λ r → pw i (f r)} m (Meas-pw i m)

  pwNegExpH : ℕ → Hom S WQ WQ
  pwNegExpH i = record
    { map = record { to = hx i ; cong = hx-cong i }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (γ ⟨$⟩ r)} {λ r → negExp (γ ⟨$⟩ r)}
        (Meas-pw i {γ ⟨$⟩_} m) (Meas-negExp {γ ⟨$⟩_} m) }

  kH : ℕ → Hom S WQ WQ
  kH j = record
    { map = record { to = λ x → natE (suc j) * hx j x ; cong = λ e → *-cong refl (hx-cong j e) }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → natE (suc j)} {λ r → hx j (γ ⟨$⟩ r)} (Meas-const (natE (suc j)))
        (map-random (pwNegExpH j) {γ} m) }
