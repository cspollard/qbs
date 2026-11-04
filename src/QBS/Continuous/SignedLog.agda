{-# OPTIONS --safe --without-K #-}

-- The logarithm as a signed value (plan 03, "Signed layer").  For a cut x, log x = log⁺ x − log⁻ x with
--   * `logP x` = log (x ⊔ 1) ∈ [0, ∞] and `logN x` = log (1 / (x ⊓ 1)) ∈ [0, ∞], characterised by e^{logP x} ≈ x for
--     1 ≤ x < ∞ and logP x ≈ 0 for x ≤ 1 (`logP-ge`, `logP-le`), e^{−logN x} ≈ x for 0 < x ≤ 1 and logN x ≈ 0 for
--     1 ≤ x (`logN-le`, `logN-ge`);
--   * `logS x : Sg` for 0 < x < ∞ (`PosQ`, `BndQ`), with `log-mul` (log xy ≃ log x + log y), `log-one`, `log-exp`,
--     monotonicity, and measurability of r ↦ logP (h r), logN (h r) (`Meas-logP`, `Meas-logN`) for use as test parts;
--   * one-sided values (`SignedInf`): `log∞ x ∈ (−∞, ∞]` for x > 0 (x = ∞ allowed) and `nlog∞ x = −log x ∈ (−∞, ∞]`
--     for x < ∞ (x = 0 allowed, −log 0 = ∞).
-- Route: suggested definitions q ∈ logP x iff q < 0 or ∃ s ∈ x with e^q < s (e^q ≤ some rational s′ < s, using
-- `ExpLower.expC` on the rational cut), and q ∈ logN x iff q < 0 or ∃ p > q with s eᵖ < 1 for all s ∈ x (as
-- `NegExp.negExp`); any construction with the stated properties will do.  `log-mul` from `ExpLower.expC-add` and
-- injectivity of e^x on finite values; the reverse inequalities by excluded middle (`LowerRealsNear.near-sup-bnd`).
--   Skeleton: holes first.
module QBS.Continuous.SignedLog where

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Rational.Unnormalised.Base using (_<_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; 0ℚᵘ)
open import QBS.Analysis.LowerReals using (Cut; _⊑_; _≋_; _⊗_; oneC; zeroC)
open Cut using (mem)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.ExpLower using (expC)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.SignedInf using (module SignedInf)

module SignedLog (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; 0S; _−_[_,_])
  open NegExp (lemOf lem₁) using (negExp)
  open Meas (lemOf lem₁) using (Meas)
  open SignedInf lem₁ using (Sg∞; _≃∞_; ι∞; _−∞_[_])

  -- bounded below by a positive rational
  PosQ : Cut → Set
  PosQ x = Σ ℚᵘ (λ q → 0ℚᵘ < q × mem x q)

  logP logN : Cut → Cut
  logP = ?
  logN = ?

  -- characterisation
  logP-ge : ∀ x → oneC ⊑ x → BndQ x → expC (lemOf lem₁) (logP x) ≋ x
  logP-ge = ?

  logP-le : ∀ x → x ⊑ oneC → logP x ≋ zeroC
  logP-le = ?

  logN-le : ∀ x → PosQ x → x ⊑ oneC → negExp (logN x) ≋ x
  logN-le = ?

  logN-ge : ∀ x → oneC ⊑ x → logN x ≋ zeroC
  logN-ge = ?

  -- finiteness, order, congruence
  logP-fin : ∀ x → BndQ x → Bnd (logP x)
  logP-fin = ?

  logN-fin : ∀ x → PosQ x → Bnd (logN x)
  logN-fin = ?

  logP-mono : ∀ {x y} → x ⊑ y → logP x ⊑ logP y
  logP-mono = ?

  logN-anti : ∀ {x y} → x ⊑ y → logN y ⊑ logN x
  logN-anti = ?

  logP-cong : ∀ {x y} → x ≋ y → logP x ≋ logP y
  logP-cong = ?

  logN-cong : ∀ {x y} → x ≋ y → logN x ≋ logN y
  logN-cong = ?

  -- the signed logarithm on (0, ∞)
  logS : ∀ x → PosQ x → BndQ x → Sg
  logS x px bx = logP x − logN x [ logP-fin x bx , logN-fin x px ]

  PosQ-one : PosQ oneC
  PosQ-one = ?

  BndQ-one : BndQ oneC
  BndQ-one = ?

  PosQ-mul : ∀ {x y} → PosQ x → PosQ y → PosQ (x ⊗ y)
  PosQ-mul = ?

  BndQ-mul : ∀ {x y} → BndQ x → BndQ y → BndQ (x ⊗ y)
  BndQ-mul = ?

  log-one : logS oneC PosQ-one BndQ-one ≃ 0S
  log-one = ?

  log-mul : ∀ x y (px : PosQ x) (py : PosQ y) (bx : BndQ x) (by : BndQ y) →
    logS (x ⊗ y) (PosQ-mul px py) (BndQ-mul bx by) ≃ logS x px bx +S logS y py by
  log-mul = ?

  log-exp : ∀ a → BndQ a → logP (expC (lemOf lem₁) a) ≋ a × logN (expC (lemOf lem₁) a) ≋ zeroC
  log-exp = ?

  -- measurability
  Meas-logP : ∀ {h} → Meas h → Meas (λ r → logP (h r))
  Meas-logP = ?

  Meas-logN : ∀ {h} → Meas h → Meas (λ r → logN (h r))
  Meas-logN = ?

  -- one-sided: log x for 0 < x ≤ ∞, and −log x for 0 ≤ x < ∞
  log∞ : ∀ x → PosQ x → Sg∞
  log∞ x px = logP x −∞ logN x [ logN-fin x px ]

  nlog∞ : ∀ x → BndQ x → Sg∞
  nlog∞ x bx = logN x −∞ logP x [ logP-fin x bx ]

  log∞-ι : ∀ x (px : PosQ x) (bx : BndQ x) → log∞ x px ≃∞ ι∞ (logS x px bx)
  log∞-ι = ?
