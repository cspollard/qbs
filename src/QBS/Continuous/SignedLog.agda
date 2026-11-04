{-# OPTIONS --safe --without-K #-}

-- The logarithm as a signed value (plan 03, "Signed layer").  For a cut x, log x = log⁺ x − log⁻ x with
--   * `logP x` = log (x ⊔ 1) ∈ [0, ∞] and `logN x` = log (1 / (x ⊓ 1)) ∈ [0, ∞], characterised by e^{logP x} ≈ x for
--     1 ≤ x < ∞ and logP x ≈ 0 for x ≤ 1 (`logP-ge`, `logP-le`), e^{−logN x} ≈ x for 0 < x ≤ 1 and logN x ≈ 0 for
--     1 ≤ x (`logN-le`, `logN-ge`);
--   * `logS x : Sg` for 0 < x < ∞ (`PosQ`, `BndQ`), with `log-mul` (log xy ≃ log x + log y), `log-one`, `log-exp`,
--     monotonicity, and measurability of r ↦ logP (h r), logN (h r) (`Meas-logP`, `Meas-logN`) for use as test parts;
--   * one-sided values (`SignedInf`): `log∞ x ∈ (−∞, ∞]` for x > 0 (x = ∞ allowed) and `nlog∞ x = −log x ∈ (−∞, ∞]`
--     for x < ∞ (x = 0 allowed, −log 0 = ∞).
-- Route: `LogCore.logP` (q ∈ logP x iff q < 0 or some p > q and s ∈ x have e^p ≤ s, with e^p the cut `LogRat.E p`),
-- characterised by `LogCore.logP-ge` (near-supremum arguments, by excluded middle) and `log-exp` (strictness of e^p);
-- `logN x = logP (recC (x ⊓ 1))` with `LogRecip.recC` the reciprocal cut (`recC-mul`: w · (1/w) = 1, the near-maximal
-- element argument of `NegExp` for an arbitrary cut), so `logN-le` is `negExp-expC` for e^{logN x} ≈ 1/(x ⊓ 1) and
-- `LogNeg.UD` : x · e^{logN x} ≈ e^{logP x} (two cases, x ≤ 1 and 1 ≤ x).  `log-mul` exponentiates both sides
-- (`ExpLower.Add.exp-add`, `UD`) and applies injectivity of e^x on finite values, from `log-exp`.
module QBS.Continuous.SignedLog where

open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised.Base using (_<_; _*_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; 0<1; 0<½; ½; ≤-refl; ≤-<-trans; <-trans; *-pos)
open import QBS.Analysis.RationalLemmas using (*-mono-<-posʳ; *-mono-<-pos)
open import QBS.Analysis.LowerReals using (Cut; _⊑_; _≋_; _⊗_; oneC; zeroC; ⊑-refl; ⊑-trans; ⊕-inl)
open Cut using (mem)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.SignedInf using (module SignedInf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.LogCore using (module LogCore; bnd-pos)
open import QBS.Continuous.LogRecip using (recC)
open import QBS.Continuous.LogNeg using (module LogNeg; ½<1)

module SignedLog (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Bounded A using (Bnd; Sg; _≃_; _+S_; 0S; _−_[_,_])
  open NegExp (lemOf lem₁) using (negExp)
  open Meas (lemOf lem₁) using (Meas)
  open SignedInf lem₁ using (Sg∞; _≃∞_; ι∞; _−∞_[_]; ≃∞-refl)
  open MonusAlg lem₁ using (rat-bnd)
  module LC = LogCore (lemOf lem₁)
  module LN = LogNeg (lemOf lem₁)
  open Bounded A using (mk≃; finite)
  open OmegaSemiring A using (_+_; 0#; +-cong; refl; sym; trans)
  open SubSemiring finite using (Is-0)

  -- bounded below by a positive rational
  PosQ : Cut → Set
  PosQ x = Σ ℚᵘ (λ q → 0ℚᵘ < q × mem x q)

  logP logN : Cut → Cut
  logP = LC.logP
  logN = LN.logN

  -- characterisation
  logP-ge : ∀ x → oneC ⊑ x → BndQ x → expC (lemOf lem₁) (logP x) ≋ x
  logP-ge = LC.logP-ge

  logP-le : ∀ x → x ⊑ oneC → logP x ≋ zeroC
  logP-le x xo = LC.logP-le xo

  logN-le : ∀ x → PosQ x → x ⊑ oneC → negExp (logN x) ≋ x
  logN-le x px xo = LN.logN-le px xo

  logN-ge : ∀ x → oneC ⊑ x → logN x ≋ zeroC
  logN-ge x ox = LN.logN-ge ox

  -- finiteness, order, congruence
  logP-fin : ∀ x → BndQ x → Bnd (logP x)
  logP-fin x bx = rat-bnd (logP x) (LC.logP-bndQ {x} bx)

  logN-fin : ∀ x → PosQ x → Bnd (logN x)
  logN-fin x px = rat-bnd (logN x) (LN.logN-bndQ {x} px)

  logP-mono : ∀ {x y} → x ⊑ y → logP x ⊑ logP y
  logP-mono = LC.logP-mono

  logN-anti : ∀ {x y} → x ⊑ y → logN y ⊑ logN x
  logN-anti = LN.logN-anti

  logP-cong : ∀ {x y} → x ≋ y → logP x ≋ logP y
  logP-cong = LC.logP-cong

  logN-cong : ∀ {x y} → x ≋ y → logN x ≋ logN y
  logN-cong = LN.logN-cong

  -- the signed logarithm on (0, ∞)
  logS : ∀ x → PosQ x → BndQ x → Sg
  logS x px bx = logP x − logN x [ logP-fin x bx , logN-fin x px ]

  PosQ-one : PosQ oneC
  PosQ-one = ½ , 0<½ , ½<1

  BndQ-one : BndQ oneC
  BndQ-one = 1ℚᵘ , λ r m → m

  PosQ-mul : ∀ {x y} → PosQ x → PosQ y → PosQ (x ⊗ y)
  PosQ-mul (a , 0<a , ma) (b , 0<b , mb) = a * b , *-pos 0<a 0<b , inj₂ (a , b , 0<a , 0<b , ma , mb , ≤-refl)

  BndQ-mul : ∀ {x y} → BndQ x → BndQ y → BndQ (x ⊗ y)
  BndQ-mul {x} {y} bx by = proj₁ (bnd-pos {x} bx) * proj₁ (bnd-pos {y} by) , f
    where
      B₁ = proj₁ (bnd-pos {x} bx)
      B₂ = proj₁ (bnd-pos {y} by)
      0<B₁ = proj₁ (proj₂ (bnd-pos {x} bx))
      0<B₂ = proj₁ (proj₂ (bnd-pos {y} by))
      f : ∀ q → mem (x ⊗ y) q → q < B₁ * B₂
      f q (inj₁ lt) = <-trans lt (*-pos 0<B₁ 0<B₂)
      f q (inj₂ (r , s , 0<r , 0<s , mr , ms , h)) = ≤-<-trans h
        (<-trans (*-mono-<-posʳ 0<s (proj₂ (proj₂ (bnd-pos {x} bx)) r mr))
        (*-mono-<-pos 0<B₁ (proj₂ (proj₂ (bnd-pos {y} by)) s ms)))

  log-one : logS oneC PosQ-one BndQ-one ≃ 0S
  log-one = mk≃ 0# Is-0 (trans (+-cong (+-cong lp refl) refl) (sym (+-cong (+-cong refl ln) refl)))
    where
      lp = logP-le oneC ⊑-refl
      ln = logN-ge oneC ⊑-refl

  log-mul : ∀ x y (px : PosQ x) (py : PosQ y) (bx : BndQ x) (by : BndQ y) →
    logS (x ⊗ y) (PosQ-mul px py) (BndQ-mul bx by) ≃ logS x px bx +S logS y py by
  log-mul x y px py bx by = mk≃ 0# Is-0 (+-cong (LN.exp-inj (LN.logmul-exp px py (PosQ-mul px py) bx by (BndQ-mul bx by))) refl)

  log-exp : ∀ a → BndQ a → logP (expC (lemOf lem₁) a) ≋ a × logN (expC (lemOf lem₁) a) ≋ zeroC
  log-exp a ba = LC.log-exp-P a , logN-ge (expC (lemOf lem₁) a) (⊑-trans (⊕-inl oneC a) (1+≤expC (lemOf lem₁) a))

  -- measurability
  Meas-logP : ∀ {h} → Meas h → Meas (λ r → logP (h r))
  Meas-logP = LC.Meas-logP

  Meas-logN : ∀ {h} → Meas h → Meas (λ r → logN (h r))
  Meas-logN = LN.Meas-logN

  -- one-sided: log x for 0 < x ≤ ∞, and −log x for 0 ≤ x < ∞
  log∞ : ∀ x → PosQ x → Sg∞
  log∞ x px = logP x −∞ logN x [ logN-fin x px ]

  nlog∞ : ∀ x → BndQ x → Sg∞
  nlog∞ x bx = logN x −∞ logP x [ logP-fin x bx ]

  log∞-ι : ∀ x (px : PosQ x) (bx : BndQ x) → log∞ x px ≃∞ ι∞ (logS x px bx)
  log∞-ι x px bx = ≃∞-refl
