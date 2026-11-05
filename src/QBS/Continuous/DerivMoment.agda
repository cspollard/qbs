{-# OPTIONS --safe --without-K #-}

-- Validation of the certificate calculus: `∫₀^∞ xⁿ e^{−x} dλ(x) = n!` from `Deriv` data built by the rules.
-- The statement is that of `HalfLineMomentFact.∫ᴹ-pw-moment`; there the unit-interval identities came from the 300-line pack
-- `Analysis/PolyExpCert` through `HalfLineMomentN.AtInterval` (about 150 lines of shifting by hand).  Here
--   * `dvn j n : Deriv (n+1) (xʲ⁺¹ e^{−x}) (xʲ⁺¹ e^{−x}) ((j+1) xʲ e^{−x})` is `Analysis/DerivExp.xjE` (the identity, the powers by the
--     product rule, the exponential `DE`) with M = n + 1, and the exponential facts of `HalfLineMomentN`;
--   * `OnHalfLine.glue-D` (`Continuous/DerivBridge`) turns it into `∫ xʲ⁺¹ e^{−x} = ∫ (j+1) xʲ e^{−x}`, with G 0 = 0 and the tail
--     `xʲ⁺¹ e^{−N} → 0` of `Analysis/ExpTail` as in `HalfLineMomentFact`.
-- The recursion and the base case are unchanged, and the old modules stay as checks (the two results are the same statement).
module QBS.Continuous.DerivMoment where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivExp using (module AlgDE)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCExpHalf using (module TailFTCExpHalf)
open import QBS.Continuous.DerivBridge using (module DerivBridge)

module DerivMoment (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgP A R using (natE≤P)
  open AlgD A R using (Deriv)
  open AlgDE A R using (module Expo)
  open Exp A using (natE)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; negExp-anti)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineMomentN lem₁ using (negExp-cong; pwNegExpH; kH; hx; facts; eadd)
  open HalfLineMomentFact lem₁ using (fact; G0; k-scale; module T)
  open TailFTCExpHalf lem₁ using (∫-negExp)
  open DerivBridge lem₁ using (module OnHalfLine)
  open QBS
  open Hom

  -- the data on [0, n+1]
  dvn : ∀ j n → Deriv (natE (suc n)) (hx (suc j)) (λ x → map (pwNegExpH (suc j)) ⟨$⟩ x) (λ x → map (kH j) ⟨$⟩ x)
  dvn j n = Expo.xjE negExp (natE (suc n)) (suc n) (natE≤P (suc n)) negExp≤1 negExp-anti negExp-cong (eadd (suc n))
    (λ t1 → proj₁ (facts t1)) (λ t1 → proj₂ (facts t1)) (suc n , natE≤P (suc n)) j

  -- ∫ xʲ⁺¹ e^{−x} = (j+1) ∫ xʲ e^{−x}
  moment-succ : ∀ j → ∫ᴹ {WQ} lebPre (pwNegExpH (suc j)) ≈ natE (suc j) * ∫ᴹ {WQ} lebPre (pwNegExpH j)
  moment-succ j = trans (OnHalfLine.glue-D (pwNegExpH (suc j)) (kH j) (hx (suc j)) (dvn j) (G0 j) (λ m N₀ → T.tail (suc j) m N₀))
    (k-scale j)

  -- ∫ xⁿ e^{−x} = n!
  ∫-moment : ∀ n → ∫ᴹ {WQ} lebPre (pwNegExpH n) ≈ fact n
  ∫-moment zero = trans (∫ᴹ-cong lebPre {pwNegExpH 0} {negExpH} (λ x → *-identityˡ (negExp x))) ∫-negExp
  ∫-moment (suc j) = trans (moment-succ j) (*-cong refl (∫-moment j))
