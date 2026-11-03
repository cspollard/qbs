{-# OPTIONS --safe --without-K #-}

-- Pointwise facts for the change of variables (helper for `ChangeOfVariables`).  For an increasing bijection φ with
-- inverse ψ given by the Galois connection `a ≤ ψ y ↔ φ a ≤ y` (module `Pull`):
--   * `χIv-pull`: χ[a,b)(ψ y) ≈ χ[φ a, φ b)(y);
--   * `χInf-pull`: ψ y = ∞ iff y = ∞ (ψ and φ preserve finiteness; excluded middle for the non-infinite case);
-- and `inf-null`: every reweighting of Lebesgue measure gives {∞} mass 0 (the shifted unit pieces are finite).
module QBS.Continuous.ChangeOfVariablesAlg where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using ([_,_]′)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitStream using (module DigitStream)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.LebesgueScaleAlg using (module LebesgueScaleAlg)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)

module ChangeOfVariablesAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong)
  open OmegaSemiring A using (_≈_; _≤_; 0#; refl; trans; *-cong; ≤-trans; ≤-reflexive; sym; zeroʳ; 0-least)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Exp A using (natE)
  open Meas (lemOf lem₁) using (Meas-const)
  open Series A using (∑ᶠ-zero)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open Intervals (lemOf lem₁) using (Ge; InIv; InInf; χIv; χInf; tv-cong)
  open DigitStream (lemOf lem₁) using (floor-ex)
  open LebesgueDyadic lem₁ using (J-const)
  open LebesgueDyadicAlg (lemOf lem₁) using (natE≈nat; no-succ; bnd-natE; inf-out)
  open LebesgueScaleAlg (lemOf lem₁) using (ge⇒≤; ≤⇒ge)
  open LebesgueShiftAlg (lemOf lem₁) using (total)
  open QBS
  open Hom

  -- a point that is not infinite is bounded, and a bounded one is not infinite
  inf-bnd : ∀ y → (InInf y → ⊥) → Bnd y
  inf-bnd y ni = [ (λ yb → suc k , ≤-trans yb (≤-reflexive (natE≈nat (suc k))))
                 , (λ bk → ⊥-elim (nk (≤⇒ge (natE (suc k)) y bk))) ]′ (total y (natE (suc k)))
    where
      fl = floor-ex y ni
      k = proj₁ fl
      nk = proj₂ (proj₂ fl)

  bnd-notinf : ∀ x → Bnd x → InInf x → ⊥
  bnd-notinf x (m , xm) g = no-succ m (≤-trans (ge⇒≤ (natE (suc m)) x (g (suc m))) (≤-trans xm (≤-reflexive (sym (natE≈nat m)))))

  module Pull (Φ Ψ : ∣A∣ → ∣A∣) (gc-to : ∀ a y → a ≤ Ψ y → Φ a ≤ y) (gc-from : ∀ a y → Φ a ≤ y → a ≤ Ψ y) where

    χIv-pull : ∀ a b y → map (χIv a b) ⟨$⟩ Ψ y ≈ map (χIv (Φ a) (Φ b)) ⟨$⟩ y
    χIv-pull a b y = tv-cong {InIv a b (Ψ y)} {InIv (Φ a) (Φ b) y}
      (λ (g , n) → ≤⇒ge (Φ a) y (gc-to a y (ge⇒≤ a (Ψ y) g)) , (λ h → n (≤⇒ge b (Ψ y) (gc-from b y (ge⇒≤ (Φ b) y h)))))
      (λ (g , n) → ≤⇒ge a (Ψ y) (gc-from a y (ge⇒≤ (Φ a) y g)) , (λ h → n (≤⇒ge (Φ b) y (gc-to b y (ge⇒≤ b (Ψ y) h)))))

    module _ (Φ-fin : ∀ a → Bnd a → Bnd (Φ a)) (Ψ-fin : ∀ y → Bnd y → Bnd (Ψ y)) where

      inf-fwd : ∀ y → InInf (Ψ y) → InInf y
      inf-fwd y g = [ (λ i → i) , (λ ni → ⊥-elim (bnd-notinf (Ψ y) (Ψ-fin y (inf-bnd y ni)) g)) ]′ (lemOf lem₁ (InInf y))

      inf-bwd : ∀ y → InInf y → InInf (Ψ y)
      inf-bwd y g k = ≤⇒ge (natE k) (Ψ y) (gc-from (natE k) y (≤-trans (proj₂ (Φ-fin (natE k) (bnd-natE k)))
        (≤-trans (≤-reflexive (sym (natE≈nat (proj₁ (Φ-fin (natE k) (bnd-natE k)))))) (ge⇒≤ _ y (g _)))))

      χInf-pull : ∀ y → map χInf ⟨$⟩ Ψ y ≈ map χInf ⟨$⟩ y
      χInf-pull y = tv-cong {InInf (Ψ y)} {InInf y} (inf-fwd y) (inf-bwd y)

  -- no reweighting of Lebesgue measure charges ∞
  inf-null : ∀ (f : Hom S WQ WQ) → ∫ᴹ {WQ} lebPre (mulH {WQ} f χInf) ≈ 0#
  inf-null f = trans (∫ᴹ-leb (mulH {WQ} f χInf)) (∑ᶠ-zero z)
    where
      pt : ∀ j r → map (mulH {WQ} f χInf) ⟨$⟩ shiftPt j r ≈ 0#
      pt j r = trans (*-cong refl (inf-out j r)) (zeroʳ _)
      z : ∀ j → J fairCoin (λ r → map (mulH {WQ} f χInf) ⟨$⟩ shiftPt j r) (Meas-hshift j (mulH {WQ} f χInf)) ≈ 0#
      z j = trans (J-cong fairCoin (Meas-hshift j (mulH {WQ} f χInf)) (Meas-const 0#) (pt j)) (J-const 0# 0-least)
