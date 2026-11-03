{-# OPTIONS --safe --without-K #-}

-- The unit piece [j, j+1) of the half-line as a fair-coin integral (helper for `FTCDyadic`, plan 03, "Change of variables").
--   * `null-le`: if F ≤ F′ off the all-true point and F is constant (= c, possibly ∞) on it, then J F ≤ J F′: pointwise
--     F ≤ F′ + c χ_Top, and `J (c χ_Top) = c · 0 = 0` (`LebesgueDyadic.fair-top`, `J-scale`); no bound on F is needed;
--   * `piece`: `∫ lebPre (f · χ[j,j+1)) ≈ J (f ∘ shiftPt j)`.  By `HalfLine.∫ᴹ-leb` the integral is a sum over the unit
--     pieces i; for i ≠ j the shifted point leaves [j, j+1) off the all-true point (`base-lt`, `base-gt`), so the term is 0
--     by `null-le`, and for i = j it is J (f ∘ shiftPt j) by `null-le` (≥) and monotonicity (≤).
module QBS.Continuous.FTCDyadicPiece where

open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (<-cmp)
open import Data.Bool.Base using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>; Tri)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Cells using (Top; borelTop)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Series using (module Series)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.LebesgueDyadic using (module LebesgueDyadic)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)

module FTCDyadicPiece (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-add; J-mono; J-scale)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; *-cong; +-cong; +-comm; ≤-trans; ≤-reflexive;
    ≤-antisym; ≤-+ʳ; 0-least; zeroʳ; *-identityʳ; +-identityʳ; *-mono) renaming (Carrier to ∣A∣)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-in; case)
  open LevelSets (lemOf lem₁) using (LS)
  open Meas (lemOf lem₁) using (Meas; Meas-const; Meas-⊕; Meas-⊗)
  open Series A using (∑ᶠ-single)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre; shiftPt; shiftF; Meas-hshift; ∫ᴹ-leb)
  open Intervals (lemOf lem₁) using (χI)
  open LebesgueDyadic lem₁ using (fair-top; J-const)
  open LebesgueDyadicAlg (lemOf lem₁) using (base-in; base-lt; base-gt; χI≤1)
  open QBS
  open Hom

  χT : R₁ → ∣A∣
  χT = χ Top

  MχT : Meas χT
  MχT = LS (Fun-χ borelTop)

  Mc : ∀ (c : ∣A∣) → Meas (λ r → c * χT r)
  Mc c = Meas-⊗ {λ _ → c} {χT} (Meas-const c) MχT

  -- J (F′ + c χ_Top) = J F′
  null-int : ∀ {F′} (M′ : Meas F′) c →
    J fairCoin (λ r → F′ r + c * χT r) (Meas-⊕ {F′} {λ r → c * χT r} M′ (Mc c)) ≈ J fairCoin F′ M′
  null-int {F′} M′ c = trans (J-add fairCoin {F′} {λ r → c * χT r} M′ (Mc c))
    (trans (+-cong refl (trans (J-scale fairCoin c {χT} MχT) (trans (*-cong refl fair-top) (zeroʳ c)))) (+-identityʳ _))

  pw-bd : ∀ {F F′ : R₁ → ∣A∣} c → (∀ r → Top (lower r) → F r ≈ c) → (∀ r → (Top (lower r) → ⊥) → F r ≤ F′ r) →
    ∀ r → F r ≤ F′ r + c * χT r
  pw-bd {F} {F′} c tp nt r = case {P = Top (lower r)}
    (λ t → ≤-trans (≤-reflexive (trans (tp r t) (trans (sym (*-identityʳ c)) (*-cong refl (sym (χ-in Top r t))))))
      (≤-trans (≤-+ʳ {c * χT r} {F′ r}) (≤-reflexive (+-comm _ _))))
    (λ n → ≤-trans (nt r n) (≤-+ʳ {F′ r} {c * χT r}))

  null-le : ∀ {F F′ : R₁ → ∣A∣} (M : Meas F) (M′ : Meas F′) c → (∀ r → Top (lower r) → F r ≈ c) →
    (∀ r → (Top (lower r) → ⊥) → F r ≤ F′ r) → J fairCoin F M ≤ J fairCoin F′ M′
  null-le {F} {F′} M M′ c tp nt = ≤-trans (J-mono fairCoin M (Meas-⊕ {F′} {λ r → c * χT r} M′ (Mc c)) (pw-bd {F} {F′} c tp nt))
    (≤-reflexive (null-int M′ c))

  -- the all-true point, and the constancy of a shifted test on it
  r⊤ : R₁
  r⊤ = lift (λ _ → true)

  tp-sh : ∀ (T : Hom S WQ WQ) i r → Top (lower r) → map T ⟨$⟩ shiftPt i r ≈ map T ⟨$⟩ shiftPt i r⊤
  tp-sh T i r t = Func.cong (map T) (Func.cong (shiftF i) (lift t))

  -- off the all-true point, the shifted unit piece i lies outside [j, j+1) for i ≠ j
  χ-off′ : ∀ j i r → (i ≡.≡ j → ⊥) → (Top (lower r) → ⊥) → Tri (i <ℕ j) (i ≡.≡ j) (j <ℕ i) →
    map (χI 0 j) ⟨$⟩ shiftPt i r ≈ 0#
  χ-off′ j i r ne nt (tri< a _ _) = base-gt i j r a nt
  χ-off′ j i r ne nt (tri≈ _ b _) = ⊥-elim (ne b)
  χ-off′ j i r ne nt (tri> _ _ c) = base-lt i j r c

  χ-off : ∀ j i → (i ≡.≡ j → ⊥) → ∀ r → (Top (lower r) → ⊥) → map (χI 0 j) ⟨$⟩ shiftPt i r ≈ 0#
  χ-off j i ne r nt = χ-off′ j i r ne nt (<-cmp i j)

  -- the other unit pieces contribute nothing
  term-out : ∀ f j i → (i ≡.≡ j → ⊥) →
    J fairCoin (λ r → map (mulH f (χI 0 j)) ⟨$⟩ shiftPt i r) (Meas-hshift i (mulH f (χI 0 j))) ≈ 0#
  term-out f j i ne = ≤-antisym (≤-trans (null-le (Meas-hshift i (mulH f (χI 0 j))) (Meas-const 0#)
      (map (mulH f (χI 0 j)) ⟨$⟩ shiftPt i r⊤) (tp-sh (mulH f (χI 0 j)) i)
      (λ r nt → ≤-reflexive (trans (*-cong refl (χ-off j i ne r nt)) (zeroʳ _))))
    (≤-reflexive (J-const 0# 0-least))) 0-least

  -- the piece j contributes the whole integral of f ∘ shiftPt j
  term-in : ∀ f j → J fairCoin (λ r → map (mulH f (χI 0 j)) ⟨$⟩ shiftPt j r) (Meas-hshift j (mulH f (χI 0 j)))
    ≈ J fairCoin (λ r → map f ⟨$⟩ shiftPt j r) (Meas-hshift j f)
  term-in f j = ≤-antisym
    (J-mono fairCoin (Meas-hshift j (mulH f (χI 0 j))) (Meas-hshift j f)
      (λ r → ≤-trans (*-mono (map f ⟨$⟩ shiftPt j r) (χI≤1 0 j (shiftPt j r))) (≤-reflexive (*-identityʳ _))))
    (null-le (Meas-hshift j f) (Meas-hshift j (mulH f (χI 0 j))) (map f ⟨$⟩ shiftPt j r⊤) (tp-sh f j)
      (λ r nt → ≤-reflexive (sym (trans (*-cong refl (base-in j r nt)) (*-identityʳ _)))))

  piece : ∀ (f : Hom S WQ WQ) j →
    ∫ᴹ {WQ} lebPre (mulH {WQ} f (χI 0 j)) ≈ J fairCoin (λ r → map f ⟨$⟩ shiftPt j r) (Meas-hshift j f)
  piece f j = trans (∫ᴹ-leb (mulH {WQ} f (χI 0 j)))
    (trans (∑ᶠ-single {λ i → J fairCoin (λ r → map (mulH f (χI 0 j)) ⟨$⟩ shiftPt i r) (Meas-hshift i (mulH f (χI 0 j)))}
      j (term-out f j)) (term-in f j))
