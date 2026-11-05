{-# OPTIONS --safe --without-K #-}

-- `∫ e^{−x} dλ(x)` over [0,∞) against the Lebesgue measure `lebPre` of `Continuous/HalfLine`.
--   * `negExpH : WQ ⇒ WQ`, the test `x ↦ e^{−x}`, is a morphism (`Meas-negExp`, `negExp-anti`);
--   * `negExp-add`: `e^{−(x+y)} = e^{−x} e^{−y}` whenever `x`, `y` and `x + y` are bounded by naturals
--     (from `exp-add` and `e^{−x} e^x = 1`, `negExp-expC-nat`, with no cancellation: the product of the
--     two identities is multiplied against `e^{−(x+y)}`);
--   * `∫ᴹ-leb-negExp`: `∫ e^{−x} dλ ≈ ∑ᶠ n. J (u ↦ e^{−(n+u)})`;
--   * `∫ᴹ-leb-negExp-split`: `∫ e^{−x} dλ ≈ ∑ᶠ n. e^{−n} · ∫₀¹ e^{−u} du`.
-- The value `∫₀¹ e^{−u} du = 1 − e^{−1}` is not computed here.
module QBS.Continuous.HalfLineNegExp where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Algebra.Bundles using (CommutativeSemiring)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.ExpLower using (expC; module Add)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)

module HalfLineNegExp (lem₁ : LEM₁) where
  open HalfLine lem₁
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-scale)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 1#; refl; sym; trans; *-cong; *-identityʳ; ≤-trans; ≤-reflexive;
    +-mono; ≤-refl; +-identityˡ; commutativeSemiring)
  open Exp A using (natE)
  open Series A using (∑ᶠ; ∑ᶠ-cong)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; Meas-negExp; negExp-expC-nat)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the test `x ↦ e^{−x}`

  negExpH : Hom S WQ WQ
  negExpH = record
    { map = record { to = negExp ; cong = λ e → negExp-anti (proj₂ e) , negExp-anti (proj₁ e) }
    ; map-random = λ {γ} m → Meas-negExp {γ ⟨$⟩_} m }

  Meas-negExp-shift : ∀ n → Meas (λ r → negExp (shiftPt n r))
  Meas-negExp-shift n = Meas-negExp {shiftPt n} (Meas-shift n)

  -- the integral of `e^{−x}` over [0,∞), as a sum over the unit intervals
  ∫ᴹ-leb-negExp : ∫ᴹ {WQ} lebPre negExpH ≈ ∑ᶠ (λ n → J fairCoin (λ r → negExp (shiftPt n r)) (Meas-negExp-shift n))
  ∫ᴹ-leb-negExp = ∫ᴹ-leb negExpH

  ----------------------------------------------------------------------------
  -- multiplicativity on bounded arguments

  private
    module CS = CommutativeSemiring commutativeSemiring

  open import Algebra.Solver.CommutativeMonoid CS.*-commutativeMonoid renaming (_⊕_ to _⊙_; _⊜_ to _≐_)
  module AD x y = Add (lemOf lem₁) x y

  negExp-add : ∀ {x y N M K} → x ≤ natE N → y ≤ natE M → x + y ≤ natE K →
    negExp (x + y) ≈ negExp x * negExp y
  negExp-add {x} {y} {N} {M} {K} hx hy hxy = trans (sym (*-identityʳ P))
    (trans (*-cong refl (sym (trans (*-cong (negExp-expC-nat x N hx) (negExp-expC-nat y M hy)) (*-identityʳ 1#))))
      (trans (solve 5 (λ P nx E ny F → P ⊙ ((nx ⊙ E) ⊙ (ny ⊙ F)) ≐ (nx ⊙ ny) ⊙ (P ⊙ (E ⊙ F))) refl
                P (negExp x) (expC (lemOf lem₁) x) (negExp y) (expC (lemOf lem₁) y))
        (trans (*-cong refl (*-cong refl (sym (AD.exp-add x y))))
          (trans (*-cong refl (negExp-expC-nat (x + y) K hxy)) (*-identityʳ _)))))
    where P = negExp (x + y)

  ----------------------------------------------------------------------------
  -- the decomposition `∑ₙ e^{−n} · ∫₀¹ e^{−u} du`

  Meas-negExp-expansion : Meas (λ r → negExp (expansion r))
  Meas-negExp-expansion = Meas-negExp {expansion} (LS Fun-expansion)

  -- `∫₀¹ e^{−u} du`, left uncomputed
  I-negExp : Cut
  I-negExp = J fairCoin (λ r → negExp (expansion r)) Meas-negExp-expansion

  shift-bd : ∀ n r → shiftPt n r ≤ natE (ℕ.suc n)
  shift-bd n r = +-mono (≤-refl {natE n}) (expansion≤1 r)

  unit-bd : ∀ r → expansion r ≤ natE 1
  unit-bd r = ≤-trans (expansion≤1 r) (≤-reflexive (sym (+-identityˡ 1#)))

  -- `∫₀¹ e^{−(n+u)} du = e^{−n} ∫₀¹ e^{−u} du`
  negExp-shift-split : ∀ n → J fairCoin (λ r → negExp (shiftPt n r)) (Meas-negExp-shift n) ≈ negExp (natE n) * I-negExp
  negExp-shift-split n = trans
    (J-cong fairCoin (Meas-negExp-shift n) (Meas-⊗ {λ _ → negExp (natE n)} {λ r → negExp (expansion r)}
       (Meas-const (negExp (natE n))) Meas-negExp-expansion)
       (λ r → negExp-add {natE n} {expansion r} {n} {1} {ℕ.suc n} ≤-refl (unit-bd r) (shift-bd n r)))
    (J-scale fairCoin (negExp (natE n)) {λ r → negExp (expansion r)} Meas-negExp-expansion)

  ∫ᴹ-leb-negExp-split : ∫ᴹ {WQ} lebPre negExpH ≈ ∑ᶠ (λ n → negExp (natE n) * I-negExp)
  ∫ᴹ-leb-negExp-split = trans ∫ᴹ-leb-negExp (∑ᶠ-cong negExp-shift-split)
