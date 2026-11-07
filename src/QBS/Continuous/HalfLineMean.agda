{-# OPTIONS --safe --without-K #-}

-- The mean of the exponential distribution, `∫₀^∞ x e^{−x} dλ(x) = 1`, multiplied out (no subtraction).
-- With `g = e^{−1}`, `I = ∫₀¹ e^{−u} du` and `K = ∫₀¹ u e^{−u} du` (the true values are `1 − g` and `1 − 2g`):
--   * `xNegExpH : WQ ⇒ WQ`, the test `x ↦ x e^{−x}`, is a morphism (`Meas-⊗` of the identity and `Meas-negExp`);
--   * shift split: `∫₀¹ (n+u) e^{−(n+u)} du = gⁿ (n I + K)` (`negExp-add`, `J` linearity);
--   * value on [0,1]: `K + 2g ≈ 1`.  Route: self-similarity again, on the family `Kⱼ = ∫₀¹ u e^{−2⁻ʲu} du`.
--     Splitting off the first bit gives `Kⱼ = ½ (c (Fⱼ₊₁ + Kⱼ₊₁)) + ¼ Kⱼ₊₁` (`c = e^{−2⁻ʲ⁻¹} ½`), so
--     `wⱼ = hⱼ² Kⱼ + hⱼ qⱼ` (`hⱼ = 2⁻ʲ`, `qⱼ = e^{−hⱼ}`) satisfies the recursion `wⱼ = (1 + qⱼ₊₁) wⱼ₊₁` of
--     `xⱼ = hⱼ Fⱼ`, provided `xⱼ₊₁ + qⱼ₊₁ = 1` at every scale (`GeometricNorm.norm-s`).  The pointwise bound
--     `(1 + t) e^{−t} ≤ 1` gives `wⱼ ≤ hⱼ`, and `hⱼ qⱼ ≤ wⱼ`, so `GeometricNorm.norm` pins `w 0 + q 0 = 1`;
--   * series: `∑ gⁿ (n I + K) = 1` from `I + g = 1` and `K + 2g = 1` (`GeometricNorm.GeoMean`);
--   * `∫ᴹ-leb-xNegExp : ∫ᴹ lebPre xNegExpH ≈ 1#`.
module QBS.Continuous.HalfLineMean where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Bool.Base using (true; false)

open import QBS.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.GeometricNorm using (module GeometricNorm)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineUnit using (module HalfLineUnit)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)

module HalfLineMean (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel; J-fun; J-add; J-scale)
  open Indicators A (lemOf lem₁) using (I-const)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; refl; sym; trans; *-cong; +-cong; *-identityˡ; *-identityʳ; +-comm;
    ≤-trans; ≤-reflexive; ≤-refl; *-mono; ≤-+ʳ; +-mono; +-identityˡ; *-comm)
  R = lowerRealsArch (lemOf lem₁)
  open Arch R using (half; hp; hp-double) renaming (half+half to hh)
  open GeometricNorm A R using (hp≤1; norm; norm-s; w-alg; K-true-alg; K-false-alg; K-rec-alg; KG-alg; shift-alg; ww-alg; K-fin-alg; module GeoMean)
  open Exp A using (natE; pw; bd1)
  open Series A using (∑ᶠ; ∑ᶠ-cong)
  open Integration A using (I; I-cong; I-mono; I-add; I-scale)
  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre; sumF)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-⊕; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; Meas-negExp; negExp-expC-nat; negExp-cong)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion)
  open ExpansionCons A half hh using (expansion-cons)
  open HalfOrder A R using (half≤1)
  open Daniell lem₁ using (L-one)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineNegExp lem₁ using (negExp-add; I-negExp; Meas-negExp-expansion; shift-bd; unit-bd)
  open HalfLineUnit lem₁ using (G; Meas-G; Fun-G; F; q; q-sq; q≤1; q≤F; F≤1; base-at; xs; xs-rec; pt-true; pt-false;
    I-negExp≈F0; I-negExp-unit; hp·e≤1)
  open HalfLineNorm lem₁ using (g; negExp-pw; gb)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the test `x ↦ x e^{−x}`

  xNegExpH : Hom S WQ WQ
  xNegExpH = record
    { map = record { to = λ x → x * negExp x ; cong = λ e → *-cong e (negExp-cong e) }
    ; map-random = λ {γ} m → Meas-⊗ {γ ⟨$⟩_} {λ r → negExp (γ ⟨$⟩ r)} m (Meas-negExp {γ ⟨$⟩_} m) }
  ----------------------------------------------------------------------------
  -- the family `r ↦ u(r) e^{−2⁻ʲ u(r)}` and its integral `Kⱼ`

  KG : ℕ → R₁ → Cut
  KG j r = expansion r * G j r

  Meas-KG : ∀ j → Meas (KG j)
  Meas-KG j = Meas-⊗ {expansion} {G j} (LS Fun-expansion) (Meas-G j)

  KG≤1 : ∀ j r → KG j r ≤ 1#
  KG≤1 j r = ≤-trans (*-mono (expansion r) (negExp≤1 _)) (≤-trans (≤-reflexive (*-identityʳ _)) (expansion≤1 r))

  Fun-KG : ∀ j → Fun (KG j)
  Fun-KG j = Meas→Fun (KG≤1 j) (Meas-KG j)

  KK : ℕ → Cut
  KK j = I fairCoin (KG j) (Fun-KG j)

  c : ℕ → Cut
  c j = q (ℕ.suc j) * half

  c≤1 : ∀ j → c j ≤ 1#
  c≤1 j = ≤-trans (*-mono (q (ℕ.suc j)) half≤1) (≤-trans (≤-reflexive (*-identityʳ _)) (q≤1 _))

  -- splitting off the first bit
  KK-pt : ∀ j x → KG j (consR true x) ≈ c j * G (ℕ.suc j) x + c j * KG (ℕ.suc j) x
  KK-pt j x = trans (*-cong (expansion-cons true x) (pt-true j x))
    (K-true-alg (expansion x) (q (ℕ.suc j)) (G (ℕ.suc j) x))

  KK-pf : ∀ j x → KG j (consR false x) ≈ half * KG (ℕ.suc j) x
  KK-pf j x = trans (*-cong (trans (expansion-cons false x) (+-identityˡ _)) (pt-false j x))
    (K-false-alg (expansion x) (G (ℕ.suc j) x))

  KK-true : ∀ j → I fairCoin (λ x → KG j (consR true x)) (Fun-pre {f = consR true} (Fun-KG j) (measurable-cons true))
    ≈ c j * F (ℕ.suc j) + c j * KK (ℕ.suc j)
  KK-true j = trans (I-add fairCoin (Fun-pre {f = consR true} (Fun-KG j) (measurable-cons true)) Fc Kc (KK-pt j))
    (+-cong (I-scale fairCoin (c j) (Fun-G (ℕ.suc j)) Fc (λ _ → refl))
            (I-scale fairCoin (c j) (Fun-KG (ℕ.suc j)) Kc (λ _ → refl)))
    where
      Fc = Fun-scale (c j) (c≤1 j) (Fun-G (ℕ.suc j))
      Kc = Fun-scale (c j) (c≤1 j) (Fun-KG (ℕ.suc j))

  KK-false : ∀ j → I fairCoin (λ x → KG j (consR false x)) (Fun-pre {f = consR false} (Fun-KG j) (measurable-cons false))
    ≈ half * KK (ℕ.suc j)
  KK-false j = I-scale fairCoin half (Fun-KG (ℕ.suc j)) (Fun-pre {f = consR false} (Fun-KG j) (measurable-cons false)) (KK-pf j)

  KK-split : ∀ j → KK j ≈ half * (c j * F (ℕ.suc j) + c j * KK (ℕ.suc j)) + half * (half * KK (ℕ.suc j))
  KK-split j = trans (firstBit-fun (Fun-KG j)) (+-cong (*-cong refl (KK-true j)) (*-cong refl (KK-false j)))

  ----------------------------------------------------------------------------
  -- the combination `wⱼ = hⱼ² Kⱼ + hⱼ qⱼ`

  zz ww : ℕ → Cut
  zz j = (hp j * hp j) * KK j
  ww j = zz j + hp j * q j

  -- `xⱼ + qⱼ = 1` at every scale
  xs-pin : ∀ j → xs j + q j ≈ 1#
  xs-pin = norm-s q xs q-sq q≤1 (λ m → proj₁ (base-at m)) (λ m → proj₂ (base-at m)) xs-rec
    (λ m → *-mono (hp m) (q≤F m)) (λ m → ≤-trans (*-mono (hp m) (F≤1 m)) (≤-reflexive (*-identityʳ _)))

  ww-rec : ∀ j → ww j ≈ (1# + q (ℕ.suc j)) * ww (ℕ.suc j)
  ww-rec j = trans (+-cong (trans (*-cong refl (KK-split j)) (K-rec-alg (hp j) (q (ℕ.suc j)) (F (ℕ.suc j)) (KK (ℕ.suc j))))
                           (*-cong (sym (hp-double j)) (q-sq j)))
    (w-alg (hp (ℕ.suc j)) (q (ℕ.suc j)) (F (ℕ.suc j)) (KK (ℕ.suc j)) (xs-pin (ℕ.suc j)))

  -- `hⱼ q ≤ wⱼ`
  ww-lo : ∀ m → hp m * q m ≤ ww m
  ww-lo m = ≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))

  -- pointwise `hⱼ (u e^{−hⱼu}) + e^{−hⱼu} ≤ 1`, from `(1 + t) e^{−t} ≤ e^t e^{−t} = 1`
  KG-bd : ∀ m r → hp m * KG m r + G m r ≤ 1#
  KG-bd m r = ≤-trans (≤-reflexive (KG-alg (hp m) (expansion r) (G m r)))
    (≤-trans (*-mono (G m r) (1+≤expC (lemOf lem₁) (hp m * expansion r))) (≤-reflexive e1))
    where
      e1 : G m r * expC (lemOf lem₁) (hp m * expansion r) ≈ 1#
      e1 = negExp-expC-nat (hp m * expansion r) 1 (bd1 (hp·e≤1 m r))

  Fun-KGbd : ∀ m → Fun (λ r → hp m * KG m r + G m r)
  Fun-KGbd m = sumF (Fun-scale (hp m) (hp≤1 m) (Fun-KG m)) (Fun-G m) (λ _ → refl) (KG-bd m)

  -- `hⱼ Kⱼ + Fⱼ ≤ 1`
  KK-bd : ∀ m → hp m * KK m + F m ≤ 1#
  KK-bd m = ≤-trans (≤-reflexive (sym (trans (I-add fairCoin (Fun-KGbd m) Hk (Fun-G m) (λ _ → refl))
                                             (+-cong (I-scale fairCoin (hp m) (Fun-KG m) Hk (λ _ → refl)) refl))))
    (≤-trans (I-mono fairCoin (Fun-KGbd m) (Fun-const 1# ≤-refl) (KG-bd m))
             (≤-reflexive (I-const fairCoin L-one 1# ≤-refl)))
    where Hk = Fun-scale (hp m) (hp≤1 m) (Fun-KG m)

  -- `wⱼ ≤ hⱼ`
  ww-hi : ∀ m → ww m ≤ hp m
  ww-hi m = ≤-trans (+-mono ≤-refl (*-mono (hp m) (q≤F m)))
    (≤-trans (≤-reflexive (ww-alg (hp m) (KK m) (F m)))
      (≤-trans (*-mono (hp m) (KK-bd m)) (≤-reflexive (*-identityʳ _))))

  ww-pin : ww 0 + q 0 ≈ 1#
  ww-pin = norm q ww q-sq q≤1 (λ m → proj₁ (base-at m)) (λ m → proj₂ (base-at m)) ww-rec ww-lo ww-hi

  -- `K = ∫₀¹ u e^{−u} du`
  Meas-xe : Meas (λ r → expansion r * negExp (expansion r))
  Meas-xe = Meas-⊗ {expansion} {λ r → negExp (expansion r)} (LS Fun-expansion) Meas-negExp-expansion

  K : Cut
  K = J fairCoin (λ r → expansion r * negExp (expansion r)) Meas-xe

  K≈KK0 : K ≈ KK 0
  K≈KK0 = trans (J-cong fairCoin Meas-xe (Meas-KG 0) (λ r → *-cong refl (negExp-cong (sym (*-identityˡ _)))))
    (trans (J-irrel fairCoin (Meas-KG 0) (LS (Fun-KG 0))) (J-fun fairCoin (Fun-KG 0)))

  -- `K + 2g = 1`
  K-pin : K + (g + g) ≈ 1#
  K-pin = trans (+-cong K≈KK0 refl) (trans (sym (K-fin-alg (KK 0) (q 0))) ww-pin)

  ----------------------------------------------------------------------------
  -- the shift split `∫₀¹ (n+u) e^{−(n+u)} du = gⁿ (n I + K)`

  Meas-A : ∀ n → Meas (λ r → natE n * negExp (expansion r))
  Meas-A n = Meas-⊗ {λ _ → natE n} {λ r → negExp (expansion r)} (Meas-const (natE n)) Meas-negExp-expansion

  Meas-AB : ∀ n → Meas (λ r → natE n * negExp (expansion r) + expansion r * negExp (expansion r))
  Meas-AB n = Meas-⊕ {λ r → natE n * negExp (expansion r)} {λ r → expansion r * negExp (expansion r)} (Meas-A n) Meas-xe

  Meas-xshift : ∀ n → Meas (λ r → shiftPt n r * negExp (shiftPt n r))
  Meas-xshift n = Meas-hshift n xNegExpH

  shift-pt : ∀ n r → shiftPt n r * negExp (shiftPt n r) ≈
    negExp (natE n) * (natE n * negExp (expansion r) + expansion r * negExp (expansion r))
  shift-pt n r = trans (*-cong refl (negExp-add {natE n} {expansion r} {n} {1} {ℕ.suc n} ≤-refl (unit-bd r) (shift-bd n r)))
    (shift-alg (natE n) (expansion r) (negExp (natE n)) (negExp (expansion r)))

  shift-split : ∀ n → J fairCoin (λ r → shiftPt n r * negExp (shiftPt n r)) (Meas-xshift n) ≈
    negExp (natE n) * (natE n * I-negExp + K)
  shift-split n = trans
    (J-cong fairCoin (Meas-xshift n) (Meas-⊗ {λ _ → negExp (natE n)} (Meas-const (negExp (natE n))) (Meas-AB n)) (shift-pt n))
    (trans (J-scale fairCoin (negExp (natE n)) (Meas-AB n))
      (*-cong refl (trans (J-add fairCoin (Meas-A n) Meas-xe)
        (+-cong (J-scale fairCoin (natE n) Meas-negExp-expansion) refl))))

  ----------------------------------------------------------------------------
  -- the mean

  ∫ᴹ-leb-xNegExp-split : ∫ᴹ {WQ} lebPre xNegExpH ≈ ∑ᶠ (λ n → pw g n * (natE n * I-negExp + K))
  ∫ᴹ-leb-xNegExp-split = trans (∫ᴹ-leb xNegExpH)
    (∑ᶠ-cong (λ n → trans (shift-split n) (*-cong (negExp-pw n) refl)))

  -- `∫₀^∞ x e^{−x} dx = 1`
  ∫ᴹ-leb-xNegExp : ∫ᴹ {WQ} lebPre xNegExpH ≈ 1#
  ∫ᴹ-leb-xNegExp = trans ∫ᴹ-leb-xNegExp-split (GeoMean.total g I-negExp K I-negExp-unit K-pin gb)
