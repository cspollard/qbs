{-# OPTIONS --safe --without-K #-}

-- The second moment of the exponential distribution, `∫₀^∞ x² e^{−x} dλ(x) = 2`, multiplied out (no subtraction).
-- Mirrors `HalfLineMean`.  With `g = e^{−1}`, `I = ∫₀¹ e^{−u}`, `K = ∫₀¹ u e^{−u}` and `L = ∫₀¹ u² e^{−u}` (true values
-- `1 − g`, `1 − 2g`, `2 − 5g`):
--   * `x²NegExpH : WQ ⇒ WQ`, the test `x ↦ x² e^{−x}`, is a morphism;
--   * the family `LG j r = u(r)² e^{−2⁻ʲ u(r)}`, `LL j = ∫ LG j`, split at the first bit with the one-step facts
--     `(½ + ½e)² (q G) = d G + (q ½)(e G) + d (e² G)` and `(½e)² G = ¼ (e² G)` (`Analysis/GeometricMoment2`), the sum of three
--     terms integrated with `J` (so no bound `≤ 1` is needed on partial sums);
--   * `x j = ½ hⱼ³ LL j + (hⱼ + ½hⱼ²) qⱼ` satisfies `x j = (1 + q (j+1)) x (j+1)` given the pins `a F + q = 1` (`HalfLineUnit`)
--     and `a² K + a q + q = 1` (the mean, at every scale: `ww-pin-s`), and `hⱼ q ≤ x j ≤ hⱼ`; so `GeometricNorm.norm` pins
--     `x 0 + q 0 = 1`, which is `L + 5g ≈ 2` (`L-pin`);
--   * shift split: `∫₀¹ (n+u)² e^{−(n+u)} du = gⁿ (n² I + 2n K + L)`, and the series `GeoMom2.total`;
--   * `∫ᴹ-leb-x²NegExp : ∫ᴹ lebPre x²NegExpH ≈ 1# + 1#`.
module QBS.Continuous.HalfLineMoment2 where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)
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
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.GeometricNorm using (module GeometricNorm)
open import QBS.Analysis.GeometricMoment2 using (module GeometricMoment2)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineUnit using (module HalfLineUnit)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.HalfLineMean using (module HalfLineMean)

module HalfLineMoment2 (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel; J-fun; J-add; J-scale)
  open Indicators A (lemOf lem₁) using (I-const)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; refl; sym; trans; *-cong; +-cong; *-identityˡ; *-identityʳ; *-assoc;
    ≤-trans; ≤-reflexive; ≤-refl; *-mono)
  R = lowerRealsArch (lemOf lem₁)
  open Arch R using (half; hp; hp-zero; hp-double) renaming (half+half to hh)
  open GeometricNorm A R using (hp≤1; norm; *-monoˡ)
  open GeometricMoment2 A R using (L-true-alg; L-false-alg; Lsplit; x2-rec-alg; x2-lo; x2-hi; L5-alg; Lsplit-def; shift-alg2; module GeoMom2)
  open Exp A using (natE; pw)
  open Series A using (∑ᶠ; ∑ᶠ-cong)
  open Integration A using (I; I-cong; I-mono; I-add; I-scale)
  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-⊕; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open NegExp (lemOf lem₁) using (negExp; negExp≤1; Meas-negExp)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion)
  open ExpansionCons A half hh using (expansion-cons)
  open Daniell lem₁ using (L-one)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open HalfLineNegExp lem₁ using (negExp-add; I-negExp; Meas-negExp-expansion; shift-bd; unit-bd)
  open HalfLineUnit lem₁ using (negExp-cong; G; Meas-G; Fun-G; F; q; q-sq; q≤1; q≤F; base-at; pt-true; pt-false; I-negExp-unit)
  open HalfLineNorm lem₁ using (g; negExp-pw; gb)
  open HalfLineMean lem₁ using (KG; Meas-KG; Fun-KG; KK; K; Meas-xe; K-pin; xs-pin; ww; ww-rec; ww-lo; ww-hi)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the test `x ↦ x² e^{−x}`

  x²NegExpH : Hom S WQ WQ
  x²NegExpH = record
    { map = record { to = λ x → (x * x) * negExp x ; cong = λ e → *-cong (*-cong e e) (negExp-cong e) }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → (γ ⟨$⟩ r) * (γ ⟨$⟩ r)} {λ r → negExp (γ ⟨$⟩ r)}
        (Meas-⊗ {γ ⟨$⟩_} {γ ⟨$⟩_} m m) (Meas-negExp {γ ⟨$⟩_} m) }

  ----------------------------------------------------------------------------
  -- the family `r ↦ u(r)² e^{−2⁻ʲ u(r)}` and its integral `Lⱼ`

  LG : ℕ → R₁ → Cut
  LG j r = (expansion r * expansion r) * G j r

  Meas-ee : Meas (λ r → expansion r * expansion r)
  Meas-ee = Meas-⊗ {expansion} {expansion} (LS Fun-expansion) (LS Fun-expansion)

  Meas-LG : ∀ j → Meas (LG j)
  Meas-LG j = Meas-⊗ {λ r → expansion r * expansion r} {G j} Meas-ee (Meas-G j)

  ee≤1 : ∀ r → expansion r * expansion r ≤ 1#
  ee≤1 r = ≤-trans (*-mono (expansion r) (expansion≤1 r)) (≤-trans (≤-reflexive (*-identityʳ _)) (expansion≤1 r))

  LG≤1 : ∀ j r → LG j r ≤ 1#
  LG≤1 j r = ≤-trans (*-mono (expansion r * expansion r) (negExp≤1 _)) (≤-trans (≤-reflexive (*-identityʳ _)) (ee≤1 r))

  Fun-LG : ∀ j → Fun (LG j)
  Fun-LG j = Meas→Fun (LG≤1 j) (Meas-LG j)

  LL : ℕ → Cut
  LL j = I fairCoin (LG j) (Fun-LG j)

  -- the three terms of the first-bit `true` branch
  d e : ℕ → Cut
  d j = q (ℕ.suc j) * (half * half)
  e j = q (ℕ.suc j) * half

  T1 T2 T3 : ℕ → R₁ → Cut
  T1 j x = d j * G (ℕ.suc j) x
  T2 j x = e j * KG (ℕ.suc j) x
  T3 j x = d j * LG (ℕ.suc j) x

  -- splitting off the first bit, pointwise
  LL-pt-true : ∀ j x → LG j (consR true x) ≈ T1 j x + (T2 j x + T3 j x)
  LL-pt-true j x = trans (*-cong (*-cong (expansion-cons true x) (expansion-cons true x)) (pt-true j x))
    (L-true-alg (expansion x) (q (ℕ.suc j)) (G (ℕ.suc j) x))

  LL-pt-false : ∀ j x → LG j (consR false x) ≈ (half * half) * LG (ℕ.suc j) x
  LL-pt-false j x = trans (*-cong (*-cong e0 e0) (pt-false j x)) (L-false-alg (expansion x) (G (ℕ.suc j) x))
    where
      e0 = trans (expansion-cons false x) (OmegaSemiring.+-identityˡ A _)

  ----------------------------------------------------------------------------
  -- integrating the first-bit branches

  Meas-LL-true : ∀ j → Meas (λ x → LG j (consR true x))
  Meas-LL-true j = LS (Fun-pre {f = consR true} (Fun-LG j) (measurable-cons true))

  Meas-T1 : ∀ j → Meas (T1 j)
  Meas-T1 j = Meas-⊗ {λ _ → d j} (Meas-const (d j)) (Meas-G (ℕ.suc j))

  Meas-T2 : ∀ j → Meas (T2 j)
  Meas-T2 j = Meas-⊗ {λ _ → e j} (Meas-const (e j)) (Meas-KG (ℕ.suc j))

  Meas-T3 : ∀ j → Meas (T3 j)
  Meas-T3 j = Meas-⊗ {λ _ → d j} (Meas-const (d j)) (Meas-LG (ℕ.suc j))

  Meas-T23 : ∀ j → Meas (λ x → T2 j x + T3 j x)
  Meas-T23 j = Meas-⊕ {T2 j} {T3 j} (Meas-T2 j) (Meas-T3 j)

  Meas-sum-true : ∀ j → Meas (λ x → T1 j x + (T2 j x + T3 j x))
  Meas-sum-true j = Meas-⊕ {T1 j} {λ x → T2 j x + T3 j x} (Meas-T1 j) (Meas-T23 j)

  -- `J` of a function agrees with the bounded integral (the measurability proofs are irrelevant)
  J-G : ∀ j → J fairCoin (G j) (Meas-G j) ≈ F j
  J-G j = trans (J-irrel fairCoin (Meas-G j) (LS (Fun-G j))) (J-fun fairCoin (Fun-G j))

  J-KG : ∀ j → J fairCoin (KG j) (Meas-KG j) ≈ KK j
  J-KG j = trans (J-irrel fairCoin (Meas-KG j) (LS (Fun-KG j))) (J-fun fairCoin (Fun-KG j))

  J-LG : ∀ j → J fairCoin (LG j) (Meas-LG j) ≈ LL j
  J-LG j = trans (J-irrel fairCoin (Meas-LG j) (LS (Fun-LG j))) (J-fun fairCoin (Fun-LG j))

  J1 : ∀ j → J fairCoin (T1 j) (Meas-T1 j) ≈ d j * F (ℕ.suc j)
  J1 j = trans (J-scale fairCoin (d j) (Meas-G (ℕ.suc j))) (*-cong refl (J-G (ℕ.suc j)))

  J2 : ∀ j → J fairCoin (T2 j) (Meas-T2 j) ≈ e j * KK (ℕ.suc j)
  J2 j = trans (J-scale fairCoin (e j) (Meas-KG (ℕ.suc j))) (*-cong refl (J-KG (ℕ.suc j)))

  J3 : ∀ j → J fairCoin (T3 j) (Meas-T3 j) ≈ d j * LL (ℕ.suc j)
  J3 j = trans (J-scale fairCoin (d j) (Meas-LG (ℕ.suc j))) (*-cong refl (J-LG (ℕ.suc j)))

  LL-true : ∀ j → I fairCoin (λ x → LG j (consR true x)) (Fun-pre {f = consR true} (Fun-LG j) (measurable-cons true))
    ≈ d j * F (ℕ.suc j) + (e j * KK (ℕ.suc j) + d j * LL (ℕ.suc j))
  LL-true j = trans (sym (J-fun fairCoin (Fun-pre {f = consR true} (Fun-LG j) (measurable-cons true))))
    (trans (J-cong fairCoin (Meas-LL-true j) (Meas-sum-true j) (LL-pt-true j))
      (trans (J-add fairCoin (Meas-T1 j) (Meas-T23 j))
        (+-cong (J1 j) (trans (J-add fairCoin (Meas-T2 j) (Meas-T3 j)) (+-cong (J2 j) (J3 j))))))

  LL-false : ∀ j → I fairCoin (λ x → LG j (consR false x)) (Fun-pre {f = consR false} (Fun-LG j) (measurable-cons false))
    ≈ (half * half) * LL (ℕ.suc j)
  LL-false j = I-scale fairCoin (half * half) (Fun-LG (ℕ.suc j)) (Fun-pre {f = consR false} (Fun-LG j) (measurable-cons false))
    (LL-pt-false j)

  LL-split : ∀ j → LL j ≈ Lsplit (q (ℕ.suc j)) (F (ℕ.suc j)) (KK (ℕ.suc j)) (LL (ℕ.suc j))
  LL-split j = trans (firstBit-fun (Fun-LG j))
    (trans (+-cong (*-cong refl (LL-true j)) (*-cong refl (LL-false j)))
      (Lsplit-def (q (ℕ.suc j)) (F (ℕ.suc j)) (KK (ℕ.suc j)) (LL (ℕ.suc j))))

  ----------------------------------------------------------------------------
  -- the pins at every scale, and the combination `x j`

  ww-pin-s : ∀ j → ww j + q j ≈ 1#
  ww-pin-s = GeometricNorm.norm-s A R q ww q-sq q≤1 (λ m → proj₁ (base-at m)) (λ m → proj₂ (base-at m)) ww-rec ww-lo ww-hi

  x2 : ℕ → Cut
  x2 j = (hp (ℕ.suc j) * (hp j * hp j)) * LL j + (hp j + hp (ℕ.suc j) * hp j) * q j

  x2-rec : ∀ j → x2 j ≈ (1# + q (ℕ.suc j)) * x2 (ℕ.suc j)
  x2-rec j = trans (+-cong (*-cong refl (LL-split j)) (*-cong refl (q-sq j)))
    (x2-rec-alg (hp (ℕ.suc j)) (hp j) (q (ℕ.suc j)) (F (ℕ.suc j)) (KK (ℕ.suc j)) (LL (ℕ.suc j)) (hp-double j)
      (xs-pin (ℕ.suc j)) (ww-pin-s (ℕ.suc j)))

  -- `hⱼ Lⱼ ≤ Fⱼ`, pointwise `hⱼ u² e^{−hⱼu} ≤ e^{−hⱼu}`
  hL≤F : ∀ j → hp j * LL j ≤ F j
  hL≤F j = ≤-trans (≤-reflexive (sym (I-scale fairCoin (hp j) (Fun-LG j) Hl (λ _ → refl))))
    (I-mono fairCoin Hl (Fun-G j) pt)
    where
      Hl = Fun-scale (hp j) (hp≤1 j) (Fun-LG j)
      pt : ∀ r → hp j * LG j r ≤ G j r
      pt r = ≤-trans (≤-reflexive (sym (*-assoc (hp j) (expansion r * expansion r) (G j r))))
        (≤-trans (*-monoˡ (G j r) (≤-trans (*-mono (hp j) (ee≤1 r)) (≤-trans (≤-reflexive (*-identityʳ _)) (hp≤1 j))))
                 (≤-reflexive (*-identityˡ _)))

  x2-pin : x2 0 + q 0 ≈ 1#
  x2-pin = norm q x2 q-sq q≤1 (λ m → proj₁ (base-at m)) (λ m → proj₂ (base-at m)) x2-rec
    (λ m → x2-lo (hp (ℕ.suc m)) (hp m) (q m) (LL m))
    (λ m → x2-hi (hp (ℕ.suc m)) (hp m) (q m) (F m) (LL m) (hp-double m) (xs-pin m) (hL≤F m) (q≤F m))

  -- `L = ∫₀¹ u² e^{−u} du`
  C2f : R₁ → Cut
  C2f r = (expansion r * expansion r) * negExp (expansion r)

  Meas-C2 : Meas C2f
  Meas-C2 = Meas-⊗ {λ r → expansion r * expansion r} {λ r → negExp (expansion r)} Meas-ee Meas-negExp-expansion

  L : Cut
  L = J fairCoin C2f Meas-C2

  L≈LL0 : L ≈ LL 0
  L≈LL0 = trans (J-cong fairCoin Meas-C2 (Meas-LG 0) (λ r → *-cong refl (negExp-cong (sym (*-identityˡ _))))) (J-LG 0)

  -- `L + 5g = 2`
  L-pin : L + (((g + g) + (g + g)) + g) ≈ 1# + 1#
  L-pin = L5-alg L g (trans (+-cong (+-cong (*-cong refl L≈LL0) refl) refl) x2-pin)

  ----------------------------------------------------------------------------
  -- the shift split `∫₀¹ (n+u)² e^{−(n+u)} du = gⁿ (n² I + 2n K + L)`

  A2f B2f : ℕ → R₁ → Cut
  A2f n r = (natE n * natE n) * negExp (expansion r)
  B2f n r = (natE n + natE n) * (expansion r * negExp (expansion r))

  Meas-A2 : ∀ n → Meas (A2f n)
  Meas-A2 n = Meas-⊗ {λ _ → natE n * natE n} {λ r → negExp (expansion r)} (Meas-const (natE n * natE n)) Meas-negExp-expansion

  Meas-B2 : ∀ n → Meas (B2f n)
  Meas-B2 n = Meas-⊗ {λ _ → natE n + natE n} {λ r → expansion r * negExp (expansion r)} (Meas-const (natE n + natE n)) Meas-xe

  Meas-BC2 : ∀ n → Meas (λ r → B2f n r + C2f r)
  Meas-BC2 n = Meas-⊕ {B2f n} {C2f} (Meas-B2 n) Meas-C2

  Meas-ABC2 : ∀ n → Meas (λ r → A2f n r + (B2f n r + C2f r))
  Meas-ABC2 n = Meas-⊕ {A2f n} {λ r → B2f n r + C2f r} (Meas-A2 n) (Meas-BC2 n)

  Meas-x2shift : ∀ n → Meas (λ r → (shiftPt n r * shiftPt n r) * negExp (shiftPt n r))
  Meas-x2shift n = Meas-hshift n x²NegExpH

  shift-pt : ∀ n r → (shiftPt n r * shiftPt n r) * negExp (shiftPt n r) ≈ negExp (natE n) * (A2f n r + (B2f n r + C2f r))
  shift-pt n r = trans (*-cong refl (negExp-add {natE n} {expansion r} {n} {1} {ℕ.suc n} ≤-refl (unit-bd r) (shift-bd n r)))
    (shift-alg2 (natE n) (expansion r) (negExp (natE n)) (negExp (expansion r)))

  shift-split : ∀ n → J fairCoin (λ r → (shiftPt n r * shiftPt n r) * negExp (shiftPt n r)) (Meas-x2shift n) ≈
    negExp (natE n) * ((natE n * natE n) * I-negExp + ((natE n + natE n) * K + L))
  shift-split n = trans
    (J-cong fairCoin (Meas-x2shift n) (Meas-⊗ {λ _ → negExp (natE n)} (Meas-const (negExp (natE n))) (Meas-ABC2 n)) (shift-pt n))
    (trans (J-scale fairCoin (negExp (natE n)) (Meas-ABC2 n))
      (*-cong refl (trans (J-add fairCoin (Meas-A2 n) (Meas-BC2 n))
        (+-cong (J-scale fairCoin (natE n * natE n) Meas-negExp-expansion)
          (trans (J-add fairCoin (Meas-B2 n) Meas-C2)
            (+-cong (J-scale fairCoin (natE n + natE n) Meas-xe) refl))))))

  ----------------------------------------------------------------------------
  -- the second moment

  open GeoMom2 using (total; term)

  -- the series of `GeoMom2` (stated with `term`, so that no unfolding of it is needed at the end)
  split-pt : ∀ n → J fairCoin (λ r → (shiftPt n r * shiftPt n r) * negExp (shiftPt n r)) (Meas-x2shift n)
    ≈ term g I-negExp K L I-negExp-unit K-pin L-pin gb n
  split-pt n = trans (shift-split n) (*-cong (negExp-pw n) refl)

  ∫ᴹ-leb-x²NegExp-split : ∫ᴹ {WQ} lebPre x²NegExpH ≈ ∑ᶠ (term g I-negExp K L I-negExp-unit K-pin L-pin gb)
  ∫ᴹ-leb-x²NegExp-split = trans (∫ᴹ-leb x²NegExpH) (∑ᶠ-cong split-pt)

  -- `∫₀^∞ x² e^{−x} dx = 2`
  ∫ᴹ-leb-x²NegExp : ∫ᴹ {WQ} lebPre x²NegExpH ≈ 1# + 1#
  ∫ᴹ-leb-x²NegExp = trans ∫ᴹ-leb-x²NegExp-split (total g I-negExp K L I-negExp-unit K-pin L-pin gb)
