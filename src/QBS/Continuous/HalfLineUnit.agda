{-# OPTIONS --safe --without-K #-}

-- The integral on the unit interval: `∫₀¹ e^{−u} du + e^{−1} = 1`, multiplied out.
-- Route: self-similarity (as `UniformMean`), not Riemann sums.  With `F j = ∫₀¹ e^{−2⁻ʲ u} du` and
-- `q j = e^{−2⁻ʲ}`, splitting off the first bit gives
--   `F j = ½ (q (j+1) F (j+1)) + ½ F (j+1)`,
-- i.e. `x j = (1 + q (j+1)) x (j+1)` for `x j = 2⁻ʲ F j`, using `e^{−(a+b)} = e^{−a} e^{−b}`
-- (`negExp-add`).  The algebra that pins `x 0 + q 0 = 1` from this recursion, `q j = q (j+1)²`, the
-- bounds `q j ≤ F j ≤ 1`, and `1 + h ≤ eʰ ≤ 1 + h + h²` is `Analysis/GeometricNorm.norm`.
-- Exported: `I-negExp-unit : I-negExp + e^{−1} ≈ 1`.
module QBS.Continuous.HalfLineUnit where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Bool.Base using (true; false)

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
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.GeometricNorm using (module GeometricNorm)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)

module HalfLineUnit (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel; J-fun)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; refl; sym; trans; *-cong; +-cong; *-identityˡ; *-identityʳ;
    +-identityˡ; ≤-trans; ≤-reflexive; ≤-refl; *-mono; ≤-+ʳ)
  R = lowerRealsArch (lemOf lem₁)
  open Arch R using (half; hp; hp-double) renaming (half+half to hh)
  open GeometricNorm A R
  open Exp A using (natE)
  open Integration A using (I; I-cong; I-mono; I-scale)
  open Measurable A using (Fun; Fun-const; Fun-scale; Fun-pre)
  open Meas (lemOf lem₁) using (Meas)
  open LevelSets (lemOf lem₁) using (LS)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; Meas-negExp; negExp-expC-nat)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion)
  open ExpansionCons A half hh using (expansion-cons)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Indicators A (lemOf lem₁) using (I-const)
  open HalfLineNegExp lem₁ using (negExp-add; I-negExp; Meas-negExp-expansion)

  negExp-cong : ∀ {x y} → x ≈ y → negExp x ≈ negExp y
  negExp-cong e = negExp-anti (proj₂ e) , negExp-anti (proj₁ e)

  ----------------------------------------------------------------------------
  -- the family `r ↦ e^{−2⁻ʲ u(r)}` and its integral

  G : ℕ → R₁ → Cut
  G j r = negExp (hp j * expansion r)

  Meas-G : ∀ j → Meas (G j)
  Meas-G j = Meas-negExp {λ r → hp j * expansion r} (LS (Fun-scale (hp j) (hp≤1 j) Fun-expansion))

  Fun-G : ∀ j → Fun (G j)
  Fun-G j = Meas→Fun (λ r → negExp≤1 _) (Meas-G j)

  F : ℕ → Cut
  F j = I fairCoin (G j) (Fun-G j)

  q : ℕ → Cut
  q j = negExp (hp j)

  bd1 : ∀ {x} → x ≤ 1# → x ≤ natE 1
  bd1 h = ≤-trans h (≤-reflexive (sym (+-identityˡ 1#)))

  bd2 : ∀ {x} → x ≤ 1# → x ≤ natE 2
  bd2 h = ≤-trans (bd1 h) ≤-+ʳ

  hp·e≤1 : ∀ j r → hp j * expansion r ≤ 1#
  hp·e≤1 j r = ≤-trans (*-mono (hp j) (expansion≤1 r)) (≤-trans (≤-reflexive (*-identityʳ _)) (hp≤1 j))

  q-sq : ∀ m → q m ≈ q (ℕ.suc m) * q (ℕ.suc m)
  q-sq m = trans (negExp-cong (sym (hp-double m)))
    (negExp-add {hp (ℕ.suc m)} {hp (ℕ.suc m)} {1} {1} {2} (bd1 (hp≤1 (ℕ.suc m))) (bd1 (hp≤1 (ℕ.suc m)))
      (≤-trans (≤-reflexive (hp-double m)) (bd2 (hp≤1 m))))

  q≤1 : ∀ m → q m ≤ 1#
  q≤1 m = negExp≤1 (hp m)

  base-at : ∀ m → _
  base-at m = base {q m} {hp m} {expC (lemOf lem₁) (hp m)}
    (negExp-expC-nat (hp m) 1 (bd1 (hp≤1 m))) (1+≤expC (lemOf lem₁) (hp m)) (expC≤quad (lemOf lem₁) (hp≤1 m))
    (q≤1 m) (hp≤1 m)

  ----------------------------------------------------------------------------
  -- bounds `q j ≤ F j ≤ 1`

  F≤1 : ∀ j → F j ≤ 1#
  F≤1 j = ≤-trans (I-mono fairCoin (Fun-G j) (Fun-const 1# ≤-refl) (λ r → negExp≤1 _))
                  (≤-reflexive (I-const fairCoin L-one 1# ≤-refl))

  q≤F : ∀ j → q j ≤ F j
  q≤F j = ≤-trans (≤-reflexive (sym (I-const fairCoin L-one (q j) (q≤1 j))))
    (I-mono fairCoin (Fun-const (q j) (q≤1 j)) (Fun-G j)
       (λ r → negExp-anti (≤-trans (*-mono (hp j) (expansion≤1 r)) (≤-reflexive (*-identityʳ _)))))

  ----------------------------------------------------------------------------
  -- splitting off the first bit

  pt-true : ∀ j x → G j (consR true x) ≈ q (ℕ.suc j) * G (ℕ.suc j) x
  pt-true j x = trans
    (negExp-cong (trans (*-cong refl (expansion-cons true x)) (true-alg (hp j) (expansion x))))
    (negExp-add {hp (ℕ.suc j)} {hp (ℕ.suc j) * expansion x} {1} {1} {2} (bd1 (hp≤1 (ℕ.suc j))) (bd1 (hp·e≤1 (ℕ.suc j) x))
      (≤-trans (+-mono′ (≤-refl {hp (ℕ.suc j)}) (≤-trans (*-mono (hp (ℕ.suc j)) (expansion≤1 x)) (≤-reflexive (*-identityʳ _))))
        (≤-trans (≤-reflexive (hp-double j)) (bd2 (hp≤1 j)))))
    where open OmegaSemiring A using () renaming (+-mono to +-mono′)

  pt-false : ∀ j x → G j (consR false x) ≈ G (ℕ.suc j) x
  pt-false j x = negExp-cong (trans (*-cong refl (trans (expansion-cons false x) (+-identityˡ _))) (false-alg (hp j) (expansion x)))

  F-split : ∀ j → F j ≈ half * (q (ℕ.suc j) * F (ℕ.suc j)) + half * F (ℕ.suc j)
  F-split j = trans (firstBit-fun (Fun-G j)) (+-cong (*-cong refl it) (*-cong refl if))
    where
      Fq = Fun-scale (q (ℕ.suc j)) (q≤1 _) (Fun-G (ℕ.suc j))
      it = trans (I-cong fairCoin (pt-true j) (Fun-pre {f = consR true} (Fun-G j) (measurable-cons true)) Fq)
                 (I-scale fairCoin (q (ℕ.suc j)) (Fun-G (ℕ.suc j)) Fq (λ x → refl))
      if = I-cong fairCoin (pt-false j) (Fun-pre {f = consR false} (Fun-G j) (measurable-cons false)) (Fun-G (ℕ.suc j))

  xs : ℕ → Cut
  xs j = hp j * F j

  xs-rec : ∀ j → xs j ≈ (1# + q (ℕ.suc j)) * xs (ℕ.suc j)
  xs-rec j = trans (*-cong refl (F-split j)) (rec-alg (hp j) (q (ℕ.suc j)) (F (ℕ.suc j)))

  ----------------------------------------------------------------------------
  -- the result

  I-negExp≈F0 : I-negExp ≈ F 0
  I-negExp≈F0 = trans (J-cong fairCoin Meas-negExp-expansion (Meas-G 0) (λ r → negExp-cong (sym (*-identityˡ _))))
    (trans (J-irrel fairCoin (Meas-G 0) (LS (Fun-G 0))) (J-fun fairCoin (Fun-G 0)))

  I-negExp-unit : I-negExp + negExp 1# ≈ 1#
  I-negExp-unit = trans (+-cong (trans I-negExp≈F0 (sym (*-identityˡ _))) refl)
    (norm q xs q-sq q≤1 (λ m → proj₁ (base-at m)) (λ m → proj₂ (base-at m)) xs-rec
       (λ m → *-mono (hp m) (q≤F m)) (λ m → ≤-trans (*-mono (hp m) (F≤1 m)) (≤-reflexive (*-identityʳ _))))
