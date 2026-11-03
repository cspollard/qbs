{-# OPTIONS --safe --without-K #-}

-- Lebesgue measure of the dyadic intervals (plan 03, "Uniqueness on the half-line").
--   * `fair-top`: the all-true point has fair-coin measure 0 (`I (χ Top) ≤ ½ⁿ` for all n, by the first-bit split, since
--     `true :: r` is all-true only when `r` is; then `Arch.arch`);
--   * `cell-in`, `cell-out`: the unit interval shifted by j, `j + expansion r`, lies in the dyadic interval
--     [m/2ⁿ, (m+1)/2ⁿ) with fair-coin probability ½ⁿ when that interval is inside [j, j+1), and 0 otherwise.  Induction
--     on n with the first-bit split (`Continuous/FirstBit`) and `expansion (b ∷ r) = b/2 + expansion r / 2`
--     (`Analysis/ExpansionCons`): an affine bijection maps half-open intervals exactly onto half-open intervals, so the
--     only null set is `fair-top`, at n = 0;
--   * `leb-χI`, `leb-inf`, `leb-fin`: the hypotheses of `UniquenessWQ.uniqWQ` for `lebPre` (via `HalfLine.∫ᴹ-leb`).
module QBS.Continuous.LebesgueDyadic where

open import Level using (lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc; _*_; _^_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Bool.Base using (true; false)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Cells using (Top; borelTop)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.CoinIntegral using (lemOf; module Daniell)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.FirstBitInf using (module FirstBitInf)
open import QBS.Continuous.LebesgueDyadicNat
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)

module LebesgueDyadic (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-fun; J-irrel; J-cong; J-mono; J-add)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; ≤-antisym; +-mono;
    *-mono; ≤-+ʳ; ≤-refl; 0-least; +-identityˡ; +-identityʳ; zeroʳ; +-comm) renaming (Carrier to ∣A∣; _*_ to _·_)
  open Bounded A using (Bnd)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-in; χ-out; χ-≤1; I-≤1; I-const; case)
  open Integration A using (I; I-mono)
  open Measurable A using (Fun; Fun-pre; Fun-const)
  open Meas (lemOf lem₁) using (Meas; Meas-const; Meas-⊕)
  open Series A using (∑ᶠ-single; ∑ᶠ-zero)
  open Daniell lem₁ using (L-one)
  open FirstBit lem₁ using (firstBit-fun)
  open FirstBitInf lem₁ using (firstBit-J; mp)
  open LebesgueDyadicAlg (lemOf lem₁) using (jb; step-pt; base-in; base-lt; base-gt; χI≤1; inf-out)
  open LevelSets (lemOf lem₁) using (LS)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half; arch) renaming (half+half to hh)
  open Half A half hh using (hp)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open Intervals (lemOf lem₁) using (χI; χInf)
  open QBS
  open Hom

  -- the all-true point is null: `I (χ Top) ≤ ½ⁿ` for every n, by the first-bit split
  FT : Fun (χ Top)
  FT = Fun-χ borelTop

  tpt : ∀ r → χ Top (consR true r) ≤ χ Top r
  tpt r = case {P = Top (lower r)} (λ t → ≤-trans (χ-≤1 Top _) (≤-reflexive (sym (χ-in Top r t))))
    (λ nt → ≤-reflexive (trans (χ-out Top (consR true r) (λ t → nt (λ i → t (suc i)))) (sym (χ-out Top r nt))))

  fpt : ∀ r → χ Top (consR false r) ≈ 0#
  fpt r = χ-out Top (consR false r) (λ t → bad (t 0))
    where bad : false ≡.≡ true → ⊥
          bad ()

  I-top-≤ : ∀ n → I fairCoin (χ Top) FT ≤ hp n
  I-top-≤ zero = I-≤1 fairCoin FT
  I-top-≤ (suc n) = ≤-trans (≤-reflexive (firstBit-fun FT)) (≤-trans (+-mono (*-mono half tr) (*-mono half fl))
    (≤-reflexive (trans (+-cong refl (zeroʳ half)) (+-identityʳ _))))
    where
      tr = ≤-trans (I-mono fairCoin (Fun-pre {f = consR true} FT (measurable-cons true)) FT tpt) (I-top-≤ n)
      fl = ≤-trans (I-mono fairCoin (Fun-pre {f = consR false} FT (measurable-cons false)) (Fun-const 0# 0-least)
                     (λ r → ≤-reflexive (fpt r))) (≤-reflexive (I-const fairCoin L-one 0# 0-least))

  fair-top : J fairCoin (χ Top) (LS (Fun-χ borelTop)) ≈ 0#
  fair-top = trans (J-fun fairCoin FT) (≤-antisym
    (arch (λ n → ≤-trans (I-top-≤ n) (≤-reflexive (sym (+-identityˡ _))))) 0-least)

  ----------------------------------------------------------------------------
  -- the integral of a test along the shifted expansion, and constants

  JJ : ℕ → ℕ → ℕ → ∣A∣
  JJ n j m = J fairCoin (λ r → map (χI n m) ⟨$⟩ shiftPt j r) (Meas-hshift j (χI n m))

  J-const : ∀ c (c≤1 : c ≤ 1#) → J fairCoin (λ _ → c) (Meas-const c) ≈ c
  J-const c c≤1 = trans s1 (trans s2 s3)
    where
      s1 : J fairCoin (λ _ → c) (Meas-const c) ≈ J fairCoin (λ _ → c) (LS (Fun-const c c≤1))
      s1 = J-irrel fairCoin (Meas-const c) (LS (Fun-const c c≤1))
      s2 : J fairCoin (λ _ → c) (LS (Fun-const c c≤1)) ≈ I fairCoin (λ _ → c) (Fun-const c c≤1)
      s2 = J-fun fairCoin (Fun-const c c≤1)
      s3 : I fairCoin (λ _ → c) (Fun-const c c≤1) ≈ c
      s3 = I-const fairCoin L-one c c≤1

  -- at level 0: the cell [j, j+1) has mass 1 (all but the null point), and the others mass 0
  base-pw : ∀ j (r : R₁) → 1# ≤ (map (χI 0 j) ⟨$⟩ shiftPt j r) + χ Top r
  base-pw j r = case {P = Top (lower r)}
    (λ t → ≤-trans (≤-reflexive (sym (χ-in Top r t))) (≤-trans (≤-+ʳ {χ Top r} {f}) (≤-reflexive (+-comm _ _))))
    (λ nt → ≤-trans (≤-reflexive (sym (base-in j r nt))) (≤-+ʳ {f} {χ Top r}))
    where f = map (χI 0 j) ⟨$⟩ shiftPt j r

  base-in-J : ∀ j → JJ 0 j j ≈ 1#
  base-in-J j = ≤-antisym up lo
    where
      f : R₁ → ∣A∣
      f r = map (χI 0 j) ⟨$⟩ shiftPt j r
      mf : Meas f
      mf = Meas-hshift j (χI 0 j)
      mχ : Meas (χ Top)
      mχ = LS FT
      up : JJ 0 j j ≤ 1#
      up = ≤-trans (J-mono fairCoin mf (Meas-const 1#) (λ r → χI≤1 0 j (shiftPt j r))) (≤-reflexive (J-const 1# ≤-refl))
      sm : J fairCoin (λ r → f r + χ Top r) (Meas-⊕ {f} {χ Top} mf mχ) ≈ J fairCoin f mf + J fairCoin (χ Top) mχ
      sm = J-add fairCoin {f} {χ Top} mf mχ
      lo : 1# ≤ JJ 0 j j
      lo = ≤-trans (≤-reflexive (sym (J-const 1# ≤-refl)))
        (≤-trans (J-mono fairCoin (Meas-const 1#) (Meas-⊕ {f} {χ Top} mf mχ) (base-pw j))
          (≤-reflexive (trans sm (trans (+-cong refl fair-top) (+-identityʳ _)))))

  base-out-J : ∀ j m → (suc m ≤ℕ j) ⊎ (suc j ≤ℕ m) → JJ 0 j m ≈ 0#
  base-out-J j m h = ≤-antisym (≤-trans (J-mono fairCoin mf (LS FT) pw) (≤-reflexive fair-top)) 0-least
    where
      f : R₁ → ∣A∣
      f r = map (χI 0 m) ⟨$⟩ shiftPt j r
      mf : Meas f
      mf = Meas-hshift j (χI 0 m)
      z : ∀ r → (Top (lower r) → ⊥) → f r ≈ 0#
      z r nt = [ (λ lt → base-lt j m r lt) , (λ gt → base-gt j m r gt nt) ]′ h
      pw : ∀ r → f r ≤ χ Top r
      pw r = case {P = Top (lower r)} (λ t → ≤-trans (χI≤1 0 m _) (≤-reflexive (sym (χ-in Top r t))))
        (λ nt → ≤-trans (≤-reflexive (z r nt)) 0-least)

  -- halving: the first bit sends the cell at level n+1 of j to the cell at level n of 2j (false) and 2j+1 (true)
  step-J : ∀ n j m → JJ (suc n) j m ≈ half · JJ n (jb j true) m + half · JJ n (jb j false) m
  step-J n j m = trans (firstBit-J (Meas-hshift j (χI (suc n) m))) (+-cong (*-cong refl eT) (*-cong refl eF))
    where
      eT : J fairCoin (λ r → map (χI (suc n) m) ⟨$⟩ shiftPt j (consR true r)) (mp true (Meas-hshift j (χI (suc n) m)))
         ≈ JJ n (jb j true) m
      eT = J-cong fairCoin _ (Meas-hshift (jb j true) (χI n m)) (step-pt n m j true)
      eF : J fairCoin (λ r → map (χI (suc n) m) ⟨$⟩ shiftPt j (consR false r)) (mp false (Meas-hshift j (χI (suc n) m)))
         ≈ JJ n (jb j false) m
      eF = J-cong fairCoin _ (Meas-hshift (jb j false) (χI n m)) (step-pt n m j false)

  cell-out′ : ∀ j n m → (m <ℕ j * 2 ^ n) ⊎ (suc j * 2 ^ n ≤ℕ m) → JJ n j m ≈ 0#
  cell-out′ j zero m h = base-out-J j m (out0 j m h)
  cell-out′ j (suc n) m h = trans (step-J n j m) (trans (+-cong (*-cong refl t) (*-cong refl f))
    (trans (+-cong (zeroʳ half) (zeroʳ half)) (+-identityˡ 0#)))
    where
      sp = split-out j (2 ^ n) m h
      t : JJ n (jb j true) m ≈ 0#
      t = cell-out′ (jb j true) n m (proj₂ sp)
      f : JJ n (jb j false) m ≈ 0#
      f = cell-out′ (jb j false) n m (proj₁ sp)

  cell-in′ : ∀ j n m → j * 2 ^ n ≤ℕ m → m <ℕ suc j * 2 ^ n → JJ n j m ≈ hp n
  cell-in′ j zero m lo hi = ≡.subst (λ k → JJ 0 j k ≈ hp 0) (≡.sym (cell0 j m lo hi)) (base-in-J j)
  cell-in′ j (suc n) m lo hi = go (split-in j (2 ^ n) m lo hi)
    where
      go : (((2 * j) * 2 ^ n ≤ℕ m) × (m <ℕ suc (2 * j) * 2 ^ n)) ⊎
           ((suc (2 * j) * 2 ^ n ≤ℕ m) × (m <ℕ suc (suc (2 * j)) * 2 ^ n)) → JJ (suc n) j m ≈ hp (suc n)
      go (inj₁ (lo0 , hi0)) = trans (step-J n j m) (trans (+-cong (*-cong refl (cell-out′ _ n m (inj₁ hi0)))
        (*-cong refl (cell-in′ _ n m lo0 hi0))) (trans (+-cong (zeroʳ half) refl) (+-identityˡ _)))
      go (inj₂ (lo1 , hi1)) = trans (step-J n j m) (trans (+-cong (*-cong refl (cell-in′ _ n m lo1 hi1))
        (*-cong refl (cell-out′ _ n m (inj₂ lo1)))) (trans (+-cong refl (zeroʳ half)) (+-identityʳ _)))

  -- the law of the shifted expansion on dyadic intervals
  cell-in : ∀ j n m → j * 2 ^ n ≤ℕ m → m <ℕ suc j * 2 ^ n →
    J fairCoin (λ r → map (χI n m) ⟨$⟩ shiftPt j r) (Meas-hshift j (χI n m)) ≈ hp n
  cell-in = cell-in′

  cell-out : ∀ j n m → (m <ℕ j * 2 ^ n) ⊎ (suc j * 2 ^ n ≤ℕ m) →
    J fairCoin (λ r → map (χI n m) ⟨$⟩ shiftPt j r) (Meas-hshift j (χI n m)) ≈ 0#
  cell-out = cell-out′

  ----------------------------------------------------------------------------
  -- Lebesgue measure: the hypotheses of `UniquenessWQ.uniqWQ`

  leb-χI : ∀ n m → ∫ᴹ {WQ} lebPre (χI n m) ≈ hp n
  leb-χI n m = trans (∫ᴹ-leb (χI n m)) (trans s1 (cell-in k n m lo hi))
    where
      w = cell-div n m
      k = proj₁ w
      lo = proj₁ (proj₂ w)
      hi = proj₂ (proj₂ w)
      s1 = ∑ᶠ-single k (λ j ne → cell-out j n m (cell-other k j (2 ^ n) m lo hi ne))

  leb-inf : ∫ᴹ {WQ} lebPre χInf ≈ 0#
  leb-inf = trans (∫ᴹ-leb χInf) (∑ᶠ-zero z)
    where
      z : ∀ j → J fairCoin (λ r → map χInf ⟨$⟩ shiftPt j r) (Meas-hshift j χInf) ≈ 0#
      z j = trans (J-cong fairCoin (Meas-hshift j χInf) (Meas-const 0#) (inf-out j)) (J-const 0# 0-least)

  leb-fin : ∀ k → Bnd (∫ᴹ {WQ} lebPre (χI 0 k))
  leb-fin k = 1 , ≤-reflexive (trans (leb-χI 0 k) (sym (+-identityʳ 1#)))
