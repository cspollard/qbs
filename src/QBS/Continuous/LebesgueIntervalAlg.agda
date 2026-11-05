{-# OPTIONS --safe --without-K #-}

-- The mass of an interval under a measure whose dyadic cells have mass ½ⁿ (plan 03, "Uniqueness on the half-line"),
-- the engine of `LebesgueInterval.leb-Iv`.  For a pre-measure p on `WQ`, write `F b = ∫ p χ[0,b)`.
--   * `∫ᴹ-split-iv`: `∫ χ[a,b) = ∫ χ[a,c) + ∫ χ[c,b)` for a ≤ c ≤ b (additivity of the integral over `split-iv`);
--   * `F-dy`: `F (m/2ⁿ) ≈ m/2ⁿ`, from the cells `χ[i/2ⁿ, (i+1)/2ⁿ)`, i < m, by induction on m;
--   * `tgt-ex`: a bounded point lies, for every n, in a dyadic interval [M/2ⁿ, (M+1)/2ⁿ) (`DigitStream`);
--   * `F-eq`: `F b ≈ b` for bounded b: both `F b ≤ b + ½ⁿ` and `b ≤ F b + ½ⁿ` follow by monotonicity from the
--     dyadic points around b, then `Arch.arch`;
--   * `Iv-eq`: `a + ∫ χ[a,b) ≈ b` for a ≤ b with b bounded.
module QBS.Continuous.LebesgueIntervalAlg where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (mk⊑; _⊑_)
open _⊑_ using (ap)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitStream using (module DigitStream)
open import QBS.Continuous.DigitCut using (module DigitCut)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)

module LebesgueIntervalAlg (lem : LEM₀) where
  open Lebesgue lem using (A; J-add; J-cong; J-scale)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; ≤-antisym;
    +-mono; ≤-+ʳ; ≤-refl; 0-least; +-comm; distribˡ; *-mono; *-identityʳ; zeroˡ; zeroʳ) renaming (Carrier to ∣A∣)
  open Bounded A using (nat; Bnd)
  open Arch (lowerRealsArch lem) using (half; arch) renaming (half+half to hh)
  open Half A half hh using (hp; hp-zero; hp-≤)
  open AlgDigit A half hh using (dy-succ; dy-mono; mN)
  open Exp A using (natE)
  open Meas lem using (Meas-⊕; Meas-⊗; Meas-const)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; ψ; mψ; module C)
  open C using (Pre)
  open C.Pre
  open Intervals lem using (Ge; dy; χI; χIv; χIv-out; split-iv)
  open DigitStream lem using (floor-ex; fr; out; fr-inv; fl-tgt; Tgt)
  open DigitCut lem using (below-dec)
  open LebesgueDyadicAlg lem using (no-succ; natE≈nat)
  open QBS
  open Hom

  -- additivity of the integral over a split of an interval
  ∫ᴹ-split-iv : ∀ (p : Pre (XW WQ)) a c b → Ge a c → Ge c b →
    ∫ᴹ {WQ} p (χIv a b) ≈ ∫ᴹ {WQ} p (χIv a c) + ∫ᴹ {WQ} p (χIv c b)
  ∫ᴹ-split-iv p a c b ac cb = trans
    (J-cong (m p) (mψ {WQ} p (χIv a b))
      (Meas-⊕ {ψ {WQ} p (χIv a c)} {ψ {WQ} p (χIv c b)} (mψ {WQ} p (χIv a c)) (mψ {WQ} p (χIv c b))) pt)
    (J-add (m p) {ψ {WQ} p (χIv a c)} {ψ {WQ} p (χIv c b)} (mψ {WQ} p (χIv a c)) (mψ {WQ} p (χIv c b)))
    where
      pt : ∀ r → ψ {WQ} p (χIv a b) r ≈ ψ {WQ} p (χIv a c) r + ψ {WQ} p (χIv c b) r
      pt r = trans (*-cong refl (split-iv a c b (proj₂ (α p ⟨$⟩ r)) ac cb)) (distribˡ _ _ _)

  -- an integral of a test that vanishes pointwise
  ∫ᴹ-zero′ : ∀ (p : Pre (XW WQ)) (f : Hom S WQ WQ) → (∀ x → map f ⟨$⟩ x ≈ 0#) → ∫ᴹ {WQ} p f ≈ 0#
  ∫ᴹ-zero′ p f e = trans
    (J-cong (m p) (mψ {WQ} p f) (Meas-⊗ {λ _ → 0#} {λ _ → 0#} (Meas-const 0#) (Meas-const 0#))
      (λ r → trans (trans (*-cong refl (e _)) (zeroʳ _)) (sym (zeroˡ 0#))))
    (trans (J-scale (m p) 0# {λ _ → 0#} (Meas-const 0#)) (zeroˡ _))

  F : Pre (XW WQ) → ∣A∣ → _
  F p b = ∫ᴹ {WQ} p (χIv 0# b)

  F-mono : ∀ p b c → b ≤ c → F p b ≤ F p c
  F-mono p b c bc = ≤-trans ≤-+ʳ (≤-reflexive (sym (∫ᴹ-split-iv p 0# b c (ap (0-least {b})) (ap bc))))

  F-dy : ∀ p → (∀ n i → ∫ᴹ {WQ} p (χI n i) ≈ hp n) → ∀ n m → F p (dy n m) ≈ dy n m
  F-dy p cell n zero = trans (∫ᴹ-zero′ p (χIv 0# (dy n zero)) pt) (sym (zeroˡ (hp n)))
    where pt = λ x → χIv-out 0# (dy n zero) x (λ (_ , ng) → ng (ap (≤-trans (≤-reflexive (zeroˡ (hp n))) (0-least {x}))))
  F-dy p cell n (suc m) = trans (∫ᴹ-split-iv p 0# (dy n m) (dy n (suc m)) (ap (0-least {dy n m})) (ap (dy-mono n (ℕ.n≤1+n m))))
    (trans (+-cong (F-dy p cell n m) (cell n m)) (sym (dy-succ m n)))

  tgt-ex : ∀ b → Bnd b → ∀ n → Σ ℕ (λ M → Tgt n M b)
  tgt-ex b (k , bk) n = mN (out b (fr zero k′)) k′ n , fr-inv b n zero k′ n (≡.sym (ℕ.+-identityʳ n)) (fl-tgt b k′ gk ng)
    where
      fl = floor-ex b (λ all → no-succ k (≤-trans (mk⊑ (all (suc k))) (≤-trans bk (≤-reflexive (sym (natE≈nat k))))))
      k′ = proj₁ fl
      gk = proj₁ (proj₂ fl)
      ng = proj₂ (proj₂ fl)

  F-le : ∀ p → (∀ n i → ∫ᴹ {WQ} p (χI n i) ≈ hp n) → ∀ b → Bnd b → F p b ≤ b
  F-le p cell b bd = arch (λ n → let M = proj₁ (tgt-ex b bd n); t = proj₂ (tgt-ex b bd n) in
    ≤-trans (F-mono p b (dy n (suc M)) (below-dec M n b (proj₂ t)))
      (≤-trans (≤-reflexive (F-dy p cell n (suc M)))
        (≤-trans (≤-reflexive (dy-succ M n)) (+-mono (mk⊑ (proj₁ t)) ≤-refl))))

  F-ge : ∀ p → (∀ n i → ∫ᴹ {WQ} p (χI n i) ≈ hp n) → ∀ b → Bnd b → b ≤ F p b
  F-ge p cell b bd = arch (λ n → let M = proj₁ (tgt-ex b bd n); t = proj₂ (tgt-ex b bd n) in
    ≤-trans (below-dec M n b (proj₂ t))
      (≤-trans (≤-reflexive (dy-succ M n))
        (≤-trans (+-mono (≤-reflexive (sym (F-dy p cell n M))) ≤-refl)
          (+-mono (F-mono p (dy n M) b (mk⊑ (proj₁ t))) ≤-refl))))

  F-eq : ∀ p → (∀ n i → ∫ᴹ {WQ} p (χI n i) ≈ hp n) → ∀ b → Bnd b → F p b ≈ b
  F-eq p cell b bd = ≤-antisym (F-le p cell b bd) (F-ge p cell b bd)

  Iv-eq : ∀ p → (∀ n i → ∫ᴹ {WQ} p (χI n i) ≈ hp n) → ∀ a b → a ≤ b → Bnd b → a + ∫ᴹ {WQ} p (χIv a b) ≈ b
  Iv-eq p cell a b ab (k , bk) = trans
    (+-cong (sym (F-eq p cell a (k , ≤-trans ab bk))) refl)
    (trans (sym (∫ᴹ-split-iv p 0# a b (ap (0-least {a})) (ap ab))) (F-eq p cell b (k , bk)))
