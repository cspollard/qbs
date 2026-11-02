{-# OPTIONS --safe --without-K #-}

-- The Beta integral for integer parameters under the uniform distribution:
--   B(k,m) = ∫ uᵏ (1−u)ᵐ du,   (k+m+1)! · B(k,m) = k! · m!   (`beta-closed`, multiplied out, no division),
-- and the conjugacy step (k+m+2) · B(k+1,m) = (k+1) · B(k,m) (`beta-conj`: the posterior mean (k+1)/(k+m+2) after
-- k heads and m tails under a uniform prior).
--
-- Here 1−u is the complement `v` of the binary expansion `u` (`Fun.complF`), so that u + v = 1 pointwise and
--   uᵏ vᵐ = uᵏ⁺¹ vᵐ + uᵏ vᵐ⁺¹,   i.e.   B(k,m) = B(k+1,m) + B(k,m+1)    (`beta-add`);
-- the base case B(k,0) is the k-th moment (`Continuous/UniformMomentN`).  The algebra `AlgB` is over an abstract
-- Archimedean ω-semiring; the two cancellations (of bounded terms) are `BoundedCancel.cancel-bnd`.
module QBS.Continuous.BetaIntegral where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.UniformMomentN as UMN using (module UniformMomentN)
open import QBS.Classical using (LEM₁)

module AlgB (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open UMN.AlgN A R using (#)
  open Bounded A using (Bnd; finite)
  open BoundedCancel A half hh using (cancel-bnd)
  open SetoidReasoning setoid

  -- factorials, in the semiring
  fact : ℕ → ∣A∣
  fact zero = 1#
  fact (suc n) = # (suc n) * fact n

  #-+ : ∀ a b → # (a ℕ.+ b) ≈ # a + # b
  #-+ zero b = sym (+-identityˡ _)
  #-+ (suc a) b = trans (+-cong refl (#-+ a b)) (sym (+-assoc 1# (# a) (# b)))

  -- (k+1) + (m+1) = (k+m+1) + 1
  nn : ∀ k m → # (suc (suc (k ℕ.+ m))) ≈ # (suc k) + # (suc m)
  nn k m = ≡.subst (λ x → # x ≈ # (suc k) + # (suc m)) (≡.cong suc (ℕ.+-suc k m)) (#-+ (suc k) (suc m))

  -- boundedness
  bnd# : ∀ n → Bnd (# n)
  bnd# zero = SubSemiring.Is-0 finite
  bnd# (suc n) = SubSemiring.Is-+ finite (SubSemiring.Is-1 finite) (bnd# n)

  bnd-fact : ∀ n → Bnd (fact n)
  bnd-fact zero = SubSemiring.Is-1 finite
  bnd-fact (suc n) = SubSemiring.Is-* finite (bnd# (suc n)) (bnd-fact n)

  bnd≤1 : ∀ {x} → x ≤ 1# → Bnd x
  bnd≤1 le = 1 , ≤-trans le (≤-reflexive (sym (+-identityʳ 1#)))

  -- u + v = 1 splits  P Q = (u P) Q + P (v Q)
  split : ∀ u v P Q → u + v ≈ 1# → P * Q ≈ (u * P) * Q + P * (v * Q)
  split u v P Q e = trans (sym (trans (*-cong e refl) (*-identityˡ _)))
    (solve 4 (λ u′ v′ P′ Q′ → (u′ :+ v′) :* (P′ :* Q′) := (u′ :* P′) :* Q′ :+ P′ :* (v′ :* Q′)) refl u v P Q)

  -- subtract a common bounded term: n d = q e, e = d + a, n = q + μ give μ d = q a
  cancel-step : ∀ {n q μ d e a} → n ≈ q + μ → e ≈ d + a → n * d ≈ q * e → Bnd (q * d) → μ * d ≈ q * a
  cancel-step {n} {q} {μ} {d} {e} {a} en ee i bq = cancel-bnd bq (begin
    q * d + μ * d    ≈⟨ sym (trans (*-cong en refl) (distribʳ d q μ)) ⟩
    n * d            ≈⟨ i ⟩
    q * e            ≈⟨ trans (*-cong refl ee) (distribˡ q d a) ⟩
    q * d + q * a    ∎)

  -- the induction step of the closed form: n = p + μ, ih0 : F_N B₀ = F_k F_m, ih1 : n F_N B₁ = p F_k F_m, B₀ = B₁ + B₂
  step-eq : ∀ {n p μ fk fm fN b0 b1 b2} → n ≈ p + μ → b0 ≈ b1 + b2 → fN * b0 ≈ fk * fm →
    (n * fN) * b1 ≈ (p * fk) * fm → Bnd (p * (fk * fm)) → (n * fN) * b2 ≈ μ * (fk * fm)
  step-eq {n} {p} {μ} {fk} {fm} {fN} {b0} {b1} {b2} en ad i0 i1 bp = sym (cancel-bnd bp (begin
    p * (fk * fm) + μ * (fk * fm)    ≈⟨ sym (trans (*-cong en refl) (distribʳ (fk * fm) p μ)) ⟩
    n * (fk * fm)                    ≈⟨ *-cong refl (sym i0) ⟩
    n * (fN * b0)                    ≈⟨ *-cong refl (trans (*-cong refl ad) (distribˡ fN b1 b2)) ⟩
    n * (fN * b1 + fN * b2)          ≈⟨ distribˡ n _ _ ⟩
    n * (fN * b1) + n * (fN * b2)    ≈⟨ +-cong (sym (*-assoc n fN b1)) (sym (*-assoc n fN b2)) ⟩
    (n * fN) * b1 + (n * fN) * b2    ≈⟨ +-cong (trans i1 (*-assoc p fk fm)) refl ⟩
    p * (fk * fm) + (n * fN) * b2    ∎))

  ----------------------------------------------------------------------------
  -- the closed form and the conjugacy step

  module Closed (B : ℕ → ℕ → ∣A∣) (B≤1 : ∀ k m → B k m ≤ 1#)
    (add : ∀ k m → B k m ≈ B (suc k) m + B k (suc m)) (base : ∀ k → # (suc k) * B k 0 ≈ 1#) where

    -- (k+m+1)! B(k,m) = k! m!
    closed : ∀ m k → fact (suc (k ℕ.+ m)) * B k m ≈ fact k * fact m
    closed zero k rewrite ℕ.+-identityʳ k = trans
      (solve 3 (λ p f b → (p :* f) :* b := f :* (p :* b)) refl (# (suc k)) (fact k) (B k 0)) (*-cong refl (base k))
    closed (suc m) k rewrite ℕ.+-suc k m = trans (step-eq (nn k m) (add k m) (closed m k) (closed m (suc k)) bp)
      (solve 3 (λ μ f g → μ :* (f :* g) := f :* (μ :* g)) refl _ _ _)
      where bp = SubSemiring.Is-* finite (bnd# (suc k)) (SubSemiring.Is-* finite (bnd-fact k) (bnd-fact m))

    -- (k+m+2) B(k+1,m) = (k+1) B(k,m)
    conj : ∀ m k → # (suc (suc (k ℕ.+ m))) * B (suc k) m ≈ # (suc k) * B k m
    conj zero k rewrite ℕ.+-identityʳ k = trans (base (suc k)) (sym (base k))
    conj (suc m) k rewrite ℕ.+-suc k m = begin
      # (suc (suc (suc (k ℕ.+ m)))) * B (suc k) (suc m)  ≈⟨ *-cong (nn (suc k) m) refl ⟩
      (# (suc (suc k)) + # (suc m)) * B (suc k) (suc m)  ≈⟨ distribʳ _ _ _ ⟩
      # (suc (suc k)) * B (suc k) (suc m) + # (suc m) * B (suc k) (suc m)  ≈⟨ +-cong (sym s2) refl ⟩
      # (suc m) * B (suc (suc k)) m + # (suc m) * B (suc k) (suc m)  ≈⟨ sym (distribˡ _ _ _) ⟩
      # (suc m) * (B (suc (suc k)) m + B (suc k) (suc m))  ≈⟨ *-cong refl (sym (add (suc k) m)) ⟩
      # (suc m) * B (suc k) m  ≈⟨ s1 ⟩
      # (suc k) * B k (suc m)  ∎
      where
      s1 = cancel-step (nn k m) (add k m) (conj m k) (SubSemiring.Is-* finite (bnd# (suc k)) (bnd≤1 (B≤1 (suc k) m)))
      s2 = cancel-step (nn (suc k) m) (add (suc k) m) (conj m (suc k))
        (SubSemiring.Is-* finite (bnd# (suc (suc k))) (bnd≤1 (B≤1 (suc (suc k)) m)))


-- the measure side: `B k m = ∫ uᵏ vᵐ` with `u` the binary expansion and `v = 1 − u`
module BetaIntegral (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  open UMN.UniformMomentN lem₁ using (A; R; pw; pw≤1; Meas-pw; M; Fpow; I-pow; moment-N)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open Integration A
  open Meas (lemOf lem₁)
  open Expansion A half hh
  open FairCoin lem₁ using (fairCoin)
  open Measurable A using (Fun; Fun-const; complF; Fun-≤1)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open Indicators A (lemOf lem₁) using (I-const)
  open AlgB A R using (fact; split)
  open UMN.AlgN A R using (#)

  -- v = 1 − u, by the complement of the binary expansion
  v : R₁ → ∣A∣
  v r = proj₁ (complement (expansion≤1 r))

  uv : ∀ r → expansion r + v r ≈ 1#
  uv r = proj₂ (complement (expansion≤1 r))

  Fv : Fun v
  Fv = complF Fun-expansion (λ r → trans (+-comm _ _) (uv r))

  -- the functions uᵏ vᵐ
  bf : ℕ → ℕ → R₁ → ∣A∣
  bf k m r = pw (expansion r) k * pw (v r) m

  bf≤1 : ∀ k m r → bf k m r ≤ 1#
  bf≤1 k m r = ≤-trans (*-mono _ (pw≤1 (Fun-≤1 Fv r) m))
    (≤-trans (≤-reflexive (*-identityʳ _)) (pw≤1 (expansion≤1 r) k))

  Fbf : ∀ k m → Fun (bf k m)
  Fbf k m = Meas→Fun (bf≤1 k m) (Meas-⊗ {λ r → pw (expansion r) k} {λ r → pw (v r) m}
    (Meas-pw (LS Fun-expansion) k) (Meas-pw (LS Fv) m))

  -- the Beta integral B(k,m) = ∫ uᵏ (1−u)ᵐ
  Bt : ℕ → ℕ → ∣A∣
  Bt k m = I fairCoin (bf k m) (Fbf k m)

  Bt≤1 : ∀ k m → Bt k m ≤ 1#
  Bt≤1 k m = ≤-trans (I-mono fairCoin (Fbf k m) (Fun-const 1# ≤-refl) (bf≤1 k m))
    (≤-reflexive (I-const fairCoin L-one 1# ≤-refl))

  -- B(k,m) = B(k+1,m) + B(k,m+1)
  Bt-add : ∀ k m → Bt k m ≈ Bt (suc k) m + Bt k (suc m)
  Bt-add k m = I-add fairCoin (Fbf k m) (Fbf (suc k) m) (Fbf k (suc m)) (λ r → split _ _ _ _ (uv r))

  -- B(k,0) = ∫ uᵏ
  Bt-base : ∀ k → # (suc k) * Bt k 0 ≈ 1#
  Bt-base k = trans (*-cong refl (trans (I-cong fairCoin (λ r → *-identityʳ _) (Fbf k 0) (Fpow k)) (I-pow k)))
    (moment-N k)

  open AlgB.Closed A R Bt Bt≤1 Bt-add Bt-base using () renaming (closed to beta-closed; conj to beta-conj)
