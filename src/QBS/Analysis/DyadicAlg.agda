{-# OPTIONS --safe --without-K #-}

-- The algebra behind dyadic scaling of Lebesgue measure (`Continuous/HalfLineScale`), over an abstract ω-semiring with a half.
--   * `⨆-mix`: the supremum of ½aₖ + ½bₖ is ½ ⨆a + ½ ⨆b;
--   * `dbl n = 2n`, with `natE (dbl n) ≈ 2 · natE n`, and the two halves `ix false n = 2n`, `ix true n = 2n + 1`;
--   * `cons-alg`: if `e ≈ [b]·½ + ½w` then `2 (n + e) ≈ (2n + b) + w` (the effect of doubling on `n + expansion (b :: r)`);
--   * `∑ᶠ-dbl`: reindexing a series over ℕ × Bool ≅ ℕ, `∑ᶠ a ≈ ∑ᶠ n. (a (2n) + a (2n+1))`;
--   * `tw k = 2ᵏ` with `tw k · ½ᵏ ≈ 1`.
module QBS.Analysis.DyadicAlg where

open import Level using (suc; zero)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.Half using (module Half)

module AlgDy (A : OmegaSemiring (suc zero)) (half : OmegaSemiring.Carrier A)
    (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Series A
  open Expansion A half hh using (sel)
  open Half A half hh using (hp)
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  two : ∣A∣
  two = 1# + 1#

  two-half : two * half ≈ 1#
  two-half = trans (distribʳ half 1# 1#) (trans (+-cong (*-identityˡ half) (*-identityˡ half)) hh)

  ----------------------------------------------------------------------------
  -- suprema of mixtures

  ⨆-mix : ∀ {s a b} (is : Increasing s) (ia : Increasing a) (ib : Increasing b) →
    (∀ k → s k ≈ half * a k + half * b k) → ⨆ s is ≈ half * ⨆ a ia + half * ⨆ b ib
  ⨆-mix {s} {a} {b} is ia ib e = begin
    ⨆ s is                                        ≈⟨ ⨆-cong is incS e ⟩
    ⨆ (λ k → half * a k + half * b k) incS        ≈⟨ sym (⨆-+-diag incA incB incS) ⟩
    ⨆ (λ k → half * a k) incA + ⨆ (λ k → half * b k) incB
      ≈⟨ +-cong (sym (*-⨆ half a ia incA)) (sym (*-⨆ half b ib incB)) ⟩
    half * ⨆ a ia + half * ⨆ b ib                 ∎
    where
      incA : Increasing (λ k → half * a k)
      incA k = *-mono half (ia k)
      incB : Increasing (λ k → half * b k)
      incB k = *-mono half (ib k)
      incS : Increasing (λ k → half * a k + half * b k)
      incS k = +-mono (incA k) (incB k)

  mix-scale : ∀ p x y → p * (half * x + half * y) ≈ half * (p * x) + half * (p * y)
  mix-scale p x y = solve 4 (λ p h x y → p :* (h :* x :+ h :* y) := h :* (p :* x) :+ h :* (p :* y))
    refl p half x y

  ----------------------------------------------------------------------------
  -- doubling of indices

  dbl : ℕ → ℕ
  dbl ℕ.zero = ℕ.zero
  dbl (ℕ.suc n) = ℕ.suc (ℕ.suc (dbl n))

  ix : Bool → ℕ → ℕ
  ix false n = dbl n
  ix true n = ℕ.suc (dbl n)

  natE-dbl : ∀ n → natE (dbl n) ≈ two * natE n
  natE-dbl ℕ.zero = sym (zeroʳ two)
  natE-dbl (ℕ.suc n) = begin
    (natE (dbl n) + 1#) + 1#     ≈⟨ +-cong (+-cong (natE-dbl n) refl) refl ⟩
    (two * natE n + 1#) + 1#     ≈⟨ solve 1 (λ x → ((con 1 :+ con 1) :* x :+ con 1) :+ con 1 := (con 1 :+ con 1) :* (x :+ con 1))
                                      refl (natE n) ⟩
    two * (natE n + 1#)          ∎

  -- 2(n + x) = 2n + 2x
  dbl-step : ∀ n x → two * (natE n + x) ≈ natE (dbl n) + two * x
  dbl-step n x = trans (solve 2 (λ a y → (con 1 :+ con 1) :* (a :+ y) := (con 1 :+ con 1) :* a :+ (con 1 :+ con 1) :* y)
    refl (natE n) x) (+-cong (sym (natE-dbl n)) refl)

  -- 2(½w) = w and 2(½ + ½w) = 1 + w
  two-false : ∀ w → two * (0# + half * w) ≈ w
  two-false w = trans (*-cong refl (+-identityˡ _)) (trans (sym (*-assoc two half w))
    (trans (*-cong two-half refl) (*-identityˡ w)))

  two-true : ∀ w → two * (half + half * w) ≈ 1# + w
  two-true w = trans (solve 3 (λ t h y → t :* (h :+ h :* y) := t :* h :+ t :* h :* y) refl two half w)
    (+-cong two-half (trans (*-cong two-half refl) (*-identityˡ w)))

  -- doubling `n + e` for `e = [b]·½ + ½w`
  cons-alg : ∀ b n {e w} → e ≈ sel b half + half * w → two * (natE n + e) ≈ natE (ix b n) + w
  cons-alg true n {e} {w} p = trans (dbl-step n e) (trans (+-cong refl (trans (*-cong refl p) (two-true w)))
    (sym (+-assoc _ _ _)))
  cons-alg false n {e} {w} p = trans (dbl-step n e) (+-cong refl (trans (*-cong refl p) (two-false w)))

  ----------------------------------------------------------------------------
  -- reindexing a series over ℕ × Bool

  n≤dbl : ∀ n → n ℕ.≤ dbl n
  n≤dbl ℕ.zero = ℕ.z≤n
  n≤dbl (ℕ.suc n) = ℕ.s≤s (ℕ.m≤n⇒m≤1+n (n≤dbl n))

  psum-dbl : ∀ a N → psum a (dbl N) ≈ psum (λ n → a (dbl n) + a (ℕ.suc (dbl n))) N
  psum-dbl a ℕ.zero = refl
  psum-dbl a (ℕ.suc N) = begin
    (psum a (dbl N) + a (dbl N)) + a (ℕ.suc (dbl N))
      ≈⟨ +-assoc _ _ _ ⟩
    psum a (dbl N) + (a (dbl N) + a (ℕ.suc (dbl N)))
      ≈⟨ +-cong (psum-dbl a N) refl ⟩
    psum (λ n → a (dbl n) + a (ℕ.suc (dbl n))) N + (a (dbl N) + a (ℕ.suc (dbl N))) ∎

  ∑ᶠ-dbl : ∀ a → ∑ᶠ a ≈ ∑ᶠ (λ n → a (dbl n) + a (ℕ.suc (dbl n)))
  ∑ᶠ-dbl a = ≤-antisym
    (∑ᶠ-lub (λ N → ≤-trans (psum-index-mono a (n≤dbl N))
      (≤-trans (≤-reflexive (psum-dbl a N)) (psum≤∑ᶠ _ N))))
    (∑ᶠ-lub (λ N → ≤-trans (≤-reflexive (sym (psum-dbl a N))) (psum≤∑ᶠ a (dbl N))))

  ----------------------------------------------------------------------------
  -- powers of two

  tw : ℕ → ∣A∣
  tw ℕ.zero = 1#
  tw (ℕ.suc k) = two * tw k

  -- ½x = y gives x = 2y
  unhalf : ∀ x y → half * x ≈ y → x ≈ two * y
  unhalf x y e = begin
    x                 ≈⟨ sym (*-identityˡ x) ⟩
    1# * x            ≈⟨ *-cong (sym two-half) refl ⟩
    (two * half) * x  ≈⟨ *-assoc two half x ⟩
    two * (half * x)  ≈⟨ *-cong refl e ⟩
    two * y           ∎

  -- (2t)·x = t·(2x)
  mulswap : ∀ t x → (two * t) * x ≈ t * (two * x)
  mulswap t x = solve 2 (λ t x → ((con 1 :+ con 1) :* t) :* x := t :* ((con 1 :+ con 1) :* x)) refl t x

  tw-hp : ∀ k → tw k * hp k ≈ 1#
  tw-hp ℕ.zero = *-identityˡ 1#
  tw-hp (ℕ.suc k) = begin
    (two * tw k) * (half * hp k)  ≈⟨ swap4 two (tw k) half (hp k) ⟩
    (two * half) * (tw k * hp k)  ≈⟨ *-cong two-half (tw-hp k) ⟩
    1# * 1#                       ≈⟨ *-identityˡ 1# ⟩
    1#                            ∎
    where
      swap4 : ∀ t x h y → (t * x) * (h * y) ≈ (t * h) * (x * y)
      swap4 = solve 4 (λ t x h y → (t :* x) :* (h :* y) := (t :* h) :* (x :* y)) refl
