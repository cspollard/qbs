{-# OPTIONS --safe --without-K #-}

-- The algebra behind the digit code of `[0,∞]` (`Continuous/DigitStream`, `Continuous/DigitCode`), over an abstract
-- ω-semiring with a half.
--   * `mN c m N`, the numerator after N steps of the dyadic subdivision that reads the bits of c: `m ↦ 2m + b`;
--   * `part-mN`: `m + part N c ≈ (mN c m N) · ½ᴺ`, the partial sums of the expansion are the dyadic points;
--   * `part-resp`: `part N` only depends on the first N bits;
--   * `dy-dbl`, `dy-succ`, `dy-mono`: the dyadic points `m · ½ⁿ` under halving, successor and the order.
module QBS.Analysis.DigitAlg where

import Level as L
open import Level using (lift)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core using (Cantor)
open import QBS.Analysis.Clopen using (cons)
open import QBS.Analysis.Omega
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
open import QBS.Analysis.Half using (module Half)

module AlgDigit (A : OmegaSemiring (L.suc L.zero)) (half : OmegaSemiring.Carrier A)
    (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Expansion A half hh using (part; sel)
  open ExpansionCons A half hh using (part-cons)
  open AlgDy A half hh using (two; two-half; dbl; ix; natE-dbl; cons-alg)
  open Half A half hh using (hp)
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  tl : Cantor → Cantor
  tl c n = c (ℕ.suc n)

  -- the numerator after N steps: `m ↦ 2m + b` for the bits b of c
  mN : Cantor → ℕ → ℕ → ℕ
  mN c m ℕ.zero = m
  mN c m (ℕ.suc N) = mN (tl c) (ix (c ℕ.zero) m) N

  part-resp : ∀ {c d : Cantor} → (∀ n → c n ≡ d n) → ∀ N → part N (lift c) ≈ part N (lift d)
  part-resp e ℕ.zero = refl
  part-resp e (ℕ.suc N) = +-cong (part-resp e N) (reflexive (cong (λ b → sel b (half * hp N)) (e N)))

  half-two : ∀ L → half * (two * L) ≈ L
  half-two L = trans (sym (*-assoc half two L)) (trans (*-cong (trans (*-comm half two) two-half) refl) (*-identityˡ L))

  -- the last three steps of `part-mN`: halving moves into the next dyadic scale
  half-nat : ∀ k N → half * (natE k * hp N) ≈ natE k * hp (ℕ.suc N)
  half-nat k N = begin
    half * (natE k * hp N)  ≈⟨ sym (*-assoc half _ _) ⟩
    (half * natE k) * hp N  ≈⟨ *-cong (*-comm _ _) refl ⟩
    (natE k * half) * hp N  ≈⟨ *-assoc _ _ _ ⟩
    natE k * hp (ℕ.suc N) ∎

  -- peeling the first digit: `m + part (N+1) c = (2m + c₀ + part N (tl c)) / 2`
  part-half : ∀ N m (c : Cantor) →
    natE m + part (ℕ.suc N) (lift c) ≈ half * (natE (ix (c ℕ.zero) m) + part N (lift (tl c)))
  part-half N m c = begin
    natE m + part (ℕ.suc N) (lift c)
      ≈⟨ +-cong refl (part-resp {c} {cons b (tl c)} e (ℕ.suc N)) ⟩
    natE m + part (ℕ.suc N) (lift (cons b (tl c)))
      ≈⟨ +-cong refl (part-cons b N (lift (tl c))) ⟩
    natE m + (sel b half + half * w)
      ≈⟨ sym (half-two _) ⟩
    half * (two * (natE m + (sel b half + half * w)))
      ≈⟨ *-cong refl (cons-alg b m {sel b half + half * w} {w} refl) ⟩
    half * (natE (ix b m) + w) ∎
    where
      b = c ℕ.zero
      w = part N (lift (tl c))
      e : ∀ n → c n ≡ cons b (tl c) n
      e ℕ.zero = _≡_.refl
      e (ℕ.suc n) = _≡_.refl

  -- `m + part N c` is the dyadic point `(mN c m N) / 2ᴺ`
  part-mN : ∀ N m (c : Cantor) → natE m + part N (lift c) ≈ natE (mN c m N) * hp N
  part-mN ℕ.zero m c = trans (+-identityʳ _) (sym (trans (*-cong refl (hp0)) (*-identityʳ _)))
    where hp0 : hp 0 ≈ 1#
          hp0 = refl
  part-mN (ℕ.suc N) m c = begin
    natE m + part (ℕ.suc N) (lift c)
      ≈⟨ part-half N m c ⟩
    half * (natE (ix (c ℕ.zero) m) + part N (lift (tl c)))
      ≈⟨ *-cong refl (part-mN N (ix (c ℕ.zero) m) (tl c)) ⟩
    half * (natE (mN (tl c) (ix (c ℕ.zero) m) N) * hp N)
      ≈⟨ half-nat _ N ⟩
    natE (mN c m (ℕ.suc N)) * hp (ℕ.suc N) ∎

  ----------------------------------------------------------------------------
  -- dyadic points

  -- `2m / 2ⁿ⁺¹ = m / 2ⁿ`
  dy-dbl : ∀ m n → natE (dbl m) * hp (ℕ.suc n) ≈ natE m * hp n
  dy-dbl m n = begin
    natE (dbl m) * (half * hp n)       ≈⟨ *-cong (natE-dbl m) refl ⟩
    (two * natE m) * (half * hp n)
      ≈⟨ solve 4 (λ t N h P → (t :* N) :* (h :* P) := (t :* h) :* (N :* P)) refl two (natE m) half (hp n) ⟩
    (two * half) * (natE m * hp n)     ≈⟨ *-cong two-half refl ⟩
    1# * (natE m * hp n)               ≈⟨ *-identityˡ _ ⟩
    natE m * hp n ∎

  -- `(m + 1) / 2ⁿ = m / 2ⁿ + 1 / 2ⁿ`
  dy-succ : ∀ m n → natE (ℕ.suc m) * hp n ≈ natE m * hp n + hp n
  dy-succ m n = trans (distribʳ (hp n) (natE m) 1#) (+-cong refl (*-identityˡ _))

  natE-mono : ∀ {m n} → m ℕ.≤ n → natE m ≤ natE n
  natE-mono ℕ.z≤n = 0-least
  natE-mono (ℕ.s≤s h) = +-mono (natE-mono h) ≤-refl

  dy-mono : ∀ {m m′} n → m ℕ.≤ m′ → natE m * hp n ≤ natE m′ * hp n
  dy-mono {m} {m′} n h = ≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (*-mono (hp n) (natE-mono h)) (≤-reflexive (*-comm _ _)))

  dbl-*2 : ∀ m → dbl m ≡ m ℕ.* 2
  dbl-*2 ℕ.zero = _≡_.refl
  dbl-*2 (ℕ.suc m) = cong (λ t → ℕ.suc (ℕ.suc t)) (dbl-*2 m)

  -- `(a · 2ˡ) / 2ˡ⁺ⁿ = a / 2ⁿ`
  dy-scale : ∀ a l n → natE (a ℕ.* 2 ℕ.^ l) * hp (l ℕ.+ n) ≈ natE a * hp n
  dy-scale a ℕ.zero n = *-cong (reflexive (cong natE (ℕ.*-identityʳ a))) refl
  dy-scale a (ℕ.suc l) n = trans (*-cong (reflexive (cong natE e)) refl) (trans (dy-dbl (a ℕ.* 2 ℕ.^ l) (l ℕ.+ n)) (dy-scale a l n))
    where
      e : a ℕ.* 2 ℕ.^ ℕ.suc l ≡ dbl (a ℕ.* 2 ℕ.^ l)
      e = ≡.trans (cong (a ℕ.*_) (ℕ.*-comm 2 (2 ℕ.^ l))) (≡.trans (≡.sym (ℕ.*-assoc a (2 ℕ.^ l) 2)) (≡.sym (dbl-*2 _)))

  -- comparing dyadic points of different depths
  dy-le : ∀ l n M M′ → M ℕ.* 2 ℕ.^ l ℕ.≤ M′ → natE M * hp n ≤ natE M′ * hp (l ℕ.+ n)
  dy-le l n M M′ h = ≤-trans (≤-reflexive (sym (dy-scale M l n))) (dy-mono (l ℕ.+ n) h)

  dy-ge : ∀ l n M M′ → M′ ℕ.≤ M ℕ.* 2 ℕ.^ l → natE M′ * hp (l ℕ.+ n) ≤ natE M * hp n
  dy-ge l n M M′ h = ≤-trans (dy-mono (l ℕ.+ n) h) (≤-reflexive (dy-scale M l n))
