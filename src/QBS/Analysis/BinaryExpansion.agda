{-# OPTIONS --safe --without-K #-}

-- The binary expansion map R → [0,1], r ↦ Σₙ rₙ 2^{-(n+1)}, is measurable (a `Fun`): it is the
-- supremum of the partial sums, each a finite sum of weighted bit indicators.  Pushing the fair
-- coin along it is the uniform measure on [0,1].
module QBS.Analysis.BinaryExpansion where

import Level as L
open import Level using (lift; lower)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Series using (module Series)

module Expansion (A : OmegaSemiring (L.suc L.zero)) (half : OmegaSemiring.Carrier A)
    (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Series A
  open SetoidReasoning setoid
  private R = R₁

  -- 2^{-n} and 2^{-(n+1)}
  hpow : ℕ → ∣A∣
  hpow ℕ.zero = 1#
  hpow (ℕ.suc n) = half * hpow n

  sel : Bool → ∣A∣ → ∣A∣
  sel true w = w
  sel false w = 0#

  bitW : ℕ → R → ∣A∣
  bitW n r = sel (lower r n) (half * hpow n)

  -- Σ_{n<N} 2^{-(n+1)} + 2^{-N} = 1
  geom : ∀ N → psum (λ n → half * hpow n) N + hpow N ≈ 1#
  geom ℕ.zero = +-identityˡ 1#
  geom (ℕ.suc N) = begin
    (psum (λ n → half * hpow n) N + half * hpow N) + half * hpow N
      ≈⟨ +-assoc _ _ _ ⟩
    psum (λ n → half * hpow n) N + (half * hpow N + half * hpow N)
      ≈⟨ +-cong refl (sym (distribʳ (hpow N) half half)) ⟩
    psum (λ n → half * hpow n) N + (half + half) * hpow N
      ≈⟨ +-cong refl (trans (*-cong hh refl) (*-identityˡ _)) ⟩
    psum (λ n → half * hpow n) N + hpow N
      ≈⟨ geom N ⟩
    1# ∎

  psum-≤1 : ∀ N → psum (λ n → half * hpow n) N ≤ 1#
  psum-≤1 N = ≤-trans ≤-+ʳ (≤-reflexive (geom N))

  bitW-≤ : ∀ n r → bitW n r ≤ half * hpow n
  bitW-≤ n r with lower r n
  ... | true = ≤-refl
  ... | false = 0-least

  w≤1 : ∀ n → half * hpow n ≤ 1#
  w≤1 n = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm _ _))) (psum-≤1 (ℕ.suc n))

  -- the partial sums of the expansion
  part : ℕ → R → ∣A∣
  part ℕ.zero r = 0#
  part (ℕ.suc N) r = part N r + bitW N r

  part-≤ : ∀ N r → part N r ≤ psum (λ n → half * hpow n) N
  part-≤ ℕ.zero r = ≤-refl
  part-≤ (ℕ.suc N) r = +-mono (part-≤ N r) (bitW-≤ N r)

  part-≤1 : ∀ N r → part N r ≤ 1#
  part-≤1 N r = ≤-trans (part-≤ N r) (psum-≤1 N)

  part-inc : ∀ r → Increasing (λ N → part N r)
  part-inc r N = ≤-+ʳ

  -- the bit indicator is measurable
  Fun-bitW : ∀ n → Fun (bitW n)
  Fun-bitW n = ind {U = λ x → x n ≡.≡ true} (half * hpow n) (w≤1 n) (gen n true) on off (λ r → ≤-trans (bitW-≤ n r) (w≤1 n))
    where
      on : ∀ r → lower r n ≡.≡ true → bitW n r ≈ half * hpow n
      on r p = reflexive (≡.cong (λ b → sel b (half * hpow n)) p)
      off : ∀ r → (lower r n ≡.≡ true → ⊥) → bitW n r ≈ 0#
      off r q with lower r n in e
      ... | true = ⊥-elim (q ≡.refl)
      ... | false = refl

  Fun-part : ∀ N → Fun (part N)
  Fun-part ℕ.zero = Fun-const 0# 0-least
  Fun-part (ℕ.suc N) = sumF (Fun-part N) (Fun-bitW N) (λ r → refl) (part-≤1 (ℕ.suc N))

  -- the binary expansion of r
  expansion : R → ∣A∣
  expansion r = ⨆ (λ N → part N r) (part-inc r)

  expansion≤1 : ∀ r → expansion r ≤ 1#
  expansion≤1 r = ⨆-lub _ (part-inc r) (λ N → part-≤1 N r)

  Fun-expansion : Fun expansion
  Fun-expansion = supF part Fun-part part-inc (λ r → refl)
