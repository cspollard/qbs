{-# OPTIONS --safe --without-K #-}

-- ∞ times a nonzero value is ∞ in [0, ∞] (plan 05, item 55b; helper for `SignedMul`).
--   * `ex-pos`: a cut that is not 0 has a positive member (excluded middle on the rationals);
--   * `top-pos`: infC ⊗ y ≋ infC when y ≉ 0.
-- Route: take a positive s ∈ y; for a rational q the Archimedean property gives q ≤ k s, and r = k + 1 > 0 has
-- q ≤ r s, so q lies in infC ⊗ y.
module QBS.Continuous.TopMulPos where

open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base using (suc)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Classical using (LEM₀)
open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals using (Cut; module Cut; _⊑_; mk⊑; _≋_; zeroC; infC; _⊗_; 0-least)

open Cut using (mem; open′)
open _⊑_ using (ap)

-- a nonzero cut has a positive member
ex-pos : LEM₀ → ∀ y → (y ≋ zeroC → ⊥) → Σ ℚᵘ (λ s → 0ℚᵘ <ᵘ s × mem y s)
ex-pos lem y nz with lem (Σ ℚᵘ (λ s → mem y s × 0ℚᵘ ≤ᵘ s))
... | inj₁ (s , ms , 0≤s) with open′ y ms
...   | s′ , s<s′ , ms′ = s′ , ≤-<-trans 0≤s s<s′ , ms′
ex-pos lem y nz | inj₂ no = ⊥-elim (nz (mk⊑ fwd , 0-least))
  where
    fwd : ∀ q → mem y q → q <ᵘ 0ℚᵘ
    fwd q mq with neg-or-nonneg q
    ... | inj₁ q<0 = q<0
    ... | inj₂ 0≤q = ⊥-elim (no (q , mq , 0≤q))

top-pos : LEM₀ → ∀ y → (y ≋ zeroC → ⊥) → infC ⊗ y ≋ infC
top-pos lem y nz = mk⊑ (λ _ _ → tt) , mk⊑ (λ q _ → body q)
  where
    open import Data.Product.Base using (proj₁; proj₂)
    s = proj₁ (ex-pos lem y nz)
    0<s = proj₁ (proj₂ (ex-pos lem y nz))
    ms = proj₂ (proj₂ (ex-pos lem y nz))
    body : ∀ q → mem (infC ⊗ y) q
    body q with arch q 0<s
    ... | k , qk = inj₂ (nat (suc k) , s ,
      ≤-<-trans (nat-nonneg k) (≃-<ʳ (≃-sym (nat-suc k)) (lt-add 0<1)) , 0<s , tt , ms ,
      ≤-trans qk (≤-trans (≤-trans (≤-≃ (≃-sym (+-identityʳ _))) (+-mono-≤ (≤-refl {_}) (<-≤ 0<s)))
        (≤-≃ (≃-sym (nat-suc* k s)))))
