{-# OPTIONS --safe --without-K #-}

-- Natural-number arithmetic for the dyadic cells of `LebesgueDyadic`: the cell `[j·2ⁿ, (j+1)·2ⁿ)` of indices `m`, its two
-- halves (the cells `2j` and `2j+1` at level n, for `p = 2ⁿ`), the level-0 cell, and the unique `k = m / 2ⁿ` whose cell
-- contains `m`.
module QBS.Continuous.LebesgueDyadicNat where

open import Data.Nat.Base using (ℕ; suc; NonZero; _+_; _*_; _^_; _≤_; _<_)
open import Data.Nat.Properties
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Nat.DivMod using (_/_; m≡m%n+[m/n]*n; m%n<n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

-- level 0: the cell [j, j+1)
cell0 : ∀ j m → j * 2 ^ 0 ≤ m → m < suc j * 2 ^ 0 → m ≡ j
cell0 j m lo hi = ≤-antisym (≡.subst (m ≤_) (*-identityʳ j) (≤-pred hi)) (≡.subst (_≤ m) (*-identityʳ j) lo)

out0 : ∀ j m → (m < j * 2 ^ 0) ⊎ (suc j * 2 ^ 0 ≤ m) → (suc m ≤ j) ⊎ (suc j ≤ m)
out0 j m (inj₁ h) = inj₁ (≡.subst (suc m ≤_) (*-identityʳ j) h)
out0 j m (inj₂ h) = inj₂ (≡.subst (_≤ m) (*-identityʳ (suc j)) h)

-- halving the cell: j·2p = (2j)·p, (j+1)·2p = (2j+2)·p
eq1 : ∀ j p → j * (2 * p) ≡ (2 * j) * p
eq1 = solve 2 (λ j p → j :* (con 2 :* p) := (con 2 :* j) :* p) ≡.refl

eq2 : ∀ j p → suc j * (2 * p) ≡ suc (suc (2 * j)) * p
eq2 = solve 2 (λ j p → (con 1 :+ j) :* (con 2 :* p) := (con 2 :+ con 2 :* j) :* p) ≡.refl

split-in : ∀ j p m → j * (2 * p) ≤ m → m < suc j * (2 * p) →
  (((2 * j) * p ≤ m) × (m < suc (2 * j) * p)) ⊎ ((suc (2 * j) * p ≤ m) × (m < suc (suc (2 * j)) * p))
split-in j p m lo hi with <-cmp m (suc (2 * j) * p)
... | tri< a _ _ = inj₁ (≡.subst (_≤ m) (eq1 j p) lo , a)
... | tri≈ _ e _ = inj₂ (≤-reflexive (≡.sym e) , ≡.subst (m <_) (eq2 j p) hi)
... | tri> _ _ c = inj₂ (<⇒≤ c , ≡.subst (m <_) (eq2 j p) hi)

split-out : ∀ j p m → (m < j * (2 * p)) ⊎ (suc j * (2 * p) ≤ m) →
  ((m < (2 * j) * p) ⊎ (suc (2 * j) * p ≤ m)) × ((m < suc (2 * j) * p) ⊎ (suc (suc (2 * j)) * p ≤ m))
split-out j p m (inj₁ h) = inj₁ h′ , inj₁ (<-≤-trans h′ (m≤n+m ((2 * j) * p) p))
  where h′ = ≡.subst (m <_) (eq1 j p) h
split-out j p m (inj₂ h) = inj₂ (≤-trans (+-monoʳ-≤ p (m≤n+m ((2 * j) * p) p)) h′) , inj₂ h′
  where h′ = ≡.subst (_≤ m) (eq2 j p) h

-- the cell of m
cell-div : ∀ n m → Σ ℕ (λ k → (k * 2 ^ n ≤ m) × (m < suc k * 2 ^ n))
cell-div n m = m / p , lo , hi
  where
    p = 2 ^ n
    instance _ : NonZero p
    _ = m^n≢0 2 n
    e = m≡m%n+[m/n]*n m p
    lo : (m / p) * p ≤ m
    lo = ≡.subst ((m / p) * p ≤_) (≡.sym e) (m≤n+m _ _)
    hi : m < p + (m / p) * p
    hi = ≡.subst (_< p + (m / p) * p) (≡.sym e) (+-monoˡ-< ((m / p) * p) (m%n<n m p))

-- every other cell misses m
cell-other : ∀ k k′ p m → k * p ≤ m → m < suc k * p → (k′ ≡ k → ⊥) → (m < k′ * p) ⊎ (suc k′ * p ≤ m)
cell-other k k′ p m lo hi ne with <-cmp k′ k
... | tri< a _ _ = inj₂ (≤-trans (*-monoˡ-≤ p a) lo)
... | tri≈ _ e _ = ⊥-elim (ne e)
... | tri> _ _ c = inj₁ (<-≤-trans hi (*-monoˡ-≤ p c))
