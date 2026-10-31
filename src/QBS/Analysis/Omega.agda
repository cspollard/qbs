{-# OPTIONS --safe --without-K #-}

-- Values for measures: a commutative semiring with a compatible partial order (for the extended
-- non-negative reals, the natural order a ≤ b ⟺ ∃ d, a + d = b), suprema of increasing sequences
-- preserved by + and ×, and cancellation of elements ≤ 1.
-- The extended non-negative reals [0, ∞] are the intended instance.
-- `OmegaSemiring` is an ω-continuous semiring in the sense of Kuich (1987, "The Kleene and the
-- Parikh theorem in complete semirings") and Ésik–Kuich ("Equational axioms for a theory of automata"):
-- an ordered semiring with suprema of increasing sequences, along which + and × are continuous.
-- The stdlib (2.3) has no ordered-semiring bundle, so the record is local, but its order is a stdlib
-- `IsPartialOrder` (`isPartialOrder`, with the bundled `poset`).
module QBS.Analysis.Omega where

import Level as L
open import Level using (Level; _⊔_)
open import Function.Base using (_∘_)
open import Algebra.Bundles using (CommutativeSemiring)
import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Properties
import Data.Sum.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Structures using (IsPartialOrder)

-- a commutative semiring with a compatible order: monotone `+` and `*`, `0` least, complements below `1`
record OrderedSemiring (ℓ : Level) : Set (L.suc ℓ) where
  field
    commutativeSemiring : CommutativeSemiring ℓ ℓ
  open CommutativeSemiring commutativeSemiring public

  infix 4 _≤_
  field
    _≤_ : Carrier → Carrier → Set ℓ
    isPartialOrder : IsPartialOrder _≈_ _≤_
    0-least : ∀ {a} → 0# ≤ a
    ≤-+ʳ : ∀ {a b} → a ≤ a + b
    +-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
    *-mono : ∀ c {a b} → a ≤ b → c * a ≤ c * b
    -- subtraction below 1: every c ≤ 1 has a complement
    complement : ∀ {c} → c ≤ 1# → Σ Carrier (λ d → c + d ≈ 1#)

  poset : Poset ℓ ℓ ℓ
  poset = record { isPartialOrder = isPartialOrder }

  open IsPartialOrder isPartialOrder public
    using (≤-resp-≈)
    renaming (reflexive to ≤-reflexive; trans to ≤-trans; antisym to ≤-antisym; refl to ≤-refl)

  Increasing : (ℕ → Carrier) → Set ℓ
  Increasing c = ∀ n → c n ≤ c (suc n)

-- an ordered semiring with suprema of increasing sequences, along which `+` and `*` are continuous
record OmegaSemiring (ℓ : Level) : Set (L.suc ℓ) where
  field
    ordered : OrderedSemiring ℓ
  open OrderedSemiring ordered public

  field
    ⨆ : (c : ℕ → Carrier) → Increasing c → Carrier
    ⨆-ub : ∀ c (inc : Increasing c) n → c n ≤ ⨆ c inc
    ⨆-lub : ∀ c (inc : Increasing c) {b} → (∀ n → c n ≤ b) → ⨆ c inc ≤ b
    -- continuity of + and × along increasing sequences
    +-⨆ : ∀ a c (inc : Increasing c) (inc′ : Increasing (λ n → a + c n)) →
      a + ⨆ c inc ≈ ⨆ (λ n → a + c n) inc′
    *-⨆ : ∀ a c (inc : Increasing c) (inc′ : Increasing (λ n → a * c n)) →
      a * ⨆ c inc ≈ ⨆ (λ n → a * c n) inc′
    -- elements below 1 can be cancelled
    cancel : ∀ {a x y} → a ≤ 1# → a + x ≈ a + y → x ≈ y

  open SetoidReasoning setoid

  ----------------------------------------------------------------------------
  -- the order

  ≤-resp : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → a ≤ b → a′ ≤ b′
  ≤-resp ea eb p = ≤-trans (≤-reflexive (sym ea)) (≤-trans p (≤-reflexive eb))

  ----------------------------------------------------------------------------
  -- suprema

  ⨆-cong : ∀ {c c′} (inc : Increasing c) (inc′ : Increasing c′) →
    (∀ n → c n ≈ c′ n) → ⨆ c inc ≈ ⨆ c′ inc′
  ⨆-cong {c} {c′} inc inc′ e = ≤-antisym
    (⨆-lub c inc (λ n → ≤-trans (≤-reflexive (e n)) (⨆-ub c′ inc′ n)))
    (⨆-lub c′ inc′ (λ n → ≤-trans (≤-reflexive (sym (e n))) (⨆-ub c inc n)))

  -- increasing sequences are monotone
  inc-mono : ∀ c → Increasing c → ∀ {n m} → n ℕ.≤′ m → c n ≤ c m
  inc-mono c inc ℕ.≤′-refl = ≤-refl
  inc-mono c inc (ℕ.≤′-step h) = ≤-trans (inc-mono c inc h) (inc _)

  -- an eventually constant increasing sequence has that constant as supremum
  ⨆-const-from : ∀ c (inc : Increasing c) (N : ℕ) {v} →
    (∀ n → N ℕ.≤′ n → c n ≈ v) → ⨆ c inc ≈ v
  ⨆-const-from c inc N {v} e = ≤-antisym
    (⨆-lub c inc bound)
    (≤-trans (≤-reflexive (sym (e N ℕ.≤′-refl))) (⨆-ub c inc N))
    where
      ≤′-total : ∀ n m → n ℕ.≤′ m ⊎ m ℕ.≤′ n
      ≤′-total n m with Data.Nat.Properties.≤-total n m
      ... | inj₁ h = inj₁ (Data.Nat.Properties.≤⇒≤′ h)
      ... | inj₂ h = inj₂ (Data.Nat.Properties.≤⇒≤′ h)

      bound : ∀ n → c n ≤ v
      bound n with ≤′-total n N
      ... | inj₁ h = ≤-trans (inc-mono c inc h) (≤-reflexive (e N ℕ.≤′-refl))
      ... | inj₂ h = ≤-reflexive (e n h)

  ⨆-const : ∀ v (inc : Increasing (λ _ → v)) → ⨆ (λ _ → v) inc ≈ v
  ⨆-const v inc = ⨆-const-from (λ _ → v) inc 0 (λ _ _ → refl)
