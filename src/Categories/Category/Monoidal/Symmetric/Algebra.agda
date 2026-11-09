{-# OPTIONS --safe --without-K #-}

-- Internal algebra in a symmetric monoidal category, laid out like the standard library's `Algebra.Structures` /
-- `Algebra.Bundles`: `IsX` records are the laws on a carrier object, `X` bundles are a carrier with its `IsX`.
-- Each level extends the one below it:
--   IsCommutativeMonoid, IsCommutativeComonoid   (the monoid layer reuses agda-categories' `Object.Monoid`;
--                                                 the comonoid is a monoid of the opposite monoidal structure)
--   IsCommutativeMonoidWithZero (below the semiring),
--   IsGroup < IsAbelianGroup, IsCommutativeSemiring, and IsCommutativeRing (an abelian group under + and a
--   commutative monoid under *, as in `Algebra.Structures.IsRing`; it yields an `IsCommutativeSemiring`)
-- Several structures on one carrier (addition and multiplication) are several `IsMonoid` values over the same
-- object, so no equality of carriers is needed.
--
-- Multiplication distributes over addition, which uses its variable twice, and a general symmetric monoidal
-- category has no diagonal.  So distributivity, absorption and inverses are stated relative to a commutative comonoid
-- `(Δ, δ)` on the carrier, as in copy-discard categories (Cockett-Lack, Restriction categories III; Fritz, A synthetic
-- approach to Markov kernels).  Unlike agda-categories' `CounitalCopy`, `Δ` and `δ` are not required to be natural,
-- so Markov-style categories are allowed.  In a cartesian category `Δ` is the diagonal and `δ` is `!`, and every
-- comonoid law and the `δ`-compatibility laws below hold automatically.
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

module Categories.Category.Monoidal.Symmetric.Algebra
  {o h e} {C : Category o h e} {M : Monoidal C} (S : Symmetric M)
  where

open import Level using (_⊔_)

open import Categories.Category.Monoidal.Braided.Properties using (module Shorthands)
open import Categories.Category.Monoidal.Properties M using (monoidal-Op)
import Categories.Object.Monoid M as Mon
import Categories.Object.Monoid monoidal-Op as Comon

open Category C
open Symmetric S
open Shorthands braided using (σ⇒)

-- the middle-four interchange `(A ⊗ B) ⊗ (C ⊗ D) ⇒ (A ⊗ C) ⊗ (B ⊗ D)`
swap-mid : ∀ {A B C D} → (A ⊗₀ B) ⊗₀ (C ⊗₀ D) ⇒ (A ⊗₀ C) ⊗₀ (B ⊗₀ D)
swap-mid = associator.to ∘ (id ⊗₁ (associator.from ∘ (σ⇒ ⊗₁ id) ∘ associator.to)) ∘ associator.from

------------------------------------------------------------------------
-- Structures

record IsCommutativeMonoid (X : Obj) : Set (h ⊔ e) where
  field
    isMonoid : Mon.IsMonoid X
  open Mon.IsMonoid isMonoid public
  field
    comm : μ ∘ σ⇒ ≈ μ

  -- the underlying monoid object, e.g. for `Categories.Monad.Writer`
  monoid : Mon.Monoid
  monoid = record { Carrier = X ; isMonoid = isMonoid }

record IsCommutativeComonoid (X : Obj) : Set (h ⊔ e) where
  field
    isComonoid : Comon.IsMonoid X
  open Comon.IsMonoid isComonoid public
    renaming (μ to Δ; η to δ; assoc to Δ-assoc; identityˡ to δ-identityˡ; identityʳ to δ-identityʳ)
  field
    cocomm : σ⇒ ∘ Δ ≈ Δ

module _ {X : Obj} (K : IsCommutativeComonoid X) where
  open IsCommutativeComonoid K

  -- `neg` is a two-sided inverse for the monoid; `x + (-x)` uses `x` twice, so it is stated with the copy `Δ`
  record IsGroup : Set (h ⊔ e) where
    field
      isMonoid : Mon.IsMonoid X
    open Mon.IsMonoid isMonoid public
    field
      neg : X ⇒ X
      inverseˡ : μ ∘ (neg ⊗₁ id) ∘ Δ ≈ η ∘ δ
      inverseʳ : μ ∘ (id ⊗₁ neg) ∘ Δ ≈ η ∘ δ

  record IsAbelianGroup : Set (h ⊔ e) where
    field
      isGroup : IsGroup
    open IsGroup isGroup public
    field
      comm : μ ∘ σ⇒ ≈ μ

    isCommutativeMonoid : IsCommutativeMonoid X
    isCommutativeMonoid = record { isMonoid = isMonoid ; comm = comm }

  -- a commutative monoid `(X, μ, η)` with an absorbing element `zero⇒`, and no addition: the part of a semiring
  -- (written multiplicatively) that soft conditioning needs of its weights.  `x · 0 = 0` has no terminal unit to
  -- discard `x` into, so the right side uses the discard `δ`.
  record IsCommutativeMonoidWithZero : Set (h ⊔ e) where
    field
      *-isCommutativeMonoid : IsCommutativeMonoid X
      zero⇒ : unit ⇒ X

    module Mul = IsCommutativeMonoid *-isCommutativeMonoid
    open Mul public using () renaming (μ to μ*; η to η*)

    field
      zeroʳ : μ* ∘ (id ⊗₁ zero⇒) ≈ zero⇒ ∘ δ ∘ unitorʳ.from
      -- `δ` is a monoid homomorphism from the multiplication into the trivial monoid on the unit, and a retraction
      -- of `0` (all automatic when `unit` is terminal)
      δ-unit : δ ∘ η* ≈ id
      δ-mul : δ ∘ μ* ≈ unitorˡ.from ∘ (δ ⊗₁ δ)
      δ-zero : δ ∘ zero⇒ ≈ id

  record IsCommutativeSemiring : Set (h ⊔ e) where
    field
      +-isCommutativeMonoid : IsCommutativeMonoid X
      *-isCommutativeMonoid : IsCommutativeMonoid X

    module Add = IsCommutativeMonoid +-isCommutativeMonoid
    open Add public using () renaming (μ to μ⁺; η to η⁺)
    module Mul = IsCommutativeMonoid *-isCommutativeMonoid
    open Mul public using () renaming (μ to μ*; η to η*)

    field
      -- `x · (y + z) = x · y + x · z`; the other side follows from commutativity of `μ*`
      distribˡ : μ* ∘ (id ⊗₁ μ⁺) ≈ μ⁺ ∘ (μ* ⊗₁ μ*) ∘ swap-mid ∘ (Δ ⊗₁ id)
      -- `x · 0 = 0`; with no terminal unit the right side discards `x` with `δ`
      zeroʳ : μ* ∘ (id ⊗₁ η⁺) ≈ η⁺ ∘ δ ∘ unitorʳ.from
      -- `δ` is a monoid homomorphism from the multiplication into the trivial monoid on the unit, and a retraction
      -- of `0` (all automatic when `unit` is terminal)
      δ-unit : δ ∘ η* ≈ id
      δ-mul : δ ∘ μ* ≈ unitorˡ.from ∘ (δ ⊗₁ δ)
      δ-zero : δ ∘ η⁺ ≈ id

    isCommutativeMonoidWithZero : IsCommutativeMonoidWithZero
    isCommutativeMonoidWithZero = record
      { *-isCommutativeMonoid = *-isCommutativeMonoid
      ; zero⇒ = η⁺
      ; zeroʳ = zeroʳ
      ; δ-unit = δ-unit
      ; δ-mul = δ-mul
      ; δ-zero = δ-zero
      }

  -- as in the standard library's `IsRing`: an abelian group under `+`, a commutative monoid under `*`, and the laws
  record IsCommutativeRing : Set (h ⊔ e) where
    field
      +-isAbelianGroup : IsAbelianGroup
      *-isCommutativeMonoid : IsCommutativeMonoid X

    module Add = IsAbelianGroup +-isAbelianGroup
    open Add public using () renaming (μ to μ⁺; η to η⁺)
    module Mul = IsCommutativeMonoid *-isCommutativeMonoid
    open Mul public using () renaming (μ to μ*; η to η*)

    field
      distribˡ : μ* ∘ (id ⊗₁ μ⁺) ≈ μ⁺ ∘ (μ* ⊗₁ μ*) ∘ swap-mid ∘ (Δ ⊗₁ id)
      zeroʳ : μ* ∘ (id ⊗₁ η⁺) ≈ η⁺ ∘ δ ∘ unitorʳ.from
      δ-unit : δ ∘ η* ≈ id
      δ-mul : δ ∘ μ* ≈ unitorˡ.from ∘ (δ ⊗₁ δ)
      δ-zero : δ ∘ η⁺ ≈ id

    isCommutativeSemiring : IsCommutativeSemiring
    isCommutativeSemiring = record
      { +-isCommutativeMonoid = Add.isCommutativeMonoid
      ; *-isCommutativeMonoid = *-isCommutativeMonoid
      ; distribˡ = distribˡ
      ; zeroʳ = zeroʳ
      ; δ-unit = δ-unit
      ; δ-mul = δ-mul
      ; δ-zero = δ-zero
      }

------------------------------------------------------------------------
-- Bundles

record CommutativeMonoid : Set (o ⊔ h ⊔ e) where
  field
    Carrier : Obj
    isCommutativeMonoid : IsCommutativeMonoid Carrier
  open IsCommutativeMonoid isCommutativeMonoid public

record CommutativeComonoid : Set (o ⊔ h ⊔ e) where
  field
    Carrier : Obj
    isCommutativeComonoid : IsCommutativeComonoid Carrier
  open IsCommutativeComonoid isCommutativeComonoid public

record CommutativeMonoidWithZero : Set (o ⊔ h ⊔ e) where
  field
    Carrier : Obj
    isCommutativeComonoid : IsCommutativeComonoid Carrier
    isCommutativeMonoidWithZero : IsCommutativeMonoidWithZero isCommutativeComonoid
  open IsCommutativeComonoid isCommutativeComonoid public
  open IsCommutativeMonoidWithZero isCommutativeMonoidWithZero public

record CommutativeSemiring : Set (o ⊔ h ⊔ e) where
  field
    Carrier : Obj
    isCommutativeComonoid : IsCommutativeComonoid Carrier
    isCommutativeSemiring : IsCommutativeSemiring isCommutativeComonoid
  open IsCommutativeComonoid isCommutativeComonoid public
  open IsCommutativeSemiring isCommutativeSemiring public

  commutativeMonoidWithZero : CommutativeMonoidWithZero
  commutativeMonoidWithZero = record
    { Carrier = Carrier
    ; isCommutativeComonoid = isCommutativeComonoid
    ; isCommutativeMonoidWithZero = isCommutativeMonoidWithZero
    }

record CommutativeRing : Set (o ⊔ h ⊔ e) where
  field
    Carrier : Obj
    isCommutativeComonoid : IsCommutativeComonoid Carrier
    isCommutativeRing : IsCommutativeRing isCommutativeComonoid
  open IsCommutativeComonoid isCommutativeComonoid public
  open IsCommutativeRing isCommutativeRing public

  commutativeSemiring : CommutativeSemiring
  commutativeSemiring = record
    { Carrier = Carrier
    ; isCommutativeComonoid = isCommutativeComonoid
    ; isCommutativeSemiring = isCommutativeSemiring
    }
