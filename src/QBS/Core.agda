{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces over an abstract random source.
--   RandomSource S : the "reals" R (a type with measurable endomorphisms and countable partitions R → ℕ).
--   QBS S          : a setoid with a set of random elements R → X, closed under constants, precomposition, gluing.
--   Hom X Y        : setoid maps preserving random elements.   Also identity and composition.
module QBS.Core where

open import Level using (Level; suc)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

-- The parameters of the theory: a "random source" R (the reals) together with the measurable maps
-- R → R, the measurable countable partitions of R, and a pairing of ℕ.  Three small pieces make up
-- a `RandomSource`; all their fields are re-exported by it.

-- the reals and their measurable endomorphisms: closed under identity, composition, extensionality, constants
record Measurability (ℓ : Level) : Set (suc ℓ) where
  field
    R : Set ℓ
    Meas : (R → R) → Set ℓ
    meas-id : Meas id
    meas-∘ : ∀ {f g} → Meas f → Meas g → Meas (f ∘ g)
    meas-ext : ∀ {f g} → (∀ r → f r ≡ g r) → Meas f → Meas g
    meas-const : ∀ r → Meas (const r)

-- measurable index functions R → ℕ (i.e. measurable countable partitions), along which measurable
-- functions glue
record Partitions {ℓ} (M : Measurability ℓ) : Set (suc ℓ) where
  open Measurability M
  field
    Idx : (R → ℕ) → Set ℓ
    meas-glue : ∀ {j} {f : ℕ → R → R} → Idx j → (∀ n → Meas (f n)) → Meas (λ r → f (j r) r)
    idx-const : ∀ n → Idx (const n)
    idx-pre : ∀ {i f} → Idx i → Meas f → Idx (i ∘ f)

-- a bijection ℕ × ℕ ≅ ℕ
record NatPairing : Set where
  field
    pair : ℕ → ℕ → ℕ
    unpair : ℕ → ℕ × ℕ
    unpair-pair : ∀ n m → unpair (pair n m) ≡ (n , m)

record RandomSource (ℓ : Level) : Set (suc ℓ) where
  field
    measurable : Measurability ℓ
  open Measurability measurable public
  field
    partitions : Partitions measurable
  open Partitions partitions public
  field
    pairing : NatPairing
  open NatPairing pairing public
  field
    -- indices glue under the pairing
    idx-glue : ∀ {j} {i : ℕ → R → ℕ} → Idx j → (∀ n → Idx (i n)) →
      Idx (λ r → pair (j r) (i (j r) r))

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S

  -- A quasi-Borel space: a setoid with a class of "random elements" R → X
  -- that respects the setoid equality.
  record QBS : Set (suc ℓ) where
    no-eta-equality
    field
      Carrier : Setoid ℓ ℓ
    open Setoid Carrier public using () renaming (Carrier to ∣_∣; _≈_ to _≈ˣ_)
    field
      Random : (R → ∣_∣) → Set ℓ
      random-resp : ∀ {α β} → (∀ r → α r ≈ˣ β r) → Random α → Random β
      const-random : ∀ x → Random (const x)
      pre-random : ∀ {α f} → Random α → Meas f → Random (α ∘ f)
      glue-random : ∀ {i} → Idx i → (α : ℕ → R → ∣_∣) →
        (∀ n → Random (α n)) → Random (λ r → α (i r) r)

  open QBS

  -- Morphisms: setoid maps preserving random elements.
  record Hom (X Y : QBS) : Set ℓ where
    field
      map : Func (Carrier X) (Carrier Y)
      map-random : ∀ {α} → Random X α → Random Y (λ r → map ⟨$⟩ α r)

  open Hom

  idH : ∀ {X} → Hom X X
  idH {X} = record { map = Id.function (Carrier X) ; map-random = λ p → p }

  _∘H_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
  g ∘H f = record
    { map = Comp.function (map f) (map g)
    ; map-random = λ p → map-random g (map-random f p)
    }

  -- Morphisms are equal when they agree pointwise.
  _≈H_ : ∀ {X Y} → Hom X Y → Hom X Y → Set ℓ
  _≈H_ {X} {Y} f g = ∀ x → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)
