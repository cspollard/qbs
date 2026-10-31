{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces over an abstract random source, as concrete sheaves on a one-object site.
--   Measurability  : a monoid 𝕄 of setoid maps Rˢ → Rˢ (closed under ≈, containing the constants).
--   Probes M X     : a sub-𝕄-set of the setoid maps Rˢ → X, closed under ≈ and containing the constants;
--                    i.e. a subpresheaf of Setoid(Rˢ, X) on 𝕄.
--   Partitions     : the measurable countable partitions R → ℕ, the probes of discrete ℕ.  With `idx-glue`
--                    they form a coverage J on 𝕄 (`idx-const` the trivial cover, `idx-pre` pullback,
--                    `idx-glue` composition of covers), and `meas-glue` says J is subcanonical.
--   QBS S          : a setoid with probes that glue along J (the sheaf condition).
--   Hom X Y        : setoid maps preserving probes (natural transformations).  Also identity and composition.
module QBS.Core where

open import Level using (Level; suc; _⊔_; 0ℓ)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

-- Setoid maps: composition, constants, discrete ℕ, and gluing a family along an index map.
infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {a b c d e f} {A : Setoid a b} {B : Setoid c d} {C : Setoid e f} → Func B C → Func A B → Func A C
g ∘ₛ f = Comp.function f g

constₛ : ∀ {a b c d} {A : Setoid a b} {B : Setoid c d} → Setoid.Carrier B → Func A B
constₛ {B = B} b = record { to = λ _ → b ; cong = λ _ → Setoid.refl B }

-- every function out of a ≡-setoid is a setoid map
⇑ : ∀ {a c d} {A : Set a} {B : Setoid c d} → (A → Setoid.Carrier B) → Func (setoid A) B
⇑ {B = B} f = record { to = f ; cong = λ e → Setoid.reflexive B (≡.cong f e) }

ℕˢ : Setoid 0ℓ 0ℓ
ℕˢ = setoid ℕ

-- r ↦ α (j r) r
glueₛ : ∀ {a b c d} {A : Setoid a b} {B : Setoid c d} → Func A ℕˢ → (ℕ → Func A B) → Func A B
glueₛ {B = B} j α = record
  { to = λ r → α (j ⟨$⟩ r) ⟨$⟩ r
  ; cong = λ {r} {r′} e → Setoid.trans B (Func.cong (α (j ⟨$⟩ r)) e)
      (Setoid.reflexive B (≡.cong (λ n → α n ⟨$⟩ r′) (Func.cong j e)))
  }

-- The parameters of the theory: a "random source" R (the reals) together with the measurable maps
-- R → R, the measurable countable partitions of R, and a pairing of ℕ.  Three small pieces make up
-- a `RandomSource`; all their fields are re-exported by it.

-- the monoid 𝕄 ⊆ End(Rˢ) of measurable maps
record Measurability (ℓ : Level) : Set (suc ℓ) where
  field
    Rˢ : Setoid ℓ ℓ
  open Setoid Rˢ public using () renaming (Carrier to R; _≈_ to _≈ᴿ_)
  field
    Meas : Func Rˢ Rˢ → Set ℓ
    meas-ext : ∀ {f g} → (∀ r → f ⟨$⟩ r ≈ᴿ g ⟨$⟩ r) → Meas f → Meas g
    meas-id : Meas (Id.function Rˢ)
    meas-∘ : ∀ {f g} → Meas f → Meas g → Meas (f ∘ₛ g)
    meas-const : ∀ r → Meas (constₛ r)

-- Probes of a setoid X: the 𝕄-set of "random elements" Rˢ → X.
module _ {ℓ} (M : Measurability ℓ) where
  open Measurability M

  record Probes {c e} (X : Setoid c e) : Set (suc ℓ ⊔ c ⊔ e) where
    open Setoid X using (_≈_)
    field
      Random : Func Rˢ X → Set ℓ
      random-resp : ∀ {α β} → (∀ r → α ⟨$⟩ r ≈ β ⟨$⟩ r) → Random α → Random β
      const-random : ∀ x → Random (constₛ x)
      pre-random : ∀ {α f} → Random α → Meas f → Random (α ∘ₛ f)

    -- probes are determined by their underlying functions
    random-cast : ∀ {α β} → (∀ r → α ⟨$⟩ r ≡ β ⟨$⟩ r) → Random α → Random β
    random-cast e = random-resp (λ r → Setoid.reflexive X (e r))

    -- gluing under a map g: glue (g ∘ αₙ) is g ∘ (glue α)
    random-glue-∘ : ∀ {a b} {A : Setoid a b} {j : Func Rˢ ℕˢ} (g : Func A X) (α : ℕ → Func Rˢ A) →
      Random (glueₛ j (λ n → g ∘ₛ α n)) → Random (g ∘ₛ glueₛ j α)
    random-glue-∘ g α = random-cast (λ _ → refl)

  -- the measurable maps are the probes of R itself (the representable)
  measProbes : Probes Rˢ
  measProbes = record
    { Random = Meas ; random-resp = meas-ext ; const-random = meas-const ; pre-random = meas-∘ }

-- the measurable countable partitions R → ℕ, the probes of discrete ℕ, along which measurable maps glue
record Partitions {ℓ} (M : Measurability ℓ) : Set (suc ℓ) where
  open Measurability M
  field
    partitions : Probes M ℕˢ
  open Probes partitions public using () renaming
    (Random to Idx; random-resp to idx-ext; const-random to idx-const; pre-random to idx-pre)
  field
    meas-glue : ∀ {j f} → Idx j → (∀ n → Meas (f n)) → Meas (glueₛ j f)

-- a bijection ℕ × ℕ ≅ ℕ
record NatPairing : Set where
  field
    pair : ℕ → ℕ → ℕ
    unpair : ℕ → ℕ × ℕ
    unpair-pair : ∀ n m → unpair (pair n m) ≡ (n , m)

  pairₛ : ℕ → Func ℕˢ ℕˢ
  pairₛ n = record { to = pair n ; cong = ≡.cong (pair n) }

  -- the composite cover of j by the i n: r ↦ pair (j r) (i (j r) r)
  refineₛ : ∀ {a b} {A : Setoid a b} → Func A ℕˢ → (ℕ → Func A ℕˢ) → Func A ℕˢ
  refineₛ j i = glueₛ j (λ n → pairₛ n ∘ₛ i n)

record RandomSource (ℓ : Level) : Set (suc ℓ) where
  field
    measurable : Measurability ℓ
  open Measurability measurable public
  field
    covering : Partitions measurable
  open Partitions covering public
  field
    pairing : NatPairing
  open NatPairing pairing public
  field
    -- covers compose: refining each piece of j by i n is again a partition
    idx-glue : ∀ {j} {i : ℕ → Func Rˢ ℕˢ} → Idx j → (∀ n → Idx (i n)) → Idx (refineₛ j i)

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S

  -- A quasi-Borel space: a setoid with probes that glue along measurable partitions.
  record QBS : Set (suc ℓ) where
    no-eta-equality
    field
      Carrier : Setoid ℓ ℓ
      probes : Probes measurable Carrier
    open Setoid Carrier public using () renaming (Carrier to ∣_∣; _≈_ to _≈ˣ_)
    open Probes probes public
    field
      glue-random : ∀ {i} → Idx i → (α : ℕ → Func Rˢ Carrier) → (∀ n → Random (α n)) → Random (glueₛ i α)

  open QBS

  -- Morphisms: setoid maps preserving probes.
  record Hom (X Y : QBS) : Set ℓ where
    field
      map : Func (Carrier X) (Carrier Y)
      map-random : ∀ {α} → Random X α → Random Y (map ∘ₛ α)

  open Hom

  idH : ∀ {X} → Hom X X
  idH {X} = record { map = Id.function (Carrier X) ; map-random = λ p → p }

  _∘H_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
  g ∘H f = record
    { map = map g ∘ₛ map f
    ; map-random = λ p → map-random g (map-random f p)
    }

  -- Morphisms are equal when they agree pointwise.
  _≈H_ : ∀ {X Y} → Hom X Y → Hom X Y → Set ℓ
  _≈H_ {X} {Y} f g = ∀ x → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)
