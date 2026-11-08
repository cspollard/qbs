{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces over an abstract random source.  Elementarily: a QBS is a setoid X together with a set of
-- "random elements" ℛ → X, closed under precomposition with measurable maps, constants, and countable measurable
-- case splits.  Equivalently (the rest of this header): concrete sheaves on a one-object site.
--   MeasurableMaps sc : the monoid 𝕄 of measurable maps Rˢ → Rˢ is a one-object sub-category `sc` of `Setoids`
--                    (agda-categories `SubCat`).  `Meas f` says f is pointwise equal to a hom of `sc` (the image of
--                    the inclusion `Sub`), so it respects ≈ by construction; only the constants are extra data.
--   Probes M X     : a sub-𝕄-set of the setoid maps Rˢ → X, closed under ≈ and containing the constants;
--                    i.e. a subpresheaf of Setoid(Rˢ, X) on 𝕄.  `probesSubHom` is the
--                    subpresheaf with its injection into the Hom functor.
--   Partitions     : the measurable countable partitions R → ℕ, the probes of discrete ℕ.  With `common-refinement`
--                    they form a coverage J on 𝕄 (`idx-const` the trivial cover, `idx-pre` pullback,
--                    `common-refinement` composition of covers), and `meas-glue` says J is subcanonical.
--   QBS S          : a setoid with probes that glue along J (the sheaf condition).
--   Hom X Y        : setoid maps preserving probes (natural transformations).  Also identity and composition.
module QBS.Core where

open import Level using (Level; suc; _⊔_; 0ℓ; Lift; lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp
open import Data.Nat.Base using (ℕ)
open import Function.Base using (const)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.SubCategory using (Sub)
import Categories.Category.SubCategory.SubHom as SH
import Categories.Morphism.Constant as Const
open import Relation.Binary.PropositionalEquality.Core using (_≡_; sym; subst)
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

-- `constₛ b` is a constant morphism of `Setoids` (`Categories.Morphism.Constant`)
constₛ-isConstant : ∀ {a b} {A B : Setoid a b} (x : Setoid.Carrier B) →
  Const.IsConstant (Setoids a b) {A} {B} (constₛ x)
constₛ-isConstant {B = B} x f g {_} = Setoid.refl B

-- discrete ℕ, lifted to any level
ℕˢ : ∀ {ℓ} → Setoid ℓ ℓ
ℕˢ {ℓ} = setoid (Lift ℓ ℕ)

-- ... in particular an index function into ℕ
⇑ℕ : ∀ {a ℓ} {A : Set a} → (A → ℕ) → Func (setoid A) (ℕˢ {ℓ})
⇑ℕ f = ⇑ (λ r → lift (f r))

-- r ↦ α (j r) r
glueₛ : ∀ {a b c d ℓ} {A : Setoid a b} {B : Setoid c d} → Func A (ℕˢ {ℓ}) → (ℕ → Func A B) → Func A B
glueₛ {B = B} j α = record
  { to = λ r → α (lower (j ⟨$⟩ r)) ⟨$⟩ r
  ; cong = λ {r} {r′} e → Setoid.trans B (Func.cong (α (lower (j ⟨$⟩ r))) e)
      (Setoid.reflexive B (≡.cong (λ n → α (lower n) ⟨$⟩ r′) (Func.cong j e)))
  }

-- equality of setoid maps: pointwise
infix 4 _≈ₛ_
_≈ₛ_ : ∀ {a b c d} {A : Setoid a b} {B : Setoid c d} → Func A B → Func A B → Set (a ⊔ d)
_≈ₛ_ {B = B} f g = ∀ r → Setoid._≈_ B (f ⟨$⟩ r) (g ⟨$⟩ r)

-- gluing under a map g: glue (g ∘ αₙ) is g ∘ (glue α)
glueₛ-∘ : ∀ {a b c d e f ℓ} {A : Setoid a b} {B : Setoid c d} {C : Setoid e f} {j : Func A (ℕˢ {ℓ})}
  (g : Func B C) (α : ℕ → Func A B) → glueₛ j (λ n → g ∘ₛ α n) ≈ₛ (g ∘ₛ glueₛ j α)
glueₛ-∘ {C = C} _ _ _ = Setoid.refl C

-- gluing then precomposing: (glue j f) ∘ γ is the glue of the f n ∘ γ along j ∘ γ
glueₛ-pre : ∀ {a b a′ b′ c d ℓ} {A : Setoid a b} {A′ : Setoid a′ b′} {B : Setoid c d} {j : Func A (ℕˢ {ℓ})}
  (f : ℕ → Func A B) (γ : Func A′ A) → glueₛ (j ∘ₛ γ) (λ n → f n ∘ₛ γ) ≈ₛ (glueₛ j f ∘ₛ γ)
glueₛ-pre {B = B} _ _ _ = Setoid.refl B

-- The parameters of the theory: a "random source" R (the reals) together with the measurable maps
-- R → R, and the measurable countable partitions of R.  Two small pieces make up
-- an `IsRandomSource` on a setoid Rˢ, and `RandomSource` bundles it with Rˢ; all their fields are re-exported.

-- the monoid 𝕄 ⊆ End(Rˢ) of measurable maps: a one-object sub-category `sc` of `Setoids` (whose object is the setoid
-- `Rˢ`, whose homs `Meas` are the measurable maps, closed under identity and composition) whose maps respect `≈`
-- and which contains the constants.
record MeasurableMaps {ℓ} (sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})) : Set (suc ℓ) where
  Rˢ : Setoid ℓ ℓ
  Rˢ = SubCat.U sc tt

  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)

  open Setoid Rˢ public using () renaming (Carrier to R; _≈_ to _≈ᴿ_)

  -- the raw predicate of the sub-category
  Meas₀ : Func Rˢ Rˢ → Set ℓ
  Meas₀ = SubCat.R sc

  field
    Meas₀-const : ∀ r → Meas₀ (constₛ r)

  -- the sub-category `sc` is a subpresheaf of the homs `Rˢ ⇒ Rˢ` (the representable `repSubHom` along `Sub`)
  -- and the measurable maps are its members (`_∈ι`): maps pointwise equal to a hom of `sc`
  measSubHom : SH.SubHom (Setoids ℓ ℓ) (Sub (Setoids ℓ ℓ) sc) Rˢ
  measSubHom = SH.repSubHom (Setoids ℓ ℓ) {J = Sub (Setoids ℓ ℓ) sc} (λ e → e) tt

  Meas : Func Rˢ Rˢ → Set ℓ
  Meas f = f ∈ measSubHom

  meas₀ : ∀ {f} → Meas₀ f → Meas f
  meas₀ m = mem (_ , m) (Setoid.refl Rˢ)

  meas-id : Meas (Id.function Rˢ)
  meas-id = meas₀ (SubCat.Rid sc)

  meas-∘ : ∀ {f g} → Meas f → Meas g → Meas (f ∘ₛ g)
  meas-∘ {f} a b =
    ∈-resp (λ {r} → Func.cong f (reads b {r}))
      (∈-pre (probe b) a)

  meas-resp : ∀ {f g} → (∀ {r} → f ⟨$⟩ r ≈ᴿ g ⟨$⟩ r) → Meas f → Meas g
  meas-resp e a = ∈-resp e a

  meas-const : ∀ r → Meas (constₛ r)
  meas-const r = meas₀ (Meas₀-const r)

-- Probes of a setoid X: the 𝕄-set of "random elements" Rˢ → X, given as a subpresheaf of the homs `Rˢ ⇒ X` on the
-- one-object sub-category `sc` of the measurable maps (`SubHom` along the inclusion `Sub`) whose image contains the
-- constants.  The random elements are the image of `ι`; closure under ≈, constants and precomposition is derived.
module _ {ℓ} {sc} (M : MeasurableMaps {ℓ} sc) where
  open MeasurableMaps M
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)

  record Probes (X : Setoid ℓ ℓ) : Set (suc ℓ) where
    open Setoid X using (_≈_)
    field
      subhom : SH.SubHom (Setoids ℓ ℓ) (Sub (Setoids ℓ ℓ) sc) X

    -- the random elements are the members of the subpresheaf (the maps `ι a`), so they respect `≈` and
    -- precomposition by measurable maps by construction
    Random : Func Rˢ X → Set ℓ
    Random α = α ∈ subhom

    field
      const-image : ∀ x → Random (constₛ x)

    random-resp : ∀ {α β} → α ≈ₛ β → Random α → Random β
    random-resp e = ∈-resp (λ {r} → e r)

    const-random : ∀ x → Random (constₛ x)
    const-random = const-image

    pre-random : ∀ {α f} → Random α → Meas f → Random (α ∘ₛ f)
    pre-random {α} a mf =
      ∈-resp (λ {r} → Func.cong α (reads mf {r}))
        (∈-pre (probe mf) a)

  -- the measurable maps are the probes of R itself: the members of the representable `measSubHom`
  measProbes : Probes Rˢ
  measProbes = record { subhom = measSubHom ; const-image = meas-const }

-- the measurable countable partitions R → ℕ, the probes of discrete ℕ, along which measurable maps glue
record Partitions {ℓ} {sc} (M : MeasurableMaps {ℓ} sc) : Set (suc ℓ) where
  open MeasurableMaps M
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)
  field
    partitions : Probes M (ℕˢ {ℓ})

  open Probes partitions public using () renaming
    (Random to Idx; random-resp to idx-ext; const-random to idx-const; pre-random to idx-pre)

  field
    Meas₀-glue : ∀ {j f} → Idx j → (∀ n → Meas₀ (f n)) → Meas₀ (glueₛ j f)

  meas-glue : ∀ {j f} → Idx j → (∀ n → Meas (f n)) → Meas (glueₛ j f)
  meas-glue {j} pj mf =
    mem (glueₛ j (λ n → proj₁ (probe (mf n))) , Meas₀-glue pj (λ n → proj₂ (probe (mf n))))
      (λ {r} → reads (mf (lower (j ⟨$⟩ r))) {r})

-- the laws of a random source on the one-object sub-category `sc`.  Covers compose through a common refinement:
-- refining each piece
-- of `j` by `i n` gives a partition `k` that determines the pair `(j r , i (j r) r)`, recovered by `decode`.
-- (No pairing function of ℕ is fixed: each source chooses `k` and `decode`.)
record IsRandomSource {ℓ} (sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})) : Set (suc ℓ) where
  field
    measurable : MeasurableMaps sc

  open MeasurableMaps measurable public

  field
    covering : Partitions measurable

  open Partitions covering public

  field
    common-refinement : ∀ {j} {i : ℕ → Func Rˢ ℕˢ} → Idx j → (∀ n → Idx (i n)) →
      Σ (Func Rˢ ℕˢ) λ k → Idx k × Σ (ℕ → ℕ × ℕ) λ decode →
        ∀ r → decode (lower (k ⟨$⟩ r)) ≡ (lower (j ⟨$⟩ r) , lower (i (lower (j ⟨$⟩ r)) ⟨$⟩ r))

record RandomSource (ℓ : Level) : Set (suc ℓ) where
  field
    subcat : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})
    isRandomSource : IsRandomSource subcat

  open IsRandomSource isRandomSource public

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)

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
  _≈H_ {X} {Y} f g = ∀ {x} → Setoid._≈_ (Carrier Y) (map f ⟨$⟩ x) (map g ⟨$⟩ x)
