{-# OPTIONS --safe --without-K #-}

-- Quasi-Borel spaces over an abstract random source.  Elementarily: a QBS is a setoid X together with a set of
-- "random elements" ℛ → X, closed under precomposition with measurable maps, constants, and countable measurable
-- case splits.  Equivalently (the rest of this header): concrete sheaves on a one-object site.
--   MeasurableMaps Rˢ : a monoid 𝕄 of setoid maps Rˢ → Rˢ, an `EndoSubmonoid` of `Setoids` containing the constants;
--                    `subcat` is the one-object sub-category of `Setoids` it forms.
--   Probes M X     : a sub-𝕄-set of the setoid maps Rˢ → X, closed under ≈ and containing the constants;
--                    i.e. a subpresheaf of Setoid(Rˢ, X) on 𝕄.
--   Partitions     : the measurable countable partitions R → ℕ, the probes of discrete ℕ.  With `common-refinement`
--                    they form a coverage J on 𝕄 (`idx-const` the trivial cover, `idx-pre` pullback,
--                    `common-refinement` composition of covers), and `meas-glue` says J is subcanonical.
--   QBS S          : a setoid with probes that glue along J (the sheaf condition).
--   Hom X Y        : setoid maps preserving probes (natural transformations).  Also identity and composition.
module QBS.Core where

open import Level using (Level; suc; _⊔_; 0ℓ)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp
open import Data.Nat.Base using (ℕ)
open import Function.Base using (const)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
import Categories.Category.SubCategory.EndoSubmonoid as Endo
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
-- R → R, and the measurable countable partitions of R.  Two small pieces make up
-- an `IsRandomSource` on a setoid Rˢ, and `RandomSource` bundles it with Rˢ; all their fields are re-exported.

-- the monoid 𝕄 ⊆ End(Rˢ) of measurable maps on a setoid Rˢ: a submonoid of the endomorphisms of Rˢ in `Setoids`
-- (so `subcat` is the one-object sub-category they form) that contains the constants
record MeasurableMaps {ℓ} (Rˢ : Setoid ℓ ℓ) : Set (suc ℓ) where
  open Setoid Rˢ public using () renaming (Carrier to R; _≈_ to _≈ᴿ_)
  field
    endo : Endo.EndoSubmonoid (Setoids ℓ ℓ) {p = ℓ} Rˢ
  open Endo.EndoSubmonoid endo public renaming (P to Meas; P-id to meas-id; P-∘ to meas-∘)
  field
    meas-const : ∀ r → Meas (constₛ r)

  -- the equality of maps in `Setoids` is pointwise
  meas-ext : ∀ {f g} → (∀ r → f ⟨$⟩ r ≈ᴿ g ⟨$⟩ r) → Meas f → Meas g
  meas-ext e = P-resp-≈ (λ {x} → e x)

-- Probes of a setoid X: the 𝕄-set of "random elements" Rˢ → X.
module _ {ℓ} {Rˢ : Setoid ℓ ℓ} (M : MeasurableMaps Rˢ) where
  open MeasurableMaps M

  record Probes {c e} (X : Setoid c e) : Set (suc ℓ ⊔ c ⊔ e) where
    open Setoid X using (_≈_)
    field
      Random : Func Rˢ X → Set ℓ
      random-resp : ∀ {α β} → (∀ r → α ⟨$⟩ r ≈ β ⟨$⟩ r) → Random α → Random β
      const-random : ∀ x → Random (constₛ x)
      pre-random : ∀ {α f} → Random α → Meas f → Random (α ∘ₛ f)

    -- gluing under a map g: glue (g ∘ αₙ) is g ∘ (glue α)
    random-glue-∘ : ∀ {a b} {A : Setoid a b} {j : Func Rˢ ℕˢ} (g : Func A X) (α : ℕ → Func Rˢ A) →
      Random (glueₛ j (λ n → g ∘ₛ α n)) → Random (g ∘ₛ glueₛ j α)
    random-glue-∘ g α = random-resp (λ _ → Setoid.refl X)

    -- gluing then precomposing: (glue j f) ∘ γ is the glue of the f n ∘ γ along j ∘ γ
    random-glue-pre : ∀ {a b} {A : Setoid a b} {j : Func A ℕˢ} (f : ℕ → Func A X) (γ : Func Rˢ A) →
      Random (glueₛ (j ∘ₛ γ) (λ n → f n ∘ₛ γ)) → Random (glueₛ j f ∘ₛ γ)
    random-glue-pre f γ = random-resp (λ _ → Setoid.refl X)

  -- the measurable maps are the probes of R itself (the representable)
  measProbes : Probes Rˢ
  measProbes = record
    { Random = Meas ; random-resp = meas-ext ; const-random = meas-const ; pre-random = meas-∘ }

-- the measurable countable partitions R → ℕ, the probes of discrete ℕ, along which measurable maps glue
record Partitions {ℓ} {Rˢ : Setoid ℓ ℓ} (M : MeasurableMaps Rˢ) : Set (suc ℓ) where
  open MeasurableMaps M
  field
    partitions : Probes M ℕˢ
  open Probes partitions public using () renaming
    (Random to Idx; random-resp to idx-ext; const-random to idx-const; pre-random to idx-pre)
  field
    meas-glue : ∀ {j f} → Idx j → (∀ n → Meas (f n)) → Meas (glueₛ j f)

-- the laws of a random source on the setoid Rˢ.  Covers compose through a common refinement: refining each piece
-- of `j` by `i n` gives a partition `k` that determines the pair `(j r , i (j r) r)`, recovered by `decode`.
-- (No pairing function of ℕ is fixed: each source chooses `k` and `decode`.)
record IsRandomSource {ℓ} (Rˢ : Setoid ℓ ℓ) : Set (suc ℓ) where
  field
    measurable : MeasurableMaps Rˢ
  open MeasurableMaps measurable public
  field
    covering : Partitions measurable
  open Partitions covering public
  field
    common-refinement : ∀ {j} {i : ℕ → Func Rˢ ℕˢ} → Idx j → (∀ n → Idx (i n)) →
      Σ (Func Rˢ ℕˢ) λ k → Idx k × Σ (ℕ → ℕ × ℕ) λ decode →
        ∀ r → decode (k ⟨$⟩ r) ≡ (j ⟨$⟩ r , i (j ⟨$⟩ r) ⟨$⟩ r)

record RandomSource (ℓ : Level) : Set (suc ℓ) where
  field
    Rˢ : Setoid ℓ ℓ
    isRandomSource : IsRandomSource Rˢ
  open IsRandomSource isRandomSource public

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

  -- The codiscrete QBS on a setoid: every sequence is random.
  CodiscQ : Setoid ℓ ℓ → QBS
  CodiscQ A = record
    { Carrier = A
    ; probes = record
        { Random = λ _ → ⊤
        ; random-resp = λ _ _ → tt
        ; const-random = λ _ → tt
        ; pre-random = λ _ _ → tt
        }
    ; glue-random = λ _ _ _ → tt
    }

  -- The QBS generated by a presheaf of pieces: α is random iff, locally on a measurable countable
  -- partition i, it is a piece, α r ≈ ev (c (i r)) r.  Here P is the set of pieces, ev reads a piece off at
  -- a point, `pre` precomposes a piece with a measurable map (`ev-pre`), and every point is a constant piece.
  -- This is the sheaf generated by a presheaf (for the coverage of countable partitions); compare Heunen,
  -- Kammar, Staton, Yang, LICS 2017, "A convenient category for higher-order probability theory".
  -- The sums, coequalizers and indexed sums are all of this form.
  GluedQBS : (Z : Setoid ℓ ℓ) (P : Set ℓ) (ev : P → R → Setoid.Carrier Z) →
    (pre : ∀ {f} → P → Meas f → P) →
    (ev-pre : ∀ {f} (c : P) (m : Meas f) r → Setoid._≈_ Z (ev (pre c m) r) (ev c (f ⟨$⟩ r))) →
    (pt : ∀ z → Σ P λ c → ∀ r → Setoid._≈_ Z (ev c r) z) → QBS
  GluedQBS Z P ev pre ev-pre pt = record
    { Carrier = Z
    ; probes = record
        { Random = λ α → Σ (Func Rˢ ℕˢ) λ i → Idx i × Σ (ℕ → P) λ c → ∀ r → (α ⟨$⟩ r) ≈ᶻ ev (c (i ⟨$⟩ r)) r
        ; random-resp = λ e (i , ii , c , q) → i , ii , c , λ r → Setoid.trans Z (Setoid.sym Z (e r)) (q r)
        ; const-random = λ z → constₛ 0 , idx-const 0 , const (proj₁ (pt z)) , λ r → Setoid.sym Z (proj₂ (pt z) r)
        ; pre-random = λ {_} {f} (i , ii , c , q) m →
            i ∘ₛ f , idx-pre ii m , (λ n → pre (c n) m) ,
            λ r → Setoid.trans Z (q (f ⟨$⟩ r)) (Setoid.sym Z (ev-pre (c (i ⟨$⟩ (f ⟨$⟩ r))) m r))
        }
    ; glue-random = λ {j} ij α p →
        let i = λ n → proj₁ (p n)
            c = λ n → proj₁ (proj₂ (proj₂ (p n)))
            ref = common-refinement ij (λ n → proj₁ (proj₂ (p n)))
            u = proj₁ (proj₂ (proj₂ ref))
            c′ = λ m → c (proj₁ (u m)) (proj₂ (u m))
        in proj₁ ref
         , proj₁ (proj₂ ref)
         , c′
         , λ r → subst (λ u → (α (j ⟨$⟩ r) ⟨$⟩ r) ≈ᶻ ev (c (proj₁ u) (proj₂ u)) r)
                       (sym (proj₂ (proj₂ (proj₂ ref)) r))
                       (proj₂ (proj₂ (proj₂ (p (j ⟨$⟩ r)))) r)
    }
    where _≈ᶻ_ = Setoid._≈_ Z

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
