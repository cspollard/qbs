{-# OPTIONS --safe --without-K #-}

-- `QBSCat S` is a concrete category over setoids, in three precise senses.
--   1. It is (strongly) equivalent to agda-categories' `SubCategory` of `Setoids` on the carriers, with the
--      probe-preserving maps as the predicate `R`.  The equivalence is the identity on objects and
--      repackages `Hom` as a `Σ`; it is a comparison rather than a definition because `QBSCat` unfolding
--      to a `Σ` makes Agda unify `Carrier ?X` against nested carriers, which is very slow downstream.
--   2. `Forget : QBSCat S → Setoids` factors through that subcategory (it is the subcategory inclusion
--      after the comparison), hence is faithful.
--   3. Forget sits in an adjoint triple  Disc ⊣ Forget ⊣ Codisc  with the discrete and the codiscrete QBS
--      on a setoid.  Consequently Forget preserves all limits and all colimits, Codisc preserves limits,
--      Disc preserves colimits, and Disc and Codisc are faithful.
module QBS.Category.Concrete where

open import Level using (Level; suc)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂; uncurry)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence using (StrongEquivalence; WeakInverse)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat; SubCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Construction.SubCategory using (Sub)
open import Categories.Functor.Limits using (Continuous; Cocontinuous)
open import Categories.Functor.Properties using (Faithful)
open import Categories.Adjoint using (_⊣_; Adjoint)
open import Categories.Adjoint.Properties using (rapl′; lapc′)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import QBS.Core
open import QBS.Category
open import QBS.Category.Forget

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- 1. QBSCat is the subcategory of Setoids of probe-preserving maps

  QBSSubCat : SubCat (Setoids ℓ ℓ) (QBS S)
  QBSSubCat = record
    { U = Carrier
    ; R = λ {X} {Y} f → ∀ {α} → Random X α → Random Y (f ∘ₛ α)
    ; Rid = λ p → p
    ; _∘R_ = λ g f p → g (f p)
    }

  QBSSub : Category (suc ℓ) ℓ ℓ
  QBSSub = SubCategory (Setoids ℓ ℓ) QBSSubCat

  ToSub : Functor (QBSCat S) QBSSub
  ToSub = record
    { F₀ = λ X → X
    ; F₁ = λ f → map f , map-random f
    ; identity = λ {A} → Setoid.refl (Carrier A)
    ; homomorphism = λ {_} {_} {C} → Setoid.refl (Carrier C)
    ; F-resp-≈ = λ p → p
    }

  FromSub : Functor QBSSub (QBSCat S)
  FromSub = record
    { F₀ = λ X → X
    ; F₁ = λ f → record { map = proj₁ f ; map-random = proj₂ f }
    ; identity = λ {A} → Setoid.refl (Carrier A)
    ; homomorphism = λ {_} {_} {C} → Setoid.refl (Carrier C)
    ; F-resp-≈ = λ p → p
    }

  QBS≃Sub : StrongEquivalence (QBSCat S) QBSSub
  QBS≃Sub = record
    { F = ToSub
    ; G = FromSub
    ; weak-inverse = record
        { F∘G≈id = niHelper record
            { η = λ X → Id.function (Carrier X) , λ p → p
            ; η⁻¹ = λ X → Id.function (Carrier X) , λ p → p
            ; commute = λ {_} {Y} f → Setoid.refl (Carrier Y)
            ; iso = λ X → record { isoˡ = Setoid.refl (Carrier X) ; isoʳ = Setoid.refl (Carrier X) }
            }
        ; G∘F≈id = niHelper record
            { η = λ X → record { map = Id.function (Carrier X) ; map-random = λ p → p }
            ; η⁻¹ = λ X → record { map = Id.function (Carrier X) ; map-random = λ p → p }
            ; commute = λ {_} {Y} f → Setoid.refl (Carrier Y)
            ; iso = λ X → record { isoˡ = Setoid.refl (Carrier X) ; isoʳ = Setoid.refl (Carrier X) }
            }
        }
    }

  -- Forget is the subcategory inclusion after the comparison (equal on objects and arrows by `refl`).
  Forget≡Sub∘ToSub : ∀ {X Y} (f : Hom S X Y) → Functor.F₁ (Sub (Setoids ℓ ℓ) QBSSubCat ∘F ToSub) f ≡.≡ map f
  Forget≡Sub∘ToSub f = ≡.refl

  ----------------------------------------------------------------------------
  -- 3. Disc ⊣ Forget ⊣ Codisc

  -- the codiscrete QBS: every sequence is random
  CodiscQ : Setoid ℓ ℓ → QBS S
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

  -- the discrete QBS: random = locally constant along a measurable countable partition
  DiscQ : Setoid ℓ ℓ → QBS S
  DiscQ A = record
    { Carrier = A
    ; probes = record
        { Random = λ α → Σ (Func Rˢ ℕˢ) λ j → Idx j × Σ (ℕ → Setoid.Carrier A) λ a →
            ∀ r → (α ⟨$⟩ r) ≈ᴬ a (j ⟨$⟩ r)
        ; random-resp = λ e (j , ix , a , h) → j , ix , a , λ r → Setoid.trans A (Setoid.sym A (e r)) (h r)
        ; const-random = λ x → constₛ 0 , idx-const 0 , (λ _ → x) , λ r → Setoid.refl A
        ; pre-random = λ {_} {f} (j , ix , a , h) m → j ∘ₛ f , idx-pre ix m , a , λ r → h (f ⟨$⟩ r)
        }
    ; glue-random = λ {i} ix α p →
        refineₛ i (λ n → proj₁ (p n)) ,
        idx-glue ix (λ n → proj₁ (proj₂ (p n))) ,
        (λ m → uncurry (λ n k → proj₁ (proj₂ (proj₂ (p n))) k) (unpair m)) ,
        λ r → Setoid.trans A (proj₂ (proj₂ (proj₂ (p (i ⟨$⟩ r)))) r)
          (Setoid.reflexive A (≡.sym (≡.cong (uncurry (λ n k → proj₁ (proj₂ (proj₂ (p n))) k))
            (unpair-pair (i ⟨$⟩ r) (proj₁ (p (i ⟨$⟩ r)) ⟨$⟩ r)))))
    }
    where _≈ᴬ_ = Setoid._≈_ A

  Codisc : Functor (Setoids ℓ ℓ) (QBSCat S)
  Codisc = record
    { F₀ = CodiscQ
    ; F₁ = λ f → record { map = f ; map-random = λ _ → tt }
    ; identity = λ {A} → Setoid.refl A
    ; homomorphism = λ {_} {_} {C} → Setoid.refl C
    ; F-resp-≈ = λ p → p
    }

  Disc : Functor (Setoids ℓ ℓ) (QBSCat S)
  Disc = record
    { F₀ = DiscQ
    ; F₁ = λ f → record
        { map = f
        ; map-random = λ (j , ix , a , h) → j , ix , (λ n → f ⟨$⟩ a n) , λ r → Func.cong f (h r)
        }
    ; identity = λ {A} → Setoid.refl A
    ; homomorphism = λ {_} {_} {C} → Setoid.refl C
    ; F-resp-≈ = λ p → p
    }

  Forget⊣Codisc : Forget S ⊣ Codisc
  Forget⊣Codisc = record
    { unit = ntHelper record
        { η = λ X → record { map = Id.function (Carrier X) ; map-random = λ _ → tt }
        ; commute = λ {_} {Y} f → Setoid.refl (Carrier Y)
        }
    ; counit = ntHelper record
        { η = λ A → Id.function A
        ; commute = λ {_} {B} f → Setoid.refl B
        }
    ; zig = λ {X} → Setoid.refl (Carrier X)
    ; zag = λ {A} → Setoid.refl A
    }

  Disc⊣Forget : Disc ⊣ Forget S
  Disc⊣Forget = record
    { unit = ntHelper record
        { η = λ A → Id.function A
        ; commute = λ {_} {B} f → Setoid.refl B
        }
    ; counit = ntHelper record
        { η = λ X → record
            { map = Id.function (Carrier X)
            ; map-random = λ {α} (j , ix , a , h) →
                random-resp X (λ r → Setoid.sym (Carrier X) (h r))
                  (glue-random X ix (λ n → constₛ (a n)) (λ n → const-random X (a n)))
            }
        ; commute = λ {_} {Y} f → Setoid.refl (Carrier Y)
        }
    ; zig = λ {A} → Setoid.refl A
    ; zag = λ {X} → Setoid.refl (Carrier X)
    }

  Codisc-faithful : Faithful Codisc
  Codisc-faithful eq = eq

  Disc-faithful : Faithful Disc
  Disc-faithful eq = eq

  -- what the adjunctions give for free
  Forget-continuous : ∀ {o ℓ′ e} → Continuous o ℓ′ e (Forget S)
  Forget-continuous = rapl′ Disc⊣Forget

  Forget-cocontinuous : ∀ {o ℓ′ e} → Cocontinuous o ℓ′ e (Forget S)
  Forget-cocontinuous = lapc′ Forget⊣Codisc

  Codisc-continuous : ∀ {o ℓ′ e} → Continuous o ℓ′ e Codisc
  Codisc-continuous = rapl′ Forget⊣Codisc

  Disc-cocontinuous : ∀ {o ℓ′ e} → Cocontinuous o ℓ′ e Disc
  Disc-cocontinuous = lapc′ Disc⊣Forget
