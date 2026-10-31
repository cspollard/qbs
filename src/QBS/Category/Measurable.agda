{-# OPTIONS --safe --without-K #-}

-- The measurable maps R → R as a one-object `SubCategory` of `Setoids`, and the Yoneda-style embedding of
-- that one-object site into `QBSCat S` (the object goes to `ℛQ`): a full and faithful functor, compatible
-- with `Forget`.  This is the sense in which QBS are sheaves on the site of measurable maps.
module QBS.Category.Measurable where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat; SubCategory)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Construction.SubCategory using (Sub)
open import Categories.Functor.Properties using (Faithful; Full; FullyFaithful)

open import QBS.Core
open import QBS.Category
open import QBS.Category.Forget
open import QBS.Probes using (ℛQ; unprobe)

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  MeasSubCat : SubCat (Setoids ℓ ℓ) (⊤ {ℓ})
  MeasSubCat = record { U = λ _ → Rˢ ; R = Meas ; Rid = meas-id ; _∘R_ = meas-∘ }

  -- one object, homs the measurable setoid maps R → R
  MeasCat : Category ℓ ℓ ℓ
  MeasCat = SubCategory (Setoids ℓ ℓ) MeasSubCat

  yoneda : Functor MeasCat (QBSCat S)
  yoneda = record
    { F₀ = λ _ → ℛQ S
    ; F₁ = λ (f , m) → record { map = f ; map-random = λ p → meas-∘ m p }
    ; identity = λ {_} → Setoid.refl Rˢ
    ; homomorphism = λ {_} {_} {_} → Setoid.refl Rˢ
    ; F-resp-≈ = λ p → p
    }

  yoneda-faithful : Faithful yoneda
  yoneda-faithful eq = eq

  -- a hom ℛQ ⇒ ℛQ is a measurable map: `unprobe`
  yoneda-full : Full yoneda
  yoneda-full h = (map h , unprobe S h) , Setoid.refl Rˢ

  -- the embedding followed by `Forget` is the subcategory inclusion (equal on arrows by `refl`)
  Forget∘yoneda≡Sub : ∀ {a b} (f : Category._⇒_ MeasCat a b) →
    Functor.F₁ (Forget S ∘F yoneda) f ≡.≡ Functor.F₁ (Sub (Setoids ℓ ℓ) MeasSubCat) f
  Forget∘yoneda≡Sub f = ≡.refl
