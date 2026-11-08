{-# OPTIONS --safe --without-K #-}

-- The measurable maps R → R as a one-object `SubCategory` of `Setoids`, and the Yoneda-style embedding of
-- that one-object site into `QBSCat S` (the object goes to `ℛQ`): a full and faithful functor, compatible
-- with `Forget`.  This is the sense in which QBS are sheaves on the site of measurable maps.
module QBS.Category.Measurable where

open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat; SubCategory)
import Categories.Category.SubCategory.SubHom as SH
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Construction.SubCategory using (Sub)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.Functor.Properties using (Faithful; Full)

open import QBS.Core
open import QBS.Category
open import QBS.Category.Forget
open import QBS.Probes using (ℛQ; unprobe)

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open SH (Setoids ℓ ℓ) using (_∈_; mem; probe; reads; ∈-resp; ∈-pre)
  open QBS
  open Hom

  -- the sub-category is `subcat` of the source's `MeasurableMaps`
  MeasSubCat : SubCat (Setoids ℓ ℓ) (⊤ {ℓ})
  MeasSubCat = subcat

  -- one object, homs the measurable setoid maps R → R
  MeasCat : Category ℓ ℓ ℓ
  MeasCat = SubCategory (Setoids ℓ ℓ) MeasSubCat

  yoneda : Functor MeasCat (QBSCat S)
  yoneda = record
    { F₀ = λ _ → ℛQ S
    ; F₁ = λ (f , m) → record { map = f ; map-random = λ p → meas-∘ (meas₀ m) p }
    ; identity = λ {_} → Setoid.refl Rˢ
    ; homomorphism = λ {_} {_} {_} → Setoid.refl Rˢ
    ; F-resp-≈ = λ p → p
    }

  yoneda-faithful : Faithful yoneda
  yoneda-faithful eq = eq

  -- a hom ℛQ ⇒ ℛQ is a measurable map: `unprobe`
  yoneda-full : Full yoneda
  yoneda-full h = probe m , (λ {r} → reads m {r})
    where m = unprobe S h

  -- the embedding followed by `Forget` is the subcategory inclusion (equal on arrows by `refl`)
  Forget∘yoneda≡Sub : ∀ {a b} (f : Category._⇒_ MeasCat a b) →
    Functor.F₁ (Forget S ∘F yoneda) f ≡.≡ Functor.F₁ (Sub (Setoids ℓ ℓ) MeasSubCat) f
  Forget∘yoneda≡Sub f = ≡.refl

  -- the probes of a QBS as a `Setoids`-valued presheaf on the one-object site: `Σ (Rˢ ⇒ X) Random`, with
  -- precomposition by measurable maps
  probePresheaf : (X : QBS S) → Presheaf MeasCat (Setoids ℓ ℓ)
  probePresheaf X = SH.SubHom.F (Probes.subhom (probes X))

  -- the presheaf of the measurable maps (the probes of `ℛ`) is a subpresheaf of the homs into `Rˢ` (`measSubHom`, of
  -- `Core`), and is `Representable` (agda-categories); `Sub` is faithful
  measRepresentable = SH.repRepresentable (Setoids ℓ ℓ) {J = Sub (Setoids ℓ ℓ) MeasSubCat} (λ e → e) tt
