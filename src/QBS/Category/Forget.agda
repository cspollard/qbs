{-# OPTIONS --safe --without-K #-}

-- The forgetful functor `QBSCat S → Setoids`.  It is faithful (a hom is its underlying setoid map plus a
-- property), which is what makes QBS concrete: a subcategory of Setoids in the sense of `SubCategory`,
-- though not defined as one.  Kept apart from `QBS.Category` so that the modules importing the category
-- do not also load agda-categories' `Setoids`.
module QBS.Category.Forget where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using (Faithful)

open import QBS.Core
open import QBS.Category

module _ {ℓ} (S : RandomSource ℓ) where
  open QBS
  open Hom

  Forget : Functor (QBSCat S) (Setoids ℓ ℓ)
  Forget = record
    { F₀ = Carrier
    ; F₁ = map
    ; identity = λ {A} → Setoid.refl (Carrier A)
    ; homomorphism = λ {_} {_} {C} → Setoid.refl (Carrier C)
    ; F-resp-≈ = λ p {x} → p x
    }

  Forget-faithful : Faithful Forget
  Forget-faithful eq x = eq {x}
