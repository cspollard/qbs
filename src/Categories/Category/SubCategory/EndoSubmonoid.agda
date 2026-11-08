{-# OPTIONS --safe --without-K #-}

-- Submonoids of the endomorphism monoid of an object, as one-object sub-categories.
--   * `EndoSubmonoid X`, a predicate `P` on the endomorphisms `X ⇒ X` that respects `≈`, holds of `id` and is
--     closed under `∘`: a submonoid of `End(X)`;
--   * `subcat`, the one-object `SubCat` those endomorphisms form, so that `SubCategory C subcat` has the
--     object `X` and the homs `Σ (X ⇒ X) P`.
-- Route: `SubCat` has no `≈`-respecting field, so `P-resp-≈` is the only law added over its `Rid` and `_∘R_`;
-- `subcat` repackages the three remaining fields with the single object `X`.
open import Categories.Category.Core using (Category)

module Categories.Category.SubCategory.EndoSubmonoid {o h e} (C : Category o h e) where

open import Level using (suc; _⊔_)
open import Data.Unit.Polymorphic.Base using (⊤)

open import Categories.Category.SubCategory C using (SubCat)

open Category C

record EndoSubmonoid {p} (X : Obj) : Set (h ⊔ e ⊔ suc p) where
  field
    P : X ⇒ X → Set p
    P-resp-≈ : ∀ {f g} → f ≈ g → P f → P g
    P-id : P id
    P-∘ : ∀ {f g} → P f → P g → P (f ∘ g)

  -- the one-object sub-category
  subcat : SubCat {ℓ′ = p} (⊤ {p})
  subcat = record { U = λ _ → X ; R = P ; Rid = P-id ; _∘R_ = P-∘ }
