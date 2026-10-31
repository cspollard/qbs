{-# OPTIONS --safe --without-K #-}

-- `QBSCat S`: quasi-Borel spaces and homs as an agda-categories `Category` (homs equal when pointwise equal).
module QBS.Category where

open import Level using (suc)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using (Category)

open import QBS.Core

module _ {ℓ} (S : RandomSource ℓ) where
  open QBS
  open Hom

  QBSCat : Category (suc ℓ) ℓ ℓ
  QBSCat = record
    { Obj = QBS S
    ; _⇒_ = Hom S
    ; _≈_ = _≈H_ S
    ; id = idH S
    ; _∘_ = _∘H_ S
    ; assoc = λ {_} {_} {_} {D} → Setoid.refl (Carrier D)
    ; sym-assoc = λ {_} {_} {_} {D} → Setoid.refl (Carrier D)
    ; identityˡ = λ {_} {B} → Setoid.refl (Carrier B)
    ; identityʳ = λ {_} {B} → Setoid.refl (Carrier B)
    ; identity² = λ {A} → Setoid.refl (Carrier A)
    ; equiv = λ {_} {B} → record
        { refl = Setoid.refl (Carrier B)
        ; sym = λ p → Setoid.sym (Carrier B) p
        ; trans = λ p q → Setoid.trans (Carrier B) p q
        }
    ; ∘-resp-≈ = λ {_} {_} {C} {f} {h} p q →
        Setoid.trans (Carrier C) p (Func.cong (map h) q)
    }
