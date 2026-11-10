{-# OPTIONS --safe --without-K #-}

-- The opposite monoidal category: a monoidal structure on `Category.op C` with the same unit and tensor.  Monoid objects
-- of `Opposite M` are comonoid objects of `M` (used by `Monoidal.Symmetric.Algebra`).  The structure maps are reversed:
-- the unitors and the associator of the opposite category are the inverses of those of `M`.
open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Categories.Category.Monoidal.Opposite {o h e} {C : Category o h e} (M : Monoidal C) where

open import Data.Product using (_,_)

open import Categories.Functor.Bifunctor using (Bifunctor)
import Categories.Morphism C as MC
import Categories.Morphism (Category.op C) as MO
import Categories.Category.Monoidal.Utilities M as MU

private
  module C = Category C
  module M = Monoidal M
  module CO = Category C.op

-- the isomorphism of `C` read as an isomorphism of `C.op`
op-≅ : ∀ {A B} → A MC.≅ B → A MO.≅ B
op-≅ i = record { from = MC._≅_.to i ; to = MC._≅_.from i ; iso = record { isoˡ = MC._≅_.isoˡ i ; isoʳ = MC._≅_.isoʳ i } }

Opposite : Monoidal C.op
Opposite = record
  { ⊗ = record
    { F₀ = λ { (A , B) → M.⊗.₀ (A , B) }
    ; F₁ = λ { (f , g) → M.⊗.₁ (f , g) }
    ; identity = M.⊗.identity
    ; homomorphism = M.⊗.homomorphism
    ; F-resp-≈ = M.⊗.F-resp-≈
    }
  ; unit = M.unit
  ; unitorˡ = op-≅ M.unitorˡ
  ; unitorʳ = op-≅ M.unitorʳ
  ; associator = op-≅ M.associator
  ; unitorˡ-commute-from = C.Equiv.sym M.unitorˡ-commute-to
  ; unitorˡ-commute-to = C.Equiv.sym M.unitorˡ-commute-from
  ; unitorʳ-commute-from = C.Equiv.sym M.unitorʳ-commute-to
  ; unitorʳ-commute-to = C.Equiv.sym M.unitorʳ-commute-from
  ; assoc-commute-from = C.Equiv.sym M.assoc-commute-to
  ; assoc-commute-to = C.Equiv.sym M.assoc-commute-from
  ; triangle = MU.triangle-inv
  ; pentagon = MU.pentagon-inv
  }
