{-# OPTIONS --safe --without-K #-}

-- The space ℛQ of random sources, and the correspondence between random elements of X and probes ℛQ ⇒ X.
module QBS.Probes where

open import Level using (Level; suc)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import QBS.Core
open import QBS.Category

module _ {ℓ} (S : RandomSource ℓ) where
  open RandomSource S
  open QBS
  open Hom

  -- The space of random sources: the representable, whose probes are the measurable maps.
  ℛQ : QBS S
  ℛQ = record
    { Carrier = Rˢ
    ; probes = measProbes measurable
    ; glue-random = λ ij α p → meas-glue ij p
    }

  -- A random element α of X is the same as a probe ℛQ ⇒ X (Yoneda).
  probe : ∀ {X α} → Random X α → Hom S ℛQ X
  probe {X} {α} p = record
    { map = α
    ; map-random = pre-random X p
    }

  unprobe : ∀ {X} (a : Hom S ℛQ X) → Random X (map a)
  unprobe {X} a = map-random a meas-id
