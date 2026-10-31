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

  -- The space of random sources: its random elements are the measurable maps.
  ℛQ : QBS S
  ℛQ = record
    { Carrier = Rˢ
    ; Random = Meas
    ; random-resp = λ e → meas-ext e
    ; random-cong = meas-resp
    ; const-random = meas-const
    ; pre-random = meas-∘
    ; glue-random = λ ij α p → meas-glue ij p
    }

  -- A random element α of X is the same as a probe ℛQ ⇒ X.
  probe : ∀ {X α} → Random X α → Hom S ℛQ X
  probe {X} {α} p = record
    { map = record { to = α ; cong = random-cong X p }
    ; map-random = pre-random X p
    }

  unprobe : ∀ {X} (a : Hom S ℛQ X) → Random X (λ r → map a ⟨$⟩ r)
  unprobe a = map-random a meas-id

