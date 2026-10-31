{-# OPTIONS --safe --without-K #-}

-- The discrete random source: R = ℕ with every function measurable and every
-- function R → ℕ a measurable partition.  The corresponding QBS are the sets
-- with a σ-ideal of "countable" subsets; probability on them is countable-support
-- probability.  It is the first concrete model for the abstract interfaces.
module QBS.Model.DiscreteSource where

open import Level using (Level; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import QBS.Core using (RandomSource)
open import QBS.Model.Pairing

discreteSource : ∀ ℓ → RandomSource ℓ
discreteSource ℓ = record
  { measurable = record
    { Rˢ = setoid (Lift ℓ ℕ)
    ; Meas = λ _ → ⊤
    ; meas-id = tt
    ; meas-∘ = λ _ _ → tt
    ; meas-ext = λ _ _ → tt
    ; meas-const = λ _ → tt
    }
  ; covering = record
    { partitions = record
      { Random = λ _ → ⊤
      ; random-resp = λ _ _ → tt
      ; const-random = λ _ → tt
      ; pre-random = λ _ _ → tt
      }
    ; meas-glue = λ _ _ → tt
    }
  ; pairing = record { pair = pair ; unpair = unpair ; unpair-pair = unpair-pair }
  ; idx-glue = λ _ _ → tt
  }

-- One shared name for `discreteSource ℓ`.  Modules that each defined their own private alias
-- `S = discreteSource ℓ` made Agda compare the (large) cartesian-closed structures of `QBSCat S` through
-- the two aliases by unfolding them (30 s per conversion in `Model/ProbInstance`); a single alias makes
-- the two spellings syntactically equal.
module DS (ℓ : Level) where
  S : RandomSource ℓ
  S = discreteSource ℓ
  {-# INLINE S #-}
