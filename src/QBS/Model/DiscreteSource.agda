{-# OPTIONS --safe --without-K #-}

-- The discrete random source: R = ℕ with every function measurable and every
-- function R → ℕ a measurable partition.  The corresponding QBS are the sets
-- with a σ-ideal of "countable" subsets; probability on them is countable-support
-- probability.  It is the first concrete model for the abstract interfaces.
module QBS.Model.DiscreteSource where

open import Level using (Level; Lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import Function.Bundles using (_⟨$⟩_)

open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCat)
import Categories.Category.SubCategory.SubHom as SH

open import QBS.Core using (RandomSource; MeasurableMaps; ℕˢ; ⇑ℕ)
open import QBS.Pieces

open import QBS.Model.Pairing

discreteSource : ∀ ℓ → RandomSource ℓ
discreteSource ℓ = record
  { subcat = sc
  ; isRandomSource = record
    { measurable = M
    ; covering = record
      { partitions = fromPred M (ℕˢ {ℓ}) (λ _ → ⊤) (λ _ → tt) (λ _ _ → tt)
      ; Meas₀-glue = λ _ _ → tt
      }
    ; common-refinement = λ {j} {i} _ _ →
        let k = ⇑ℕ (λ r → pair (lower (j ⟨$⟩ r)) (lower (i (lower (j ⟨$⟩ r)) ⟨$⟩ r))) in
        k , mem (k , tt) (Setoid.refl (ℕˢ {ℓ})) , unpair
          , λ r → unpair-pair (lower (j ⟨$⟩ r)) (lower (i (lower (j ⟨$⟩ r)) ⟨$⟩ r))
    }
  }
  where
    open SH (Setoids ℓ ℓ) using (mem)
    sc : SubCat (Setoids ℓ ℓ) {ℓ′ = ℓ} (⊤ {ℓ})
    sc = record { U = λ _ → setoid (Lift ℓ ℕ) ; R = λ _ → ⊤ ; Rid = tt ; _∘R_ = λ _ _ → tt }
    M : MeasurableMaps sc
    M = record { Meas₀-const = λ _ → tt }

-- One shared name for `discreteSource ℓ`.  Modules that each defined their own private alias
-- `S = discreteSource ℓ` made Agda compare the (large) cartesian-closed structures of `QBSCat S` through
-- the two aliases by unfolding them (30 s per conversion in `Model/ProbInstance`); a single alias makes
-- the two spellings syntactically equal.
module DS (ℓ : Level) where
  S : RandomSource ℓ
  S = discreteSource ℓ
  {-# INLINE S #-}
