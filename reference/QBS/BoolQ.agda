{-# OPTIONS --safe --without-K #-}

-- The Boolean QBS `BoolQ = 1Q +Q 1Q`, the coproduct (`Colimits`) of two points, over any random source.
--
--   * `boolQ : Bool → ∣ BoolQ ∣` (`true ↦ inj₁`, `false ↦ inj₂`), `trueQ`, `falseQ`;
--   * `constQ z : Hom X Z`, the constant morphism, and the case analysis `ifQ a b : Hom BoolQ Z`, the copairing
--     `[const a , const b]` of `Colimits.copair`, with `ifQ a b true ≡ a` and `ifQ a b false ≡ b` by computation.
--
-- Unlike `CodiscQ Bool` (every function from the sample space is random, so no indicator is measurable), a random
-- element of `BoolQ` is, locally on a measurable partition, constantly `true` or constantly `false`; hence every
-- `ifQ a b` is measurable into any `Z`.
module QBS.BoolQ where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Data.Unit.Polymorphic using (tt)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Limits using (1Q)
open import QBS.Colimits using (_+Q_; copair)

module BoolOn {ℓ} (S : RandomSource ℓ) where
  open RandomSource S using (Rˢ)
  open QBS using (∣_∣; Carrier; const-random)

  BoolQ : QBS S
  BoolQ = _+Q_ S (1Q S) (1Q S)

  boolQ : Bool → ∣ BoolQ ∣
  boolQ true = inj₁ tt
  boolQ false = inj₂ tt

  trueQ falseQ : ∣ BoolQ ∣
  trueQ = boolQ true
  falseQ = boolQ false

  boolQ-cong : ∀ {a b} → a ≡.≡ b → Setoid._≈_ (Carrier BoolQ) (boolQ a) (boolQ b)
  boolQ-cong {a} ≡.refl = Setoid.refl (Carrier BoolQ) {boolQ a}

  -- constant morphisms
  constQ : ∀ {X Z : QBS S} → ∣ Z ∣ → Hom S X Z
  constQ {Z = Z} z = record { map = constₛ z ; map-random = λ _ → const-random Z z }

  -- case analysis on a Boolean
  ifQ : ∀ {Z : QBS S} → ∣ Z ∣ → ∣ Z ∣ → Hom S BoolQ Z
  ifQ {Z} a b = copair S (constQ {1Q S} {Z} a) (constQ {1Q S} {Z} b)

  ifQ-true : ∀ {Z : QBS S} (a b : ∣ Z ∣) → Hom.map (ifQ {Z} a b) ⟨$⟩ trueQ ≡.≡ a
  ifQ-true a b = ≡.refl

  ifQ-false : ∀ {Z : QBS S} (a b : ∣ Z ∣) → Hom.map (ifQ {Z} a b) ⟨$⟩ falseQ ≡.≡ b
  ifQ-false a b = ≡.refl
