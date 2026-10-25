{-# OPTIONS --safe --without-K #-}

-- A worked example: probabilistic programs in Agda's `do`-notation on the discrete QBS model.
--
-- A program is a countable-support measure on a type of Agda values (`Prog T`).  `pure` and
-- `_>>=_` are the unit and bind of the probability monad of `Model/Monad.agda`, with `_>>=_`
-- taking an arbitrary Agda function `T → Prog U` as its continuation (in the discrete model every
-- function is a morphism, since every probe is a gluing of constants).  Everything is generic in
-- the weight semiring; `Flip` needs a "half".  Meaning is given by `∫ p f`, the expectation of
-- the test function `f`: we prove the expectation rules and compute two programs.  `BoolDemo`
-- instantiates the Boolean (possibilistic) semiring.
module QBS.Example.Program where

import Level as L
open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Model.DiscreteSource using (discreteSource; module DS)
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.WeightClasses using (probClass)
open import QBS.Model.Monad
open import QBS.Model.BoolSemiring using (boolComplete)

-- `K` is the weight class (probability measures, or sub-probability measures); `ok1` says that a
-- weight function of total mass 1 is admissible.
module Programs {ℓ : L.Level} (A : CompleteSemiring ℓ) (K : WeightClass A)
    (ok1 : ∀ {μ} → CompleteSemiring._≈_ A (CompleteSemiring.∑ A μ) (CompleteSemiring.1# A) → WeightClass.Ok K μ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open SetoidReasoning Aˢ
  private
    open DS ℓ using (S)
    R = L.Lift ℓ ℕ
  open Measures A K using (Pre; mk; ∫; ηPre; mapPre; joinPre; TQ; ∫-η; ∫-join; ∫ᶠ) public
  open Pre
  open QBS using (glue-random; const-random)

  -- the QBS of an Agda type: every function is a probe
  Disc : Set ℓ → QBS S
  Disc T = record
    { Carrier = setoid T
    ; Random = λ _ → ⊤
    ; random-resp = λ _ _ → tt
    ; const-random = λ _ → tt
    ; pre-random = λ _ _ → tt
    ; glue-random = λ _ _ _ → tt
    }

  -- test functions on a type
  test : ∀ {T : Set ℓ} → (T → ∣A∣) → Func (setoid T) Aˢ
  test g = record { to = g ; cong = λ { ≡.refl → Setoid.refl Aˢ } }

  ----------------------------------------------------------------------------
  -- programs

  Prog : Set ℓ → Set ℓ
  Prog T = Pre (Disc T)

  pure : ∀ {T} → T → Prog T
  pure {T} = ηPre {Disc T}

  -- any Agda function into programs is a morphism Disc T ⇒ T (Disc U): a family r ↦ k (β r)
  -- is a gluing of the constant families along r ↦ r
  kernel : ∀ {T U} → (T → Prog U) → Hom S (Disc T) (TQ (Disc U))
  kernel {T} {U} k = record
    { map = record { to = k ; cong = λ { ≡.refl _ → Setoid.refl Aˢ } }
    ; map-random = λ {β} _ →
        glue-random (TQ (Disc U)) {i = lower} tt (λ n _ → k (β (lift n)))
          (λ n → const-random (TQ (Disc U)) (k (β (lift n))))
    }

  infixl 1 _>>=_ _>>_
  _>>=_ : ∀ {T U} → Prog T → (T → Prog U) → Prog U
  p >>= k = joinPre (mapPre (kernel k) p)

  _>>_ : ∀ {T U} → Prog T → Prog U → Prog U
  p >> q = p >>= λ _ → q

  ----------------------------------------------------------------------------
  -- expectation rules

  ∫-pure : ∀ {T} (a : T) (g : T → ∣A∣) → ∫ (pure a) (test g) ≈ g a
  ∫-pure {T} a g = ∫-η {Disc T} a (test g)

  ∫-bind : ∀ {T U} (p : Prog T) (k : T → Prog U) (g : U → ∣A∣) →
    ∫ (p >>= k) (test g) ≈ ∑ (λ r → μ p r * ∫ (k (α p r)) (test g))
  ∫-bind p k g = ∫-join (mapPre (kernel k) p) (test g)

  ----------------------------------------------------------------------------
  -- a fair coin, given a half

  -- (the coin's outcomes live in any `B : Set ℓ` with two named elements and a conjunction)
  module Flip (half : ∣A∣) (half+half : half + half ≈ 1#) (B : Set ℓ) (tB fB : B) (_∧B_ : B → B → B) where
    private
      r₀ r₁ : R
      r₀ = lift 0
      r₁ = lift 1

      weights : R → ∣A∣
      weights r = half * dirac r₀ r + half * dirac r₁ r

      diracMass : ∀ (j : R) → ∑ (dirac j) ≈ 1#
      diracMass j = trans (∑-cong (λ r → sym (*-identityʳ (dirac j r)))) (dirac-∑ j (λ _ → 1#))

      mass : ∀ j → ∑ (λ r → half * dirac j r) ≈ half
      mass j = begin
        ∑ (λ r → half * dirac j r)   ≈⟨ sym (∑-distribˡ half (dirac j)) ⟩
        half * ∑ (dirac j)           ≈⟨ *-cong refl (diracMass j) ⟩
        half * 1#                    ≈⟨ *-identityʳ half ⟩
        half                         ∎

      total : ∑ weights ≈ 1#
      total = begin
        ∑ weights                                         ≈⟨ ∑-+ (λ r → half * dirac r₀ r) (λ r → half * dirac r₁ r) ⟩
        ∑ (λ r → half * dirac r₀ r) + ∑ (λ r → half * dirac r₁ r)  ≈⟨ +-cong (mass r₀) (mass r₁) ⟩
        half + half                                       ≈⟨ half+half ⟩
        1#                                                ∎

      face : R → B
      face r = if lower r ≡ᵇ 0 then tB else fB

    flip : Prog B
    flip = mk face tt weights (ok1 total)

    -- E[g(flip)] = ½ g(true) + ½ g(false)
    ∫-flip : ∀ (g : B → ∣A∣) → ∫ flip (test g) ≈ half * g tB + half * g fB
    ∫-flip g = begin
      ∑ (λ r → (half * dirac r₀ r + half * dirac r₁ r) * g (face r))
        ≈⟨ ∑-cong (λ r → distribʳ (g (face r)) (half * dirac r₀ r) (half * dirac r₁ r)) ⟩
      ∑ (λ r → (half * dirac r₀ r) * g (face r) + (half * dirac r₁ r) * g (face r))
        ≈⟨ ∑-+ (λ r → (half * dirac r₀ r) * g (face r)) (λ r → (half * dirac r₁ r) * g (face r)) ⟩
      ∑ (λ r → (half * dirac r₀ r) * g (face r)) + ∑ (λ r → (half * dirac r₁ r) * g (face r))
        ≈⟨ +-cong (pick r₀) (pick r₁) ⟩
      half * g tB + half * g fB ∎
      where
        pick : ∀ j → ∑ (λ r → (half * dirac j r) * g (face r)) ≈ half * g (face j)
        pick j = begin
          ∑ (λ r → (half * dirac j r) * g (face r))   ≈⟨ ∑-cong (λ r → *-assoc half (dirac j r) (g (face r))) ⟩
          ∑ (λ r → half * (dirac j r * g (face r)))   ≈⟨ ∑-scale half (λ r → dirac j r * g (face r)) ⟩
          half * ∑ (λ r → dirac j r * g (face r))     ≈⟨ *-cong refl (dirac-∑ j (g ∘′ face)) ⟩
          half * g (face j)                           ∎
          where _∘′_ = λ f h x → f (h x)

    -- sampling a coin and continuing with `k`
    ∫-flip->>= : ∀ {U} (k : B → Prog U) (g : U → ∣A∣) →
      ∫ (flip >>= k) (test g) ≈ half * ∫ (k tB) (test g) + half * ∫ (k fB) (test g)
    ∫-flip->>= k g = trans (∫-bind flip k g) (∫-flip (λ a → ∫ (k a) (test g)))

    ----------------------------------------------------------------------------
    -- programs, in `do`-notation

    -- the conjunction of two fair coins
    both : Prog B
    both = do
      a ← flip
      b ← flip
      pure (a ∧B b)

    -- E[g(both)]
    ∫-both : ∀ (g : B → ∣A∣) → ∫ both (test g) ≈
      half * (half * g (tB ∧B tB) + half * g (tB ∧B fB)) + half * (half * g (fB ∧B tB) + half * g (fB ∧B fB))
    ∫-both g = trans (∫-flip->>= (λ a → flip >>= λ b → pure (a ∧B b)) g)
      (+-cong (*-cong refl (trans (∫-flip->>= (λ b → pure (tB ∧B b)) g)
                                  (+-cong (*-cong refl (∫-pure (tB ∧B tB) g)) (*-cong refl (∫-pure (tB ∧B fB) g)))))
              (*-cong refl (trans (∫-flip->>= (λ b → pure (fB ∧B b)) g)
                                  (+-cong (*-cong refl (∫-pure (fB ∧B tB) g)) (*-cong refl (∫-pure (fB ∧B fB) g))))))

----------------------------------------------------------------------------
-- Boolean (possibilistic) instance: which outcomes are possible?

module BoolDemo (lem : ∀ (P : Set) → P ⊎ (P → ⊥ {L.zero})) where
  open Programs (boolComplete L.zero lem) (probClass (boolComplete L.zero lem)) (λ p → p)
  open Flip (lift true) ≡.refl Bool true false _∧_

  -- `both` can produce `true` (weights are possibilities, so the expectation of the indicator
  -- of `true` is "possible" = true) ...
  true-possible : ∫ both (test (λ b → lift b)) ≡ lift true
  true-possible = ∫-both (λ b → lift b)

  -- ... and can produce `false`.
  false-possible : ∫ both (test (λ b → lift (not b))) ≡ lift true
  false-possible = ∫-both (λ b → lift (not b))
