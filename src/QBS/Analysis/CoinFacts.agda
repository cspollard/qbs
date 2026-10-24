{-# OPTIONS --safe --without-K #-}

-- Basic facts about the fair-coin measure of Borel sets, in the form used to build its integral:
-- the whole space and the empty set, partitions, monotonicity.
module QBS.Analysis.CoinFacts where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (true; false)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.Clopen
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.BorelMeasure

module Facts (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (B : BM.BorelMeasure lem) where
  A : OmegaSemiring (L.suc L.zero)
  A = LowerRealsOmega lem
  open OmegaSemiring A renaming (Carrier to ∣A∣; zero to zero-sr)
  open Series A
  open BM.BorelMeasure B
  open Dynkin lem using ()

  μ-null : ∀ {U} (b : Borel U) → (∀ x → U x → ⊥) → μ b ≈ 0#
  μ-null {U} b nu = trans (μ-resp b ⊥-borel (λ x → nu x , (λ ()))) μ-⊥

  -- μ of a countable partition
  μ-part : ∀ {W} {E : ℕ → Pred} (bW : Borel W) (bE : ∀ j → Borel (E j)) → Disjoint E →
    W ≐ (λ x → Σ ℕ (λ j → E j x)) → μ bW ≈ ∑ᶠ (λ j → μ (bE j))
  μ-part bW bE dj e = trans (μ-resp bW (⋃ bE) e) (μ-⋃ bE dj)

  -- ∑ of a sequence supported on the first two places
  ∑ᶠ-two : ∀ (a : ℕ → ∣A∣) → (∀ n → a (suc (suc n)) ≈ 0#) → ∑ᶠ a ≈ a 0 + a 1
  ∑ᶠ-two a z = trans (∑ᶠ-shift a)
    (+-cong (refl {a 0}) (trans (∑ᶠ-shift (λ n → a (suc n)))
      (trans (+-cong (refl {a 1}) (∑ᶠ-zero {λ n → a (suc (suc n))} z)) (+-identityʳ (a 1)))))

  seq₂ : Pred → Pred → ℕ → Pred
  seq₂ U V zero = U
  seq₂ U V (suc zero) = V
  seq₂ U V (suc (suc _)) = ⊥ᵖ

  -- μ of a disjoint binary union
  μ-add : ∀ {U V W} (bU : Borel U) (bV : Borel V) (bW : Borel W) →
    (∀ x → U x → V x → ⊥) → W ≐ (λ x → U x ⊎ V x) → μ bW ≈ μ bU + μ bV
  μ-add {U} {V} {W} bU bV bW dis e = trans (μ-part bW bE dj e′) (∑ᶠ-two (λ j → μ (bE j)) (λ n → μ-⊥))
    where
      bE : ∀ j → Borel (seq₂ U V j)
      bE zero = bU
      bE (suc zero) = bV
      bE (suc (suc _)) = ⊥-borel
      dj : Disjoint (seq₂ U V)
      dj x zero zero a b = ≡.refl
      dj x zero (suc zero) a b = ⊥-elim (dis x a b)
      dj x (suc zero) zero a b = ⊥-elim (dis x b a)
      dj x (suc zero) (suc zero) a b = ≡.refl
      dj x m (suc (suc n)) a ()
      dj x (suc (suc m)) n () b
      e′ : W ≐ (λ x → Σ ℕ (λ j → seq₂ U V j x))
      e′ x = (λ w → case (proj₁ (e x) w))
           , (λ { (zero , u) → proj₂ (e x) (inj₁ u) ; (suc zero , v) → proj₂ (e x) (inj₂ v) ; (suc (suc _) , ()) })
        where case : U x ⊎ V x → Σ ℕ (λ j → seq₂ U V j x)
              case (inj₁ u) = zero , u
              case (inj₂ v) = suc zero , v

  -- monotonicity
  μ-mono : ∀ {U V} (bU : Borel U) (bV : Borel V) → (∀ x → U x → V x) → μ bU ≤ μ bV
  μ-mono {U} {V} bU bV sub = ≤-trans (≤-+ʳ {μ bU} {μ (inter₂ bV (compl bU))}) (≤-reflexive (sym eq))
    where
      D : Pred
      D x = V x × (U x → ⊥)
      eq : μ bV ≈ μ bU + μ (inter₂ bV (compl bU))
      eq = μ-add bU (inter₂ bV (compl bU)) bV (λ x u (_ , nu) → nu u) e
        where
          e : V ≐ (λ x → U x ⊎ D x)
          e x = (λ v → dec x v) , (λ { (inj₁ u) → sub x u ; (inj₂ (v , _)) → v })
            where dec : ∀ x → V x → U x ⊎ D x
                  dec x v with lem (U x)
                  ... | inj₁ u = inj₁ u
                  ... | inj₂ nu = inj₂ (v , nu)
