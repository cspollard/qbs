{-# OPTIONS --safe --without-K #-}

-- Continuity of the fair-coin measure along increasing unions, and completion of a partial
-- simple function (disjoint Borel cells with values) to a simple function on the whole space.
module QBS.Analysis.CoinCont where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda using (∁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinFacts
open import QBS.Analysis.CoinSimple
open import QBS.Classical using (LEM₀)

module Cont (lem : LEM₀) (B : BM.BorelMeasure lem) where
  open Simple lem B
  open OmegaSemiring A renaming (Carrier to ∣A∣; zero to zero-sr)
  open Series A
  open SetoidReasoning setoid
  open BM.BorelMeasure B using (μ; μ-resp; μ-⋃)
  open Sf

  ----------------------------------------------------------------------------
  -- continuity from below

  module _ (W : ℕ → Pred) (bW : ∀ n → Borel (W n)) (sub : ∀ n x → W n x → W (suc n) x) where

    mono′ : ∀ {m n} x → m ℕ.≤′ n → W m x → W n x
    mono′ x ℕ.≤′-refl w = w
    mono′ x (ℕ.≤′-step le) w = sub _ x (mono′ x le w)

    D : ℕ → Pred
    D zero = W zero
    D (suc n) = λ x → W (suc n) x × (W n x → ⊥)

    bD : ∀ n → Borel (D n)
    bD zero = bW zero
    bD (suc n) = inter₂ (bW (suc n)) (compl (bW n))

    D⊆W : ∀ n x → D n x → W n x
    D⊆W zero x w = w
    D⊆W (suc n) x (w , _) = w

    D-dj : Disjoint D
    D-dj x m n a b with ℕₚ.<-cmp m n
    ... | tri≈ _ e _ = e
    ... | tri< lt _ _ = ⊥-elim (clash x m n lt a b)
      where
        clash : ∀ x m n → m ℕ.< n → D m x → D n x → ⊥
        clash x m zero () a b
        clash x m (suc n) lt a (_ , nw) = nw (mono′ x (ℕₚ.≤⇒≤′ (ℕₚ.≤-pred lt)) (D⊆W m x a))
    ... | tri> _ _ gt = ⊥-elim (clash x n m gt b a)
      where
        clash : ∀ x m n → m ℕ.< n → D m x → D n x → ⊥
        clash x m zero () a b
        clash x m (suc n) lt a (_ , nw) = nw (mono′ x (ℕₚ.≤⇒≤′ (ℕₚ.≤-pred lt)) (D⊆W m x a))

    -- every point of a W n lies in a first cell
    W⊆D : ∀ n x → W n x → Σ ℕ (λ m → D m x)
    W⊆D zero x w = zero , w
    W⊆D (suc n) x w with lem (W n x)
    ... | inj₁ p = W⊆D n x p
    ... | inj₂ np = suc n , w , np

    -- μ (W n) is the partial sum of the cells
    μ-W : ∀ n → μ (bW n) ≈ psum (λ i → μ (bD i)) (suc n)
    μ-W zero = sym (+-identityˡ _)
    μ-W (suc n) = begin
      μ (bW (suc n))
        ≈⟨ μ-add (bW n) (bD (suc n)) (bW (suc n)) (λ x w (_ , nw) → nw w) e ⟩
      μ (bW n) + μ (bD (suc n))
        ≈⟨ +-cong (μ-W n) (refl {μ (bD (suc n))}) ⟩
      psum (λ i → μ (bD i)) (suc n) + μ (bD (suc n)) ∎
      where
        e : W (suc n) ≐ (λ x → W n x ⊎ D (suc n) x)
        e x = (λ w → dec x w) , (λ { (inj₁ w) → sub n x w ; (inj₂ (w , _)) → w })
          where dec : ∀ x → W (suc n) x → W n x ⊎ D (suc n) x
                dec x w with lem (W n x)
                ... | inj₁ p = inj₁ p
                ... | inj₂ np = inj₂ (w , np)

    μ-cont : μ (⋃ bW) ≈ ⨆ (λ n → μ (bW n)) (λ n → μ-mono (bW n) (bW (suc n)) (sub n))
    μ-cont = begin
      μ (⋃ bW)
        ≈⟨ μ-part (⋃ bW) bD D-dj e ⟩
      ∑ᶠ (λ i → μ (bD i))
        ≈⟨ ⨆-shift (psum (λ i → μ (bD i))) (psum-inc _) (λ n → psum-inc _ (suc n)) ⟩
      ⨆ (λ n → psum (λ i → μ (bD i)) (suc n)) incP
        ≈⟨ ⨆-cong incP (λ n → μ-mono (bW n) (bW (suc n)) (sub n)) (λ n → sym (μ-W n)) ⟩
      ⨆ (λ n → μ (bW n)) (λ n → μ-mono (bW n) (bW (suc n)) (sub n)) ∎
      where
        incP : Increasing (λ n → psum (λ i → μ (bD i)) (suc n))
        incP n = psum-inc (λ i → μ (bD i)) (suc n)
        e : (λ x → Σ ℕ (λ n → W n x)) ≐ (λ x → Σ ℕ (λ m → D m x))
        e x = (λ { (n , w) → W⊆D n x w }) , (λ { (m , d) → m , D⊆W m x d })

  ----------------------------------------------------------------------------
  -- completing partial simple functions

  module _ (W : ℕ → Pred) (bW : ∀ n → Borel (W n)) (dj : Disjoint W) (r : ℕ → ∣A∣) where
    -- an extra cell for the complement of the union, with value 0
    ccell : ℕ → Pred
    ccell zero = ∁ (λ x → Σ ℕ (λ a → W a x))
    ccell (suc a) = W a

    complete : Sf
    complete = record
      { V = ccell
      ; bV = λ { zero → compl (⋃ bW) ; (suc a) → bW a }
      ; dj = λ { x zero zero _ _ → ≡.refl
               ; x zero (suc n) nu w → ⊥-elim (nu (n , w))
               ; x (suc m) zero w nu → ⊥-elim (nu (m , w))
               ; x (suc m) (suc n) a b → ≡.cong suc (dj x m n a b) }
      ; cov = λ x → case x (lem (Σ ℕ (λ a → W a x)))
      ; ρ = λ { zero → 0# ; (suc a) → r a } }
      where
        case : ∀ x → (Σ ℕ (λ a → W a x)) ⊎ ((Σ ℕ (λ a → W a x)) → ⊥) → Σ ℕ (λ i → ccell i x)
        case x (inj₁ (a , w)) = suc a , w
        case x (inj₂ nu) = zero , nu

    ∫-complete : ∫ complete ≈ ∑ᶠ (λ a → r a * μ (bW a))
    ∫-complete = trans (∑ᶠ-shift (λ i → ρ complete i * μ (bV complete i)))
      (trans (+-cong {ρ complete 0 * μ (bV complete 0)} {0#} {∑ᶠ (λ a → r a * μ (bW a))} {∑ᶠ (λ a → r a * μ (bW a))}
                (zeroˡ (μ (bV complete 0))) (refl {∑ᶠ (λ a → r a * μ (bW a))}))
        (+-identityˡ (∑ᶠ (λ a → r a * μ (bW a)))))
