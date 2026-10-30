{-# OPTIONS --safe --without-K #-}

-- Simple functions on Cantor space (countable Borel partitions with values in A) and their
-- integral against the fair-coin measure; monotone and additive under common refinement.  This
-- is the base of the Lebesgue-style integral of the measurable functions.
module QBS.Analysis.CoinSimple where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open ≡ using (_≡_)

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda using (_∩ᵖ_; ∁; ⊤ᵖ; ⊥ᵖ)
open import QBS.Model.Pairing
open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinFacts

module Simple (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (B : BM.BorelMeasure lem) where
  open Facts lem B public using (A; μ-null; μ-part; μ-add; μ-mono)
  open OmegaSemiring A renaming (Carrier to ∣A∣; zero to zero-sr)
  open Series A
  open SetoidReasoning setoid
  open BM.BorelMeasure B using (μ; μ-resp; μ-⋃; μ-⊤; μ-⊥)

  -- a countable Borel partition of the space with values in A
  record Sf : Set₁ where
    field
      V : ℕ → Pred
      bV : ∀ i → Borel (V i)
      dj : Disjoint V
      cov : ∀ x → Σ ℕ (λ i → V i x)
      ρ : ℕ → ∣A∣
  open Sf

  ∫ : Sf → ∣A∣
  ∫ s = ∑ᶠ (λ i → ρ s i * μ (bV s i))

  -- the measure of the cell V i ∩ W j
  cell : Sf → Sf → ℕ → ℕ → ∣A∣
  cell s t i j = μ (inter₂ (bV s i) (bV t j))

  refine₁ : ∀ s t i → μ (bV s i) ≈ ∑ᶠ (λ j → cell s t i j)
  refine₁ s t i = μ-part (bV s i) (λ j → inter₂ (bV s i) (bV t j))
    (λ x j k (_ , a) (_ , b) → dj t x j k a b)
    (λ x → (λ v → let j , w = cov t x in j , v , w) , (λ { (j , v , w) → v }))

  refine₂ : ∀ s t j → μ (bV t j) ≈ ∑ᶠ (λ i → cell s t i j)
  refine₂ s t j = μ-part (bV t j) (λ i → inter₂ (bV s i) (bV t j))
    (λ x i k (a , _) (b , _) → dj s x i k a b)
    (λ x → (λ w → let i , v = cov s x in i , v , w) , (λ { (i , v , w) → w }))

  -- each cell contributes monotonically: on a non-null cell the values are ordered, on a null cell both sides vanish
  cell-mono : ∀ s t → (∀ i j x → V s i x → V t j x → ρ s i ≤ ρ t j) → ∀ i j →
    ρ s i * cell s t i j ≤ ρ t j * cell s t i j
  cell-mono s t le i j with lem (Σ Cantor (λ x → V s i x × V t j x))
  ... | inj₁ (x , a , b) = ≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (*-mono (cell s t i j) (le i j x a b)) (≤-reflexive (*-comm _ _)))
  ... | inj₂ none = ≤-trans (≤-reflexive (trans (*-cong refl z) (zeroʳ _))) (≤-trans 0-least (≤-reflexive (sym (trans (*-cong refl z) (zeroʳ _)))))
    where z : cell s t i j ≈ 0#
          z = μ-null (inter₂ (bV s i) (bV t j)) (λ x (a , b) → none (x , a , b))

  -- monotonicity of the integral
  ∫-mono : ∀ s t → (∀ i j x → V s i x → V t j x → ρ s i ≤ ρ t j) → ∫ s ≤ ∫ t
  ∫-mono s t le = ≤-trans (≤-reflexive step₁) (≤-trans mid (≤-reflexive (sym step₃)))
    where
      step₁ : ∫ s ≈ ∑ᶠ (λ i → ∑ᶠ (λ j → ρ s i * cell s t i j))
      step₁ = ∑ᶠ-cong (λ i → trans (*-cong refl (refine₁ s t i)) (∑ᶠ-scale (ρ s i) (λ j → cell s t i j)))
      mid : ∑ᶠ (λ i → ∑ᶠ (λ j → ρ s i * cell s t i j)) ≤ ∑ᶠ (λ j → ∑ᶠ (λ i → ρ t j * cell s t i j))
      mid = ≤-trans (∑ᶠ-mono (λ i → ∑ᶠ-mono (λ j → cell-mono s t le i j))) (≤-reflexive (∑ᶠ-swap (λ i j → ρ t j * cell s t i j)))
      step₃ : ∫ t ≈ ∑ᶠ (λ j → ∑ᶠ (λ i → ρ t j * cell s t i j))
      step₃ = ∑ᶠ-cong (λ j → trans (*-cong refl (refine₂ s t j)) (∑ᶠ-scale (ρ t j) (λ i → cell s t i j)))

  -- common refinement: the sum of two simple functions
  sadd : Sf → Sf → Sf
  sadd s t = record
    { V = λ k → V s (proj₁ (unpair k)) ∩ᵖ′ V t (proj₂ (unpair k))
    ; bV = λ k → inter₂ (bV s (proj₁ (unpair k))) (bV t (proj₂ (unpair k)))
    ; dj = λ x k k′ (a , b) (a′ , b′) →
        ≡.trans (≡.sym (pair-unpair k))
          (≡.trans (≡.cong pair′ (≡.cong₂ _,_ (dj s x _ _ a a′) (dj t x _ _ b b′))) (pair-unpair k′))
    ; cov = λ x → let i , a = cov s x
                      j , b = cov t x
                  in pair i j , ≡.subst (λ p → V s (proj₁ p) x × V t (proj₂ p) x) (≡.sym (unpair-pair i j)) (a , b)
    ; ρ = λ k → ρ s (proj₁ (unpair k)) + ρ t (proj₂ (unpair k))
    }
    where
      _∩ᵖ′_ : Pred → Pred → Pred
      U ∩ᵖ′ W = λ x → U x × W x

  ∫-sadd : ∀ s t → ∫ (sadd s t) ≈ ∫ s + ∫ t
  ∫-sadd s t = begin
    ∑ᶠ (λ k → a (proj₁ (unpair k)) (proj₂ (unpair k)))
      ≈⟨ sym (∑ᶠ-pair a) ⟩
    ∑ᶠ (λ n → ∑ᶠ (a n))
      ≈⟨ ∑ᶠ-cong (λ n → ∑ᶠ-cong (λ m → distribʳ (cell s t n m) (ρ s n) (ρ t m))) ⟩
    ∑ᶠ (λ n → ∑ᶠ (λ m → ρ s n * cell s t n m + ρ t m * cell s t n m))
      ≈⟨ ∑ᶠ-cong (λ n → ∑ᶠ-+ (λ m → ρ s n * cell s t n m) (λ m → ρ t m * cell s t n m)) ⟩
    ∑ᶠ (λ n → ∑ᶠ (λ m → ρ s n * cell s t n m) + ∑ᶠ (λ m → ρ t m * cell s t n m))
      ≈⟨ ∑ᶠ-+ (λ n → ∑ᶠ (λ m → ρ s n * cell s t n m)) (λ n → ∑ᶠ (λ m → ρ t m * cell s t n m)) ⟩
    ∑ᶠ (λ n → ∑ᶠ (λ m → ρ s n * cell s t n m)) + ∑ᶠ (λ n → ∑ᶠ (λ m → ρ t m * cell s t n m))
      ≈⟨ +-cong (sym (∑ᶠ-cong (λ n → trans (*-cong refl (refine₁ s t n)) (∑ᶠ-scale (ρ s n) (λ m → cell s t n m)))))
                (trans (∑ᶠ-swap (λ n m → ρ t m * cell s t n m))
                  (sym (∑ᶠ-cong (λ m → trans (*-cong refl (refine₂ s t m)) (∑ᶠ-scale (ρ t m) (λ n → cell s t n m)))))) ⟩
    ∫ s + ∫ t ∎
    where
      a : ℕ → ℕ → ∣A∣
      a n m = (ρ s n + ρ t m) * cell s t n m

  -- the constant simple function
  sconst : ∣A∣ → Sf
  sconst c = record
    { V = λ { zero → ⊤ᵖ ; (suc _) → ⊥ᵖ }
    ; bV = λ { zero → ⊤-borel ; (suc _) → ⊥-borel }
    ; dj = λ { x zero zero _ _ → ≡.refl ; x zero (suc n) _ () ; x (suc m) n () _ }
    ; cov = λ x → zero , tt
    ; ρ = λ _ → c }

  ∫-sconst : ∀ c → ∫ (sconst c) ≈ c
  ∫-sconst c = trans (∑ᶠ-single {λ i → c * μ (bV (sconst c) i)} 0
      (λ { zero ne → ⊥-elim (ne ≡.refl) ; (suc n) _ → trans (*-cong refl μ-⊥) (zeroʳ c) }))
    (trans (*-cong refl μ-⊤) (*-identityʳ c))

  -- scaling the values
  sscale : ∣A∣ → Sf → Sf
  sscale c s = record { V = V s ; bV = bV s ; dj = dj s ; cov = cov s ; ρ = λ i → c * ρ s i }

  ∫-sscale : ∀ c s → ∫ (sscale c s) ≈ c * ∫ s
  ∫-sscale c s = trans (∑ᶠ-cong (λ i → *-assoc c (ρ s i) (μ (bV s i)))) (sym (∑ᶠ-scale c (λ i → ρ s i * μ (bV s i))))
