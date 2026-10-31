{-# OPTIONS --safe --without-K #-}

-- Measurability of lower-real valued functions on Cantor space by thresholds:
--   Meas h  :=  for every rational q, the set {x | q ∈ h x} is Borel.
-- Unlike the inductive class `Fun` (which is bounded by 1), `Meas` is closed under sums,
-- products, minima and countable suprema by direct formulas on cuts, and it applies to functions
-- with values in [0,∞].  Every `Fun` is `Meas` (`Analysis/LevelSets`); the converse for functions
-- bounded by 1 is `Analysis/MeasFun`.
module QBS.Analysis.Meas where

open import Level using (lift; lower)
open import Function.Base using (case_of_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_)

open import QBS.Model.Pairing
open import QBS.Analysis.RationalLemmas
open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; downℕ) renaming (down to downR)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LevelSets using (enumQ; enumQ-surj; module LevelSets)
open Cut
open _⊑_

module Meas (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open LevelSets lem using (Lvl; borel-prop)

  Meas : (R₁ → Cut) → Set₁
  Meas h = ∀ q → Borel (Lvl h q)

  ----------------------------------------------------------------------------
  -- countable quantification over the rationals

  pair-enum : ∀ (P : ℚᵘ → ℚᵘ → Pred) → (∀ ρ σ → Borel (P ρ σ)) →
    Borel (λ c → Σ ℚᵘ (λ ρ → Σ ℚᵘ (λ σ → P ρ σ c)))
  pair-enum P bP = resp e (⋃ (λ k → bP (r k) (s k)))
    where
      r s : ℕ → ℚᵘ
      r k = enumQ (proj₁ (unpair k))
      s k = enumQ (proj₂ (unpair k))
      e : (λ c → Σ ℕ (λ k → P (r k) (s k) c)) ≐ (λ c → Σ ℚᵘ (λ ρ → Σ ℚᵘ (λ σ → P ρ σ c)))
      e c = (λ { (k , p) → r k , s k , p })
          , (λ { (ρ , σ , p) →
              let k₁ , p₁ = enumQ-surj ρ
                  k₂ , p₂ = enumQ-surj σ
                  eq : (r (pair k₁ k₂) , s (pair k₁ k₂)) ≡ (ρ , σ)
                  eq = ≡.trans (≡.cong₂ _,_ (≡.cong (λ u → enumQ (proj₁ u)) (unpair-pair k₁ k₂))
                                            (≡.cong (λ u → enumQ (proj₂ u)) (unpair-pair k₁ k₂)))
                               (≡.cong₂ _,_ p₁ p₂)
              in pair k₁ k₂ , ≡.subst (λ pr → P (proj₁ pr) (proj₂ pr) c) (≡.sym eq) p })

  ex-enum : ∀ (P : ℚᵘ → Pred) → (∀ ρ → Borel (P ρ)) → Borel (λ c → Σ ℚᵘ (λ ρ → P ρ c))
  ex-enum P bP = resp e (⋃ (λ k → bP (enumQ k)))
    where
      e : (λ c → Σ ℕ (λ k → P (enumQ k) c)) ≐ (λ c → Σ ℚᵘ (λ ρ → P ρ c))
      e c = (λ { (k , p) → enumQ k , p })
          , (λ { (ρ , p) → case enumQ-surj ρ of λ { (k , ≡.refl) → k , p } })

  all-enum : ∀ (P : ℚᵘ → Pred) → (∀ ρ → Borel (P ρ)) → Borel (λ c → ∀ ρ → P ρ c)
  all-enum P bP = resp e (⋂ (λ k → bP (enumQ k)))
    where
      e : (λ c → ∀ k → P (enumQ k) c) ≐ (λ c → ∀ ρ → P ρ c)
      e c = (λ h ρ → case enumQ-surj ρ of λ { (k , ≡.refl) → h k }) , (λ h k → h (enumQ k))

  -- a proposition implying a Borel set
  imp-borel : ∀ (P : Set) {B : Pred} → Borel B → Borel (λ c → P → B c)
  imp-borel P {B} bB with lem P
  ... | inj₁ p = resp {B} {λ c → P → B c} (λ c → (λ b _ → b) , (λ f → f p)) bB
  ... | inj₂ np = resp {λ _ → ⊤} {λ c → P → B c} (λ c → (λ _ p → ⊥-elim (np p)) , (λ _ → tt)) ⊤-borel

  ----------------------------------------------------------------------------
  -- closure of Meas

  Meas-ext : ∀ {h h′} → (∀ x → h x ≋ h′ x) → Meas h → Meas h′
  Meas-ext e m q = resp (λ c → ap (proj₁ (e (lift c))) q , ap (proj₂ (e (lift c))) q) (m q)

  -- threshold-measurable functions do not distinguish points that agree everywhere
  Meas-resp : ∀ {h} → Meas h → ∀ {x y} → ≡._≗_ (lower x) (lower y) → h x ≋ h y
  Meas-resp m {x} {y} e = mk⊑ (λ q → proj₁ (borel-≗ (m q) e)) , mk⊑ (λ q → proj₂ (borel-≗ (m q) e))

  Meas-const : ∀ c → Meas (λ _ → c)
  Meas-const c q = borel-prop (mem c q)

  Meas-⊕ : ∀ {h₁ h₂} → Meas h₁ → Meas h₂ → Meas (λ x → h₁ x ⊕ h₂ x)
  Meas-⊕ {h₁} {h₂} b₁ b₂ q =
    pair-enum (λ ρ σ c → Lvl h₁ ρ c × (Lvl h₂ σ c × (q ≤ ρ + σ)))
      (λ ρ σ → inter₂ (b₁ ρ) (inter₂ (b₂ σ) (borel-prop (q ≤ ρ + σ))))

  Meas-⊗ : ∀ {h₁ h₂} → Meas h₁ → Meas h₂ → Meas (λ x → h₁ x ⊗ h₂ x)
  Meas-⊗ {h₁} {h₂} b₁ b₂ q =
    union₂ (borel-prop (q < 0ℚᵘ))
      (pair-enum (λ ρ σ c → (0ℚᵘ < ρ) × ((0ℚᵘ < σ) × (Lvl h₁ ρ c × (Lvl h₂ σ c × (q ≤ ρ * σ)))))
        (λ ρ σ → inter₂ (borel-prop (0ℚᵘ < ρ)) (inter₂ (borel-prop (0ℚᵘ < σ))
                   (inter₂ (b₁ ρ) (inter₂ (b₂ σ) (borel-prop (q ≤ ρ * σ)))))))

  Meas-⊓ : ∀ {h₁ h₂} → Meas h₁ → Meas h₂ → Meas (λ x → h₁ x ⊓ h₂ x)
  Meas-⊓ b₁ b₂ q = inter₂ (b₁ q) (b₂ q)

  Meas-⨆ : ∀ {h} (hs : ℕ → R₁ → Cut) → (∀ n → Meas (hs n)) →
    (∀ x → h x ≋ unionC (λ n → hs n x)) → Meas h
  Meas-⨆ hs ms e = Meas-ext (λ x → ≋-sym (e x)) (λ q → ⋃ (λ n → ms n q))

  -- precomposition with a measurable map
  Meas-pre : ∀ {h f} → Meas h → Measurable (downR f) → Meas (λ x → h (f x))
  Meas-pre {h} {f} m mf q = preimage mf (m q)

  -- gluing along a measurable countable partition
  Meas-glue : ∀ {j : R₁ → ℕ} {hs : ℕ → R₁ → Cut} → Partition (downℕ j) → (∀ k → Meas (hs k)) →
    Meas (λ x → hs (j x) x)
  Meas-glue {j} {hs} pj ms q = resp e (⋃ (λ k → inter₂ (pj k) (ms k q)))
    where
      e : (λ c → Σ ℕ (λ k → (j (lift c) ≡ k) × Lvl (hs k) q c)) ≐ Lvl (λ x → hs (j x) x) q
      e c = (λ { (k , p , l) → ≡.subst (λ k′ → mem (hs k′ (lift c)) q) (≡.sym p) l })
          , (λ l → j (lift c) , ≡.refl , l)
