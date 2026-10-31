{-# OPTIONS --safe --without-K #-}

-- Cantor space with its Borel σ-algebra is a random source: quasi-Borel spaces over it are
-- quasi-Borel spaces in the sense of Heunen–Kammar–Staton–Yang (Def. 7; by their remark after
-- Def. 11 any uncountable standard Borel space serves as the sample space).
module QBS.Borel.Source where

open import Level using (Level; zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Nat.Properties using (_≟_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

open import QBS.Core using (RandomSource)
open import QBS.Model.Pairing
open import QBS.Borel.Core

-- the sample space: Cantor space, lifted so that the σ-algebra (which lives in Set₁) is
-- a predicate in the same universe as R
R₁ : Set₁
R₁ = Lift (suc zero) Cantor

down : (R₁ → R₁) → Cantor → Cantor
down f x = lower (f (lift x))

downℕ : (R₁ → ℕ) → Cantor → ℕ
downℕ i x = i (lift x)

private
  -- a constant proposition about ℕ is Borel
  borel-eq : ∀ (a k : ℕ) → Borel (λ (_ : Cantor) → a ≡ k)
  borel-eq a k with a ≟ k
  ... | yes p = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
  ... | no ¬p = resp (λ x → (λ ()) , (λ e → ¬p e)) ⊥-borel

  idx-glue-borel : ∀ (j : Cantor → ℕ) (i : ℕ → Cantor → ℕ) →
    Partition j → (∀ n → Partition (i n)) → Partition (λ x → pair (j x) (i (j x) x))
  idx-glue-borel j i pj pi k = resp e (inter₂ (pj a) (pi a b))
    where
      a = proj₁ (unpair k)
      b = proj₂ (unpair k)
      e : (λ x → (j x ≡ a) × (i a x ≡ b)) ≐ (λ x → pair (j x) (i (j x) x) ≡ k)
      e x = fwd , bwd
        where
          fwd : (j x ≡ a) × (i a x ≡ b) → pair (j x) (i (j x) x) ≡ k
          fwd (p , q) = trans (cong₂ pair p (trans (cong (λ t → i t x) p) q)) (pair-unpair k)
          bwd : pair (j x) (i (j x) x) ≡ k → (j x ≡ a) × (i a x ≡ b)
          bwd h = sym (cong proj₁ e₁) , trans (cong (λ t → i t x) (cong proj₁ e₁)) (sym (cong proj₂ e₁))
            where e₁ : unpair k ≡ (j x , i (j x) x)
                  e₁ = trans (cong unpair (sym h)) (unpair-pair (j x) (i (j x) x))

cantorSource : RandomSource (suc zero)
cantorSource = record
  { measurable = record
    { Rˢ = setoid R₁
    ; Meas = λ f → Measurable (down f)
    ; meas-id = measurable-id
    ; meas-∘ = λ mf mg → measurable-∘ mg mf
    ; meas-resp = λ _ e → cong _ e
    ; meas-ext = λ e mf → measurable-ext (λ x → cong lower (e (lift x))) mf
    ; meas-const = λ r → measurable-const (lower r)
    }
  ; partitions = record
    { Idx = λ i → Partition (downℕ i)
    ; idx-resp = λ _ e → cong _ e
    ; meas-glue = λ {j} {f} pj mf → measurable-glue {downℕ j} {λ k → down (f k)} pj mf
    ; idx-const = λ n k → borel-eq n k
    ; idx-pre = λ {i} {f} pi mf k → preimage mf (pi k)
    }
  ; pairing = record { pair = pair ; unpair = unpair ; unpair-pair = unpair-pair }
  ; idx-glue = λ {j} {i} pj pi → idx-glue-borel (downℕ j) (λ n → downℕ (i n)) pj pi
  }
