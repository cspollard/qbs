{-# OPTIONS --safe --without-K #-}

-- The Boolean semiring ({false, true}, ∨, ∧) as a normalisable complete semiring: sums are
-- existential quantifiers (decided classically).  Weights in it make the discrete model
-- possibilistic: a "measure" is a set of possible outcomes.  A degenerate but non-vacuous
-- instance of `NormalizableSemiring` (idempotent, so not an instance for `Analysis/Omega`).
module QBS.Model.BoolSemiring where

open import Level using (Level; Lift; lift; lower)
open import Function.Base using (_∘_)
open import Function.Bundles using (Inverse; _↔_)
open import Relation.Binary.PropositionalEquality.Core using (subst)
open import Algebra.Bundles using (CommutativeSemiring)
open import Data.Bool.Base using (Bool; true; false; _∨_; _∧_)
import Data.Bool.Properties as B
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

open import QBS.Model.Semiring

module _ (ℓ : Level) (lem : ∀ (P : Set ℓ) → P ⊎ (P → ⊥ {ℓ})) where
  private
    C = Lift ℓ Bool
    module S = CommutativeSemiring B.∨-∧-commutativeSemiring
    lc : ∀ {x y : Bool} → x ≡ y → lift {ℓ = ℓ} x ≡ lift y
    lc = cong lift

    _⊕_ _⊗_ : C → C → C
    a ⊕ b = lift (lower a ∨ lower b)
    a ⊗ b = lift (lower a ∧ lower b)

  boolCommSemiring : CommutativeSemiring ℓ ℓ
  boolCommSemiring = record
    { Carrier = C ; _≈_ = _≡_ ; _+_ = _⊕_ ; _*_ = _⊗_ ; 0# = lift false ; 1# = lift true
    ; isCommutativeSemiring = record
        { isSemiring = record
            { isSemiringWithoutAnnihilatingZero = record
                { +-isCommutativeMonoid = record
                    { isMonoid = record
                        { isSemigroup = record
                            { isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _⊕_ }
                            ; assoc = λ a b c → lc (S.+-assoc (lower a) (lower b) (lower c)) }
                        ; identity = (λ a → lc (S.+-identityˡ (lower a))) , (λ a → lc (S.+-identityʳ (lower a))) }
                    ; comm = λ a b → lc (S.+-comm (lower a) (lower b)) }
                ; *-cong = cong₂ _⊗_
                ; *-assoc = λ a b c → lc (S.*-assoc (lower a) (lower b) (lower c))
                ; *-identity = (λ a → lc (S.*-identityˡ (lower a))) , (λ a → lc (S.*-identityʳ (lower a)))
                ; distrib = (λ a b c → lc (S.distribˡ (lower a) (lower b) (lower c)))
                          , (λ a b c → lc (S.distribʳ (lower a) (lower b) (lower c))) }
            ; zero = (λ a → lc (S.zeroˡ (lower a))) , (λ a → lc (S.zeroʳ (lower a))) }
        ; *-comm = λ a b → lc (S.*-comm (lower a) (lower b)) }
    }

  private
    exfalso : ∀ {a} {A : Set a} → ⊥ {ℓ} → A
    exfalso ()

    -- classical truth value of a proposition
    dec : (P : Set ℓ) → Bool
    dec P with lem P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    dec-true : ∀ {P} → P → dec P ≡ true
    dec-true {P} p with lem P
    ... | inj₁ _ = refl
    ... | inj₂ np = exfalso (np p)

    dec-false : ∀ {P} → (P → ⊥ {ℓ}) → dec P ≡ false
    dec-false {P} np with lem P
    ... | inj₁ p = exfalso (np p)
    ... | inj₂ _ = refl

    from-true : ∀ {P} → dec P ≡ true → P
    from-true {P} e with lem P
    ... | inj₁ p = p

    dec-iff : ∀ {P Q : Set ℓ} → (P → Q) → (Q → P) → dec P ≡ dec Q
    dec-iff {P} {Q} f g with lem P | lem Q
    ... | inj₁ _ | inj₁ _ = refl
    ... | inj₂ _ | inj₂ _ = refl
    ... | inj₁ p | inj₂ nq = exfalso (nq (f p))
    ... | inj₂ np | inj₁ q = exfalso (np (g q))

    dec-or : ∀ {P Q R : Set ℓ} → (P → Q ⊎ R) → (Q ⊎ R → P) → dec P ≡ dec Q ∨ dec R
    dec-or {P} {Q} {R} f g with lem P | lem Q | lem R
    ... | inj₁ _ | inj₁ _ | _ = refl
    ... | inj₁ _ | inj₂ _ | inj₁ _ = refl
    ... | inj₁ p | inj₂ nq | inj₂ nr with f p
    ...   | inj₁ q = exfalso (nq q)
    ...   | inj₂ r = exfalso (nr r)
    dec-or f g | inj₂ np | inj₁ q | _ = exfalso (np (g (inj₁ q)))
    dec-or f g | inj₂ np | inj₂ _ | inj₁ r = exfalso (np (g (inj₂ r)))
    dec-or f g | inj₂ _ | inj₂ _ | inj₂ _ = refl

    absurd : ∀ {A : Set ℓ} → false ≡ true → A
    absurd ()

    dec-bool : ∀ {P : Set ℓ} {b} → (P → b ≡ true) → (b ≡ true → P) → dec P ≡ b
    dec-bool {b = true} f g = dec-true (g refl)
    dec-bool {b = false} f g = dec-false (λ p → absurd (f p))

  boolComplete : CompleteSemiring ℓ
  boolComplete = record
    { commutativeSemiring = boolCommSemiring
    ; ∑ = λ {I} f → lift (dec (Σ I (λ i → lower (f i) ≡ true)))
    ; ∑-cong = λ {I} {f} {g} e → lc (dec-iff
        (λ (i , p) → i , trans (sym (cong lower (e i))) p)
        (λ (i , p) → i , trans (cong lower (e i)) p))
    ; ∑-empty = λ f → lc (dec-false (λ (i , _) → i))
    ; ∑-unit = λ f → lc (dec-bool (λ (_ , p) → p) (λ p → tt , p))
    ; ∑-⊎ = λ {I} {J} f → lc (dec-or
        (λ { (inj₁ i , p) → inj₁ (i , p) ; (inj₂ j , p) → inj₂ (j , p) })
        (λ { (inj₁ (i , p)) → inj₁ i , p ; (inj₂ (j , p)) → inj₂ j , p }))
    ; ∑-Σ = λ {I} {J} f → lc (dec-iff
        (λ ((i , j) , p) → i , dec-true (j , p))
        (λ (i , p) → let (j , q) = from-true p in (i , j) , q))
    ; ∑-reindex = λ {I} {J} e f → lc (dec-iff
        (λ (i , p) → Inverse.to e i , p)
        (λ (j , p) → Inverse.from e j , subst′ e f j p))
    ; ∑-distribˡ = λ { (lift true) f → refl
                     ; (lift false) f → lc (sym (dec-false (λ (i , p) → absurd p))) }
    }
    where
      subst′ : ∀ {I J : Set ℓ} (e : I ↔ J) (f : J → C) j → lower (f j) ≡ true →
        lower (f (Inverse.to e (Inverse.from e j))) ≡ true
      subst′ e f j p = trans (cong (λ u → lower (f u)) (Inverse.inverseˡ e refl)) p

  -- Boolean weights, deciding invertibility classically
  boolNormalizable : NormalizableSemiring ℓ
  boolNormalizable = record
    { complete = boolComplete
    ; invertible? = λ { (lift true) → inj₁ (lift true , refl)
                      ; (lift false) → inj₂ (λ n e → absurd (cong lower e)) }
    ; nontrivial = λ e → absurd (cong lower e)
    }
