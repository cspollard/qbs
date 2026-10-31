{-# OPTIONS --safe --without-K #-}

-- The extended natural numbers ℕ∞ = ℕ ∪ {∞} as a commutative semiring (0 · ∞ = 0).
module QBS.Analysis.ExtNat where

import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂)

data ℕ∞ : Set where
  fin : ℕ → ℕ∞
  ∞ : ℕ∞

infixl 6 _+_
infixl 7 _*_

_+_ : ℕ∞ → ℕ∞ → ℕ∞
fin a + fin b = fin (a ℕ.+ b)
fin a + ∞ = ∞
∞ + y = ∞

_*_ : ℕ∞ → ℕ∞ → ℕ∞
fin a * fin b = fin (a ℕ.* b)
fin zero * ∞ = fin zero
fin (suc a) * ∞ = ∞
∞ * fin zero = fin zero
∞ * fin (suc b) = ∞
∞ * ∞ = ∞

+-comm : ∀ x y → x + y ≡ y + x
+-comm (fin a) (fin b) = cong fin (ℕ.+-comm a b)
+-comm (fin a) ∞ = refl
+-comm ∞ (fin b) = refl
+-comm ∞ ∞ = refl

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc (fin a) (fin b) (fin c) = cong fin (ℕ.+-assoc a b c)
+-assoc (fin a) (fin b) ∞ = refl
+-assoc (fin a) ∞ z = refl
+-assoc ∞ y z = refl

+-identityˡ : ∀ x → fin 0 + x ≡ x
+-identityˡ (fin a) = refl
+-identityˡ ∞ = refl

*-comm : ∀ x y → x * y ≡ y * x
*-comm (fin a) (fin b) = cong fin (ℕ.*-comm a b)
*-comm (fin zero) ∞ = refl
*-comm (fin (suc a)) ∞ = refl
*-comm ∞ (fin zero) = refl
*-comm ∞ (fin (suc b)) = refl
*-comm ∞ ∞ = refl

*-identityˡ : ∀ x → fin 1 * x ≡ x
*-identityˡ (fin a) = cong fin (ℕ.+-identityʳ a)
*-identityˡ ∞ = refl

zeroˡ : ∀ x → fin 0 * x ≡ fin 0
zeroˡ (fin a) = refl
zeroˡ ∞ = refl

zeroʳ : ∀ x → x * fin 0 ≡ fin 0
zeroʳ x = trans (*-comm x (fin 0)) (zeroˡ x)

*-assoc : ∀ x y z → (x * y) * z ≡ x * (y * z)
*-assoc (fin a) (fin b) (fin c) = cong fin (ℕ.*-assoc a b c)
*-assoc (fin zero) (fin zero) ∞ = refl
*-assoc (fin zero) (fin (suc b)) ∞ = refl
*-assoc (fin (suc a)) (fin zero) ∞ = trans (cong (λ k → fin k * ∞) (ℕ.*-zeroʳ a)) (cong fin (sym (ℕ.*-zeroʳ a)))
*-assoc (fin (suc a)) (fin (suc b)) ∞ = refl
*-assoc (fin zero) ∞ (fin zero) = refl
*-assoc (fin zero) ∞ (fin (suc c)) = refl
*-assoc (fin (suc a)) ∞ (fin zero) = cong fin (sym (ℕ.*-zeroʳ a))
*-assoc (fin (suc a)) ∞ (fin (suc c)) = refl
*-assoc (fin zero) ∞ ∞ = refl
*-assoc (fin (suc a)) ∞ ∞ = refl
*-assoc ∞ (fin zero) (fin c) = refl
*-assoc ∞ (fin (suc b)) (fin zero) = cong (λ k → ∞ * fin k) (sym (ℕ.*-zeroʳ b))
*-assoc ∞ (fin (suc b)) (fin (suc c)) = refl
*-assoc ∞ (fin zero) ∞ = refl
*-assoc ∞ (fin (suc b)) ∞ = refl
*-assoc ∞ ∞ (fin zero) = refl
*-assoc ∞ ∞ (fin (suc c)) = refl
*-assoc ∞ ∞ ∞ = refl

distribʳ : ∀ x y z → (y + z) * x ≡ y * x + z * x
distribʳ (fin zero) y z = trans (zeroʳ (y + z)) (sym (cong₂ _+_ (zeroʳ y) (zeroʳ z)))
distribʳ (fin (suc k)) (fin b) (fin c) = cong fin (ℕ.*-distribʳ-+ (suc k) b c)
distribʳ (fin (suc k)) (fin b) ∞ = refl
distribʳ (fin (suc k)) ∞ z = refl
distribʳ ∞ (fin zero) (fin zero) = refl
distribʳ ∞ (fin zero) (fin (suc c)) = refl
distribʳ ∞ (fin (suc b)) (fin zero) = refl
distribʳ ∞ (fin (suc b)) (fin (suc c)) = refl
distribʳ ∞ (fin zero) ∞ = refl
distribʳ ∞ (fin (suc b)) ∞ = refl
distribʳ ∞ ∞ z = refl

----------------------------------------------------------------------------
-- the order, as an inductive relation

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (subst)
open import QBS.Classical using (LEM₀)

infix 4 _⊑_
data _⊑_ : ℕ∞ → ℕ∞ → Set where
  fin⊑fin : ∀ {a b} → a ℕ.≤ b → fin a ⊑ fin b
  ⊑∞ : ∀ {x} → x ⊑ ∞

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl {fin a} = fin⊑fin ℕ.≤-refl
⊑-refl {∞} = ⊑∞

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans (fin⊑fin p) (fin⊑fin q) = fin⊑fin (ℕ.≤-trans p q)
⊑-trans _ ⊑∞ = ⊑∞

⊑-antisym : ∀ {x y} → x ⊑ y → y ⊑ x → x ≡ y
⊑-antisym (fin⊑fin p) (fin⊑fin q) = cong fin (ℕ.≤-antisym p q)
⊑-antisym ⊑∞ ⊑∞ = refl

⊑-reflexive : ∀ {x y} → x ≡ y → x ⊑ y
⊑-reflexive refl = ⊑-refl

0-⊑ : ∀ {x} → fin 0 ⊑ x
0-⊑ {fin b} = fin⊑fin ℕ.z≤n
0-⊑ {∞} = ⊑∞

+∞ : ∀ x → x + ∞ ≡ ∞
+∞ (fin a) = refl
+∞ ∞ = refl

x⊑x+y : ∀ x y → x ⊑ x + y
x⊑x+y (fin a) (fin b) = fin⊑fin (ℕ.m≤m+n a b)
x⊑x+y (fin a) ∞ = ⊑∞
x⊑x+y ∞ y = ⊑∞

x⊑y+x : ∀ x y → x ⊑ y + x
x⊑y+x x y = subst (x ⊑_) (+-comm x y) (x⊑x+y x y)

⊑⇒≤ : ∀ {x y} → x ⊑ y → Σ ℕ∞ (λ d → x + d ≡ y)
⊑⇒≤ {fin a} {fin b} (fin⊑fin p) = fin (b ℕ.∸ a) , cong fin (ℕ.m+[n∸m]≡n p)
⊑⇒≤ {x} ⊑∞ = ∞ , +∞ x

≤⇒⊑ : ∀ {x y} → Σ ℕ∞ (λ d → x + d ≡ y) → x ⊑ y
≤⇒⊑ {x} (d , p) = subst (x ⊑_) p (x⊑x+y x d)

+-mono⊑ : ∀ a {x y} → x ⊑ y → a + x ⊑ a + y
+-mono⊑ (fin a) (fin⊑fin p) = fin⊑fin (ℕ.+-monoʳ-≤ a p)
+-mono⊑ (fin a) {x} ⊑∞ = subst (fin a + x ⊑_) (sym (+∞ (fin a))) ⊑∞
+-mono⊑ ∞ _ = ⊑∞

*-mono⊑ : ∀ a {x y} → x ⊑ y → a * x ⊑ a * y
*-mono⊑ (fin zero) {x} {y} p = subst (_⊑ fin zero * y) (sym (zeroˡ x)) (subst (fin 0 ⊑_) (sym (zeroˡ y)) ⊑-refl)
*-mono⊑ (fin (suc k)) (fin⊑fin p) = fin⊑fin (ℕ.*-monoʳ-≤ (suc k) p)
*-mono⊑ (fin (suc k)) ⊑∞ = ⊑∞
*-mono⊑ ∞ {fin zero} p = 0-⊑
*-mono⊑ ∞ {fin (suc m)} (fin⊑fin {b = zero} ())
*-mono⊑ ∞ {fin (suc m)} (fin⊑fin {b = suc b} p) = ⊑∞
*-mono⊑ ∞ {fin (suc m)} ⊑∞ = ⊑∞
*-mono⊑ ∞ {∞} ⊑∞ = ⊑∞

-- x ⊑ a * x for a ≥ 1
x⊑suc*x : ∀ k x → x ⊑ fin (suc k) * x
x⊑suc*x k (fin m) = fin⊑fin (ℕ.m≤m+n m (k ℕ.* m))
x⊑suc*x k ∞ = ⊑∞

⊑-pred-not : ∀ {j x} → (fin (suc j) ⊑ x → ⊥) → x ⊑ fin j
⊑-pred-not {j} {fin k} h = fin⊑fin (ℕ.<⇒≤pred (ℕ.≰⇒> (λ p → h (fin⊑fin p))))
⊑-pred-not {j} {∞} h = ⊥-elim (h ⊑∞)

cancel : ∀ {a x y} → a ⊑ fin 1 → a + x ≡ a + y → x ≡ y
cancel {fin zero} _ e = trans (sym (+-identityˡ _)) (trans e (+-identityˡ _))
cancel {fin (suc zero)} {fin x} {fin y} _ e = cong fin (ℕ.+-cancelˡ-≡ 1 x y (fin-inj e))
  where fin-inj : ∀ {m n} → fin m ≡ fin n → m ≡ n
        fin-inj refl = refl
cancel {fin (suc zero)} {fin x} {∞} _ ()
cancel {fin (suc zero)} {∞} {fin y} _ ()
cancel {fin (suc zero)} {∞} {∞} _ _ = refl
cancel {fin (suc (suc a))} (fin⊑fin (ℕ.s≤s ()))
cancel {∞} ()

module Sups (lem : LEM₀) where

  Inc : (ℕ → ℕ∞) → Set
  Inc c = ∀ n → c n ⊑ c (suc n)

  data Sup (c : ℕ → ℕ∞) : ℕ∞ → Set where
    attained : ∀ n₀ → (∀ n → c n ⊑ c n₀) → Sup c (c n₀)
    unbounded : (∀ j → Σ ℕ (λ n → fin j ⊑ c n)) → Sup c ∞

  Sup-ub : ∀ {c s} → Sup c s → ∀ n → c n ⊑ s
  Sup-ub (attained n₀ h) = h
  Sup-ub (unbounded _) _ = ⊑∞

  Sup-lub : ∀ {c s b} → Sup c s → (∀ n → c n ⊑ b) → s ⊑ b
  Sup-lub (attained n₀ h) le = le n₀
  Sup-lub {b = ∞} (unbounded u) le = ⊑∞
  Sup-lub {c} {b = fin B} (unbounded u) le with u (suc B)
  ... | n , p with ⊑-trans p (le n)
  ... | fin⊑fin q = ⊥-elim (ℕ.<-irrefl refl q)

  Sup-unique : ∀ {c s t} → Sup c s → Sup c t → s ≡ t
  Sup-unique S T = ⊑-antisym (Sup-lub S (Sup-ub T)) (Sup-lub T (Sup-ub S))

  -- classically, every increasing sequence has a supremum
  sup-exists : ∀ c → Inc c → Σ ℕ∞ (Sup c)
  sup-exists c inc with lem (Σ ℕ (λ n₀ → ∀ n → c n ⊑ c n₀))
  ... | inj₁ (n₀ , h) = c n₀ , attained n₀ h
  ... | inj₂ no = ∞ , unbounded go
    where
      go : ∀ j → Σ ℕ (λ n → fin j ⊑ c n)
      go zero = 0 , 0-⊑
      go (suc j) with go j
      ... | n , p with lem (Σ ℕ (λ n′ → fin (suc j) ⊑ c n′))
      ... | inj₁ yes = yes
      ... | inj₂ none = ⊥-elim (no (n , λ n′ → ⊑-trans (⊑-pred-not (λ q → none (n′ , q))) p))

  Sup-+ : ∀ a {c s} → Sup c s → Sup (λ n → a + c n) (a + s)
  Sup-+ a (attained n₀ h) = attained n₀ (λ n → +-mono⊑ a (h n))
  Sup-+ a (unbounded u) = subst (Sup _) (sym (+∞ a))
    (unbounded (λ j → let (n , p) = u j in n , ⊑-trans p (x⊑y+x _ a)))

  Sup-* : ∀ a {c s} → Sup c s → Sup (λ n → a * c n) (a * s)
  Sup-* a (attained n₀ h) = attained n₀ (λ n → *-mono⊑ a (h n))
  Sup-* (fin zero) {c} (unbounded u) =
    subst (Sup _) (sym (zeroˡ ∞)) (subst (Sup _) (zeroˡ (c 0)) (attained 0 (λ n →
      ⊑-reflexive (trans (zeroˡ (c n)) (sym (zeroˡ (c 0)))))))
  Sup-* (fin (suc k)) {c} (unbounded u) =
    unbounded (λ j → let (n , p) = u j in n , ⊑-trans p (x⊑suc*x k (c n)))
  Sup-* ∞ {c} (unbounded u) = unbounded (λ j → let (n , p) = u (suc j) in n , big j (c n) p)
    where
      big : ∀ j x → fin (suc j) ⊑ x → fin j ⊑ ∞ * x
      big j (fin zero) (fin⊑fin ())
      big j (fin (suc m)) _ = ⊑∞
      big j ∞ _ = ⊑∞

----------------------------------------------------------------------------
-- the instance

open import Level using (Level; Lift; lift; lower)
open import Algebra.Bundles using (CommutativeSemiring)
open import Algebra.Structures {A = ℕ∞} _≡_ using ()
import Algebra.Structures as AS
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import QBS.Analysis.Omega

module Instance (ℓ : Level) (lem : LEM₀) where
  private
    C = Lift ℓ ℕ∞
    _⊕_ _⊗_ : C → C → C
    a ⊕ b = lift (lower a + lower b)
    a ⊗ b = lift (lower a * lower b)
    o z : C
    o = lift (fin 1)
    z = lift (fin 0)

    lc : ∀ {x y : ℕ∞} → x ≡ y → lift {ℓ = ℓ} x ≡ lift y
    lc = cong lift

  open Sups lem

  commSemiring : CommutativeSemiring ℓ ℓ
  commSemiring = record
    { Carrier = C ; _≈_ = _≡_ ; _+_ = _⊕_ ; _*_ = _⊗_ ; 0# = z ; 1# = o
    ; isCommutativeSemiring = record
        { isSemiring = record
            { isSemiringWithoutAnnihilatingZero = record
                { +-isCommutativeMonoid = record
                    { isMonoid = record
                        { isSemigroup = record
                            { isMagma = record
                                { isEquivalence = isEquivalence
                                ; ∙-cong = cong₂ _⊕_ }
                            ; assoc = λ a b c → lc (+-assoc (lower a) (lower b) (lower c)) }
                        ; identity = (λ a → lc (+-identityˡ (lower a)))
                                   , (λ a → lc (trans (+-comm (lower a) (fin 0)) (+-identityˡ (lower a)))) }
                    ; comm = λ a b → lc (+-comm (lower a) (lower b)) }
                ; *-cong = cong₂ _⊗_
                ; *-assoc = λ a b c → lc (*-assoc (lower a) (lower b) (lower c))
                ; *-identity = (λ a → lc (*-identityˡ (lower a)))
                             , (λ a → lc (trans (*-comm (lower a) (fin 1)) (*-identityˡ (lower a))))
                ; distrib = (λ a b c → lc (trans (*-comm (lower a) (lower b + lower c))
                                (trans (distribʳ (lower a) (lower b) (lower c))
                                  (cong₂ _+_ (*-comm (lower b) (lower a)) (*-comm (lower c) (lower a))))))
                          , (λ a b c → lc (distribʳ (lower a) (lower b) (lower c))) }
            ; zero = (λ a → lc (zeroˡ (lower a))) , (λ a → lc (zeroʳ (lower a))) }
        ; *-comm = λ a b → lc (*-comm (lower a) (lower b)) }
    }

  private
    _≤ᶜ_ : C → C → Set ℓ
    a ≤ᶜ b = Lift ℓ (lower a ⊑ lower b)

    chain : (ℕ → C) → ℕ → ℕ∞
    chain c n = lower (c n)

    supOf : ∀ (c : ℕ → C) → (∀ n → c n ≤ᶜ c (suc n)) → Σ ℕ∞ (Sup (chain c))
    supOf c inc = sup-exists (chain c) (λ n → lower (inc n))

    +-mono′ : ∀ {a b c d} → a ⊑ b → c ⊑ d → a + c ⊑ b + d
    +-mono′ {a} {b} {c} {d} p q = ⊑-trans s₁ (+-mono⊑ b q)
      where s₁ : a + c ⊑ b + c
            s₁ = subst (λ x → x ⊑ b + c) (+-comm c a) (subst (λ y → c + a ⊑ y) (+-comm c b) (+-mono⊑ c p))

  ExtNatOmega : OmegaSemiring ℓ
  ExtNatOmega = record
    { ordered = record
          { commutativeSemiring = commSemiring
        ; _≤_ = _≤ᶜ_
        ; isPartialOrder = record
            { isPreorder = record
                { isEquivalence = isEquivalence
                ; reflexive = λ e → lift (⊑-reflexive (cong lower e))
                ; trans = λ p q → lift (⊑-trans (lower p) (lower q)) }
            ; antisym = λ p q → lc (⊑-antisym (lower p) (lower q)) }
        ; 0-least = lift 0-⊑
        ; ≤-+ʳ = λ {a} {b} → lift (x⊑x+y (lower a) (lower b))
        ; +-mono = λ p q → lift (+-mono′ (lower p) (lower q))
        ; *-mono = λ c p → lift (*-mono⊑ (lower c) (lower p))
        ; complement = λ {c} h → let (d , e) = ⊑⇒≤ (lower h) in lift d , lc e
          }
    ; ⨆ = λ c inc → lift (proj₁ (supOf c inc))
    ; ⨆-ub = λ c inc n → lift (Sup-ub (proj₂ (supOf c inc)) n)
    ; ⨆-lub = λ c inc {b} le → lift (Sup-lub (proj₂ (supOf c inc)) (λ n → lower (le n)))
    ; +-⨆ = λ a c inc inc′ → lc (Sup-unique (Sup-+ (lower a) (proj₂ (supOf c inc))) (proj₂ (supOf _ inc′)))
    ; *-⨆ = λ a c inc inc′ → lc (Sup-unique (Sup-* (lower a) (proj₂ (supOf c inc))) (proj₂ (supOf _ inc′)))
    ; cancel = λ {a} {x} {y} h e → lc (cancel (lower h) (cong lower e))
    }
