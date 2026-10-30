{-# OPTIONS --safe --without-K #-}

-- Clopen subsets of Cantor space as finite binary trees, with Boolean semantics, and the fan
-- theorem (compactness of Cantor space): a decreasing sequence of clopen sets with empty
-- intersection is eventually empty.  Classical (`lem`); König's lemma by a choice of path.
module QBS.Analysis.Clopen where

open import Function.Base using (_∘_)
open import Data.Bool.Base using (Bool; true; false; not; _∨_; _∧_; T; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)

open import QBS.Borel.Core using (Cantor; Pred)

tl : Cantor → Cantor
tl x n = x (suc n)

cons : Bool → Cantor → Cantor
cons b y zero = b
cons b y (suc n) = y n

data Cl : Set where
  leaf : Bool → Cl
  split : Cl → Cl → Cl

eval : Cl → Cantor → Bool
eval (leaf c) x = c
eval (split a b) x = if x 0 then eval b (tl x) else eval a (tl x)

-- membership as a set
⟦_⟧ : Cl → Pred
⟦ t ⟧ x = T (eval t x)

child : Bool → Cl → Cl
child b (leaf c) = leaf c
child false (split a b) = a
child true (split a b) = b

eval-child : ∀ t b y → eval (child b t) y ≡ eval t (cons b y)
eval-child (leaf c) b y = refl
eval-child (split a c) false y = refl
eval-child (split a c) true y = refl

eval-ext : ∀ t {x y} → (∀ n → x n ≡ y n) → eval t x ≡ eval t y
eval-ext (leaf c) e = refl
eval-ext (split a b) {x} {y} e with x 0 | y 0 | e 0
... | false | .false | refl = eval-ext a (λ n → e (suc n))
... | true | .true | refl = eval-ext b (λ n → e (suc n))

eval-pt : ∀ t x → eval t x ≡ eval (child (x 0) t) (tl x)
eval-pt t x = trans (eval-ext t (λ { zero → refl ; (suc n) → refl })) (sym (eval-child t (x 0) (tl x)))

----------------------------------------------------------------------------
-- Boolean operations

infixl 6 _∪_
infixl 7 _∩_
_∪_ _∩_ : Cl → Cl → Cl
leaf true ∪ t = leaf true
leaf false ∪ t = t
split a b ∪ leaf true = leaf true
split a b ∪ leaf false = split a b
split a b ∪ split c d = split (a ∪ c) (b ∪ d)

leaf true ∩ t = t
leaf false ∩ t = leaf false
split a b ∩ leaf true = split a b
split a b ∩ leaf false = leaf false
split a b ∩ split c d = split (a ∩ c) (b ∩ d)

∁ᶜ : Cl → Cl
∁ᶜ (leaf c) = leaf (not c)
∁ᶜ (split a b) = split (∁ᶜ a) (∁ᶜ b)

∨-idʳ : ∀ b → b ∨ false ≡ b
∨-idʳ true = refl
∨-idʳ false = refl

∧-idʳ : ∀ b → b ∧ true ≡ b
∧-idʳ true = refl
∧-idʳ false = refl

∧-zeroʳ : ∀ b → b ∧ false ≡ false
∧-zeroʳ true = refl
∧-zeroʳ false = refl

∨-zeroʳ : ∀ b → b ∨ true ≡ true
∨-zeroʳ true = refl
∨-zeroʳ false = refl

eval-∪ : ∀ s t x → eval (s ∪ t) x ≡ eval s x ∨ eval t x
eval-∪ (leaf true) t x = refl
eval-∪ (leaf false) t x = refl
eval-∪ (split a b) (leaf true) x = sym (∨-zeroʳ _)
eval-∪ (split a b) (leaf false) x = sym (∨-idʳ _)
eval-∪ (split a b) (split c d) x with x 0
... | false = eval-∪ a c (tl x)
... | true = eval-∪ b d (tl x)

eval-∩ : ∀ s t x → eval (s ∩ t) x ≡ eval s x ∧ eval t x
eval-∩ (leaf true) t x = refl
eval-∩ (leaf false) t x = refl
eval-∩ (split a b) (leaf true) x = sym (∧-idʳ _)
eval-∩ (split a b) (leaf false) x = sym (∧-zeroʳ _)
eval-∩ (split a b) (split c d) x with x 0
... | false = eval-∩ a c (tl x)
... | true = eval-∩ b d (tl x)

eval-∁ : ∀ t x → eval (∁ᶜ t) x ≡ not (eval t x)
eval-∁ (leaf c) x = refl
eval-∁ (split a b) x with x 0
... | false = eval-∁ a (tl x)
... | true = eval-∁ b (tl x)

----------------------------------------------------------------------------
-- depth, and following a path

depth : Cl → ℕ
depth (leaf _) = 0
depth (split a b) = suc (depth a ⊔ depth b)

follow : Cl → Cantor → ℕ → Cl
follow t x zero = t
follow t x (suc n) = child (x n) (follow t x n)

drop : ℕ → Cantor → Cantor
drop zero x = x
drop (suc n) x = tl (drop n x)

drop-eq : ∀ n x i → drop n x i ≡ x (n + i)
drop-eq zero x i = refl
drop-eq (suc n) x i = trans (drop-eq n x (suc i)) (cong x (ℕₚ.+-suc n i))

drop-0 : ∀ n x → drop n x 0 ≡ x n
drop-0 n x = trans (drop-eq n x 0) (cong x (ℕₚ.+-identityʳ n))

eval-follow : ∀ t x n → eval t x ≡ eval (follow t x n) (drop n x)
eval-follow t x zero = refl
eval-follow t x (suc n) = trans (eval-follow t x n)
  (trans (eval-pt (follow t x n) (drop n x))
         (cong (λ b → eval (child b (follow t x n)) (tl (drop n x))) (drop-0 n x)))

depth-child : ∀ b s k → depth s ≤ suc k → depth (child b s) ≤ k
depth-child b (leaf c) k h = z≤n
depth-child false (split a c) k (s≤s h) = ℕₚ.≤-trans (ℕₚ.m≤m⊔n (depth a) (depth c)) h
depth-child true (split a c) k (s≤s h) = ℕₚ.≤-trans (ℕₚ.m≤n⊔m (depth a) (depth c)) h

depth-follow : ∀ t x n m → depth t ≤ n + m → depth (follow t x n) ≤ m
depth-follow t x zero m h = h
depth-follow t x (suc n) m h =
  depth-child (x n) (follow t x n) m (depth-follow t x n (suc m) (subst (depth t ≤_) (sym (ℕₚ.+-suc n m)) h))

leaf-of-depth : ∀ s → depth s ≤ 0 → Σ Bool (λ c → s ≡ leaf c)
leaf-of-depth (leaf c) h = c , refl
leaf-of-depth (split a b) ()

-- after `depth t` steps along any path the tree is a leaf, with the value of the point
eval-leaf : ∀ t x → Σ Bool (λ c → follow t x (depth t) ≡ leaf c × eval t x ≡ c)
eval-leaf t x with leaf-of-depth (follow t x (depth t)) (depth-follow t x (depth t) 0 (ℕₚ.≤-reflexive (sym (ℕₚ.+-identityʳ _))))
... | c , e = c , e , trans (eval-follow t x (depth t)) (subst (λ s → eval s (drop (depth t) x) ≡ c) (sym e) refl)

----------------------------------------------------------------------------
-- the fan theorem

Ne : Cl → Set
Ne t = Σ Cantor (λ y → eval t y ≡ true)

Decreasing : (ℕ → Cl) → Set
Decreasing G = ∀ N x → eval (G (suc N)) x ≡ true → eval (G N) x ≡ true

¬true⇒false : ∀ b → (b ≡ true → ⊥) → b ≡ false
¬true⇒false true h = ⊥-elim (h refl)
¬true⇒false false h = refl

true≢false : true ≡ false → ⊥
true≢false ()

module Fan (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where

  Bad : (ℕ → Cl) → Set
  Bad G = ∀ N → Ne (G N)

  childF : Bool → (ℕ → Cl) → ℕ → Cl
  childF b G N = child b (G N)

  dec-mono : ∀ G → Decreasing G → ∀ {N M} → N ℕ.≤′ M → ∀ x → eval (G M) x ≡ true → eval (G N) x ≡ true
  dec-mono G d ℕ.≤′-refl x h = h
  dec-mono G d {N} {suc M} (ℕ.≤′-step le) x h = dec-mono G d le x (d M x h)

  child-sub : ∀ s t → (∀ x → eval s x ≡ true → eval t x ≡ true) →
    ∀ b y → eval (child b s) y ≡ true → eval (child b t) y ≡ true
  child-sub s t h b y e =
    trans (eval-child t b y) (h (cons b y) (trans (sym (eval-child s b y)) e))

  childF-dec : ∀ G → Decreasing G → ∀ b → Decreasing (childF b G)
  childF-dec G d b N y = child-sub (G (suc N)) (G N) (d N) b y

  -- ¬ ∀ ⇒ ∃ ¬ (classically)
  not-all : ∀ {P : ℕ → Set} → ((∀ n → P n) → ⊥) → Σ ℕ (λ n → P n → ⊥)
  not-all {P} no with lem (Σ ℕ (λ n → P n → ⊥))
  ... | inj₁ w = w
  ... | inj₂ nw = ⊥-elim (no case-P)
    where
      case-P : ∀ n → P n
      case-P n with lem (P n)
      ... | inj₁ p = p
      ... | inj₂ np = ⊥-elim (nw (n , np))

  -- König's step: a bad decreasing sequence has a bad child
  bad-split : ∀ G → Decreasing G → Bad G → Bad (childF false G) ⊎ Bad (childF true G)
  bad-split G d bad with lem (Bad (childF false G))
  ... | inj₁ p = inj₁ p
  ... | inj₂ np = inj₂ go
    where
      go : ∀ N → Ne (child true (G N))
      go N with not-all {λ n → Ne (child false (G n))} np
      ... | N₀ , nne with bad (N ⊔ N₀)
      ...   | y , ey = by-bit (y 0) (trans (sym (eval-pt (G (N ⊔ N₀)) y)) ey)
        where
          by-bit : ∀ b → eval (child b (G (N ⊔ N₀))) (tl y) ≡ true → Ne (child true (G N))
          by-bit false h = ⊥-elim
              (nne (tl y , child-sub (G (N ⊔ N₀)) (G N₀) (dec-mono G d {N₀} {N ⊔ N₀} (ℕₚ.≤⇒≤′ (ℕₚ.m≤n⊔m N N₀))) false (tl y) h))
          by-bit true h = tl y , child-sub (G (N ⊔ N₀)) (G N) (dec-mono G d {N} {N ⊔ N₀} (ℕₚ.≤⇒≤′ (ℕₚ.m≤m⊔n N N₀))) true (tl y) h

  pick : (P : Set) → P ⊎ (P → ⊥) → Bool
  pick P (inj₁ _) = false
  pick P (inj₂ _) = true

  choice : (ℕ → Cl) → Bool
  choice G = pick (Bad (childF false G)) (lem (Bad (childF false G)))

  choice-ok : ∀ G → Decreasing G → Bad G → Bad (childF (choice G) G)
  choice-ok G d bad with lem (Bad (childF false G))
  ... | inj₁ p = p
  ... | inj₂ np with bad-split G d bad
  ...   | inj₁ q = ⊥-elim (np q)
  ...   | inj₂ q = q

  F : (ℕ → Cl) → ℕ → ℕ → Cl
  F E zero = E
  F E (suc n) = childF (choice (F E n)) (F E n)

  xs : (ℕ → Cl) → Cantor
  xs E n = choice (F E n)

  inv : ∀ E → Decreasing E → Bad E → ∀ n → Decreasing (F E n) × Bad (F E n)
  inv E d b zero = d , b
  inv E d b (suc n) = childF-dec (F E n) (proj₁ ih) _ , choice-ok (F E n) (proj₁ ih) (proj₂ ih)
    where ih = inv E d b n

  F-follow : ∀ E n N → F E n N ≡ follow (E N) (xs E) n
  F-follow E zero N = refl
  F-follow E (suc n) N = cong (child (choice (F E n))) (F-follow E n N)

  -- the fan theorem
  fan : ∀ E → Decreasing E → (∀ x → Σ ℕ (λ N → eval (E N) x ≡ false)) →
    Σ ℕ (λ N → ∀ x → eval (E N) x ≡ false)
  fan E d cover with lem (Σ ℕ (λ N → ∀ x → eval (E N) x ≡ false))
  ... | inj₁ w = w
  ... | inj₂ no = ⊥-elim (contra (cover (xs E)))
    where
      bad : Bad E
      bad N with lem (Ne (E N))
      ... | inj₁ ne = ne
      ... | inj₂ nne = ⊥-elim (no (N , λ x → ¬true⇒false (eval (E N) x) (λ e → nne (x , e))))
      contra : Σ ℕ (λ N → eval (E N) (xs E) ≡ false) → ⊥
      contra (N , e) with eval-leaf (E N) (xs E)
      ... | c , fl , ev = true≢false (trans (sym ctrue) cfalse)
        where
          n = depth (E N)
          ctrue : c ≡ true
          ctrue with proj₂ (inv E d bad n) N
          ... | y , ey = subst (λ s → eval s y ≡ true) (trans (F-follow E n N) fl) ey
          cfalse : c ≡ false
          cfalse = trans (sym ev) e
