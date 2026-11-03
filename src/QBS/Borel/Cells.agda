{-# OPTIONS --safe --without-K #-}

-- Blocks and cells of Cantor space: the cylinders that the digit code of `[0,∞]` (`Continuous/DigitCode`) sends to
-- dyadic intervals (plan 03, "Uniqueness on the half-line").  Skeleton: holes first.
--   * `Blk k = {trueᵏ false …}`, the k-th block of the unary integer part (as `Borel/Lead`, without the all-true point);
--   * `Cell k w = Blk k ∩ {the bits after the block start with the word w}`, the code of a dyadic interval of length
--     2^{-|w|} inside [k, k+1);
--   * `Top`, the all-true sequence (the code of ∞), which lies in no block;
--   * `cyl-refine`: every cylinder is decided on every cell of a large enough depth inside a block, so measures that
--     agree on the cells of a block agree on every cylinder inside it (`Continuous/UniquenessR`).
module QBS.Borel.Cells where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Bool.Properties using (_≟_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-cmp; +-suc; +-identityʳ; m≤n⇒∃[o]m+o≡n; m≤m+n; m≤n+m; ≤-trans; <-≤-trans; ≤-<-trans)
open import Data.List.Base using (List; []; _∷_; _++_; map; length; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat.Properties using () renaming (suc-injective to sucInj)
open import Relation.Binary using (tri<; tri≈; tri>)

open import QBS.Borel.Core using (Cantor; Pred; Borel; gen; ⋂; resp)
open import QBS.Borel.PiLambda using (Cyl; cylTop; cylAnd; cylResp; Cyl-∩)
open import QBS.Borel.Merge using (Cyl-borel)

Word : Set
Word = List Bool

-- drop the first j bits
dropC : ℕ → Cantor → Cantor
dropC j x i = x (j + i)

-- the first k bits are true
Ones : ℕ → Pred
Ones zero x = ⊤
Ones (suc k) x = (x zero ≡ true) × Ones k (dropC 1 x)

-- the sequence starts with the word w
Match : Word → Pred
Match [] x = ⊤
Match (b ∷ w) x = (x zero ≡ b) × Match w (dropC 1 x)

Blk : ℕ → Pred
Blk k x = Ones k x × (x k ≡ false)

Cell : ℕ → Word → Pred
Cell k w x = Blk k x × Match w (dropC (suc k) x)

Top : Pred
Top x = ∀ i → x i ≡ true

-- all words of length n
words : ℕ → List Word
words zero = [] ∷ []
words (suc n) = map (true ∷_) (words n) ++ map (false ∷_) (words n)

----------------------------------------------------------------------------
-- pointwise respect, and the offset forms of Ones and Match

Ones-≗ : ∀ k {x y} → (∀ i → x i ≡ y i) → Ones k x → Ones k y
Ones-≗ zero e _ = tt
Ones-≗ (suc k) e (p , q) = trans (sym (e zero)) p , Ones-≗ k (λ i → e (suc i)) q

Match-≗ : ∀ w {x y} → (∀ i → x i ≡ y i) → Match w x → Match w y
Match-≗ [] e _ = tt
Match-≗ (b ∷ w) e (p , q) = trans (sym (e zero)) p , Match-≗ w (λ i → e (suc i)) q

dd : ∀ s x i → dropC 1 (dropC s x) i ≡ dropC (suc s) x i
dd s x i = cong x (+-suc s i)

d0 : ∀ s x → dropC s x zero ≡ x s
d0 s x = cong x (+-identityʳ s)

cylMatch : ∀ s w → Cyl (λ x → Match w (dropC s x))
cylMatch s [] = cylTop
cylMatch s (b ∷ w) = cylResp eq (cylAnd (cylMatch (suc s) w) s b)
  where
  eq = λ x → (λ (m , e) → trans (d0 s x) e , Match-≗ w (λ i → sym (dd s x i)) m)
           , (λ (e , m) → Match-≗ w (dd s x) m , trans (sym (d0 s x)) e)

cylOnes : ∀ s k → Cyl (λ x → Ones k (dropC s x))
cylOnes s zero = cylTop
cylOnes s (suc k) = cylResp eq (cylAnd (cylOnes (suc s) k) s true)
  where
  eq = λ x → (λ (m , e) → trans (d0 s x) e , Ones-≗ k (λ i → sym (dd s x i)) m)
           , (λ (e , m) → Ones-≗ k (dd s x) m , trans (sym (d0 s x)) e)

cylBlk : ∀ k → Cyl (Blk k)
cylBlk k = cylAnd (cylOnes 0 k) k false

cylCell : ∀ k w → Cyl (Cell k w)
cylCell k w = Cyl-∩ (cylBlk k) (cylMatch (suc k) w)

borelBlk : ∀ k → Borel (Blk k)
borelBlk k = Cyl-borel (cylBlk k)

borelCell : ∀ k w → Borel (Cell k w)
borelCell k w = Cyl-borel (cylCell k w)

borelTop : Borel Top
borelTop = resp (λ x → (λ f n → f n) , (λ f n → f n)) (⋂ (λ i → gen i true))

----------------------------------------------------------------------------
-- the blocks and the all-true point are disjoint; the cells of one depth partition a block

ones-at : ∀ {k x} → Ones k x → ∀ j → j < k → x j ≡ true
ones-at {suc k} (p , q) zero _ = p
ones-at {suc k} (p , q) (suc j) (s≤s h) = ones-at q j h

true≢false : true ≡ false → ⊥
true≢false ()

blk-lt : ∀ {j k x} → Blk j x → Blk k x → j < k → ⊥
blk-lt (_ , f) (o , _) h = true≢false (trans (sym (ones-at o _ h)) f)

blk-unique : ∀ {j k x} → Blk j x → Blk k x → j ≡ k
blk-unique {j} {k} bj bk with <-cmp j k
... | tri< h _ _ = ⊥-elim (blk-lt bj bk h)
... | tri≈ _ e _ = e
... | tri> _ _ h = ⊥-elim (blk-lt bk bj h)

top-blk : ∀ {k x} → Top x → Blk k x → ⊥
top-blk t (_ , f) = true≢false (trans (sym (t _)) f)

cell-blk : ∀ {k w x} → Cell k w x → Blk k x
cell-blk (b , _) = b

-- the first n bits of a sequence, as a word
take′ : ℕ → Cantor → Word
take′ zero z = []
take′ (suc n) z = z zero ∷ take′ n (dropC 1 z)

match-take : ∀ n z → Match (take′ n z) z
match-take zero z = tt
match-take (suc n) z = refl , match-take n (dropC 1 z)

mem-cons : ∀ b {w} n → w ∈ words n → b ∷ w ∈ words (suc n)
mem-cons true n h = ∈-++⁺ˡ (∈-map⁺ (true ∷_) h)
mem-cons false n h = ∈-++⁺ʳ (map (true ∷_) (words n)) (∈-map⁺ (false ∷_) h)

mem-take : ∀ n z → take′ n z ∈ words n
mem-take zero z = here refl
mem-take (suc n) z = mem-cons (z zero) n (mem-take n (dropC 1 z))

cell-words : ∀ k n x → Blk k x → Σ Word (λ w → (w ∈ words n) × Cell k w x)
cell-words k n x b = take′ n (dropC (suc k) x) , mem-take n _ , b , match-take n _

match-unique : ∀ {w v z} → length w ≡ length v → Match w z → Match v z → w ≡ v
match-unique {[]} {[]} _ _ _ = refl
match-unique {b ∷ w} {c ∷ v} l (p , m) (q , n) =
  cong₂ _∷_ (trans (sym p) q) (match-unique (sucInj l) m n)

cell-unique : ∀ {k w v x} → length w ≡ length v → Cell k w x → Cell k v x → w ≡ v
cell-unique l (_ , m) (_ , n) = match-unique l m n

----------------------------------------------------------------------------
-- cylinders are decidable, and depend on finitely many bits

dec-cyl : ∀ {C} → Cyl C → ∀ x → Dec (C x)
dec-cyl cylTop x = yes tt
dec-cyl (cylAnd c n b) x = dec-cyl c x ×-dec (x n ≟ b)
dec-cyl (cylResp e c) x = map′ (proj₁ (e x)) (proj₂ (e x)) (dec-cyl c x)

Agree : ℕ → Cantor → Cantor → Set
Agree N x y = ∀ i → i < N → x i ≡ y i

cyl-fin : ∀ {C} → Cyl C → Σ ℕ λ N → ∀ x y → Agree N x y → C x → C y
cyl-fin cylTop = 0 , λ _ _ _ _ → tt
cyl-fin (cylAnd {U} c n b) with cyl-fin c
... | N , p = N + suc n , λ x y a (u , e) →
  p x y (λ i h → a i (<-≤-trans h (m≤m+n N _))) u
  , trans (sym (a n (m≤n+m (suc n) N))) e
cyl-fin (cylResp e c) with cyl-fin c
... | N , p = N , λ x y a v → proj₁ (e y) (p x y a (proj₂ (e x) v))

----------------------------------------------------------------------------
-- cells fix the first (k + 1 + depth) bits; a canonical point of each cell

match-agree : ∀ w {x y} → Match w x → Match w y → ∀ j → j < length w → x j ≡ y j
match-agree (b ∷ w) (p , m) (q , n) zero _ = trans p (sym q)
match-agree (b ∷ w) (p , m) (q , n) (suc j) (s≤s h) = match-agree w m n j h

cell-agree : ∀ {k w x y} → Cell k w x → Cell k w y → Agree (length w) x y
cell-agree {k} ((ox , fx) , mx) ((oy , fy) , my) i h with <-cmp k i
... | tri> _ _ g = trans (ones-at ox i g) (sym (ones-at oy i g))
... | tri≈ _ refl _ = trans fx (sym fy)
... | tri< g _ _ with m≤n⇒∃[o]m+o≡n g
...   | j , refl = match-agree _ mx my j (≤-<-trans (m≤n+m j (suc k)) h)

cons : Bool → Cantor → Cantor
cons b z zero = b
cons b z (suc i) = z i

pre : Word → Cantor → Cantor
pre [] z = z
pre (b ∷ u) z = cons b (pre u z)

canon : ℕ → Word → Cantor
canon k w = pre (replicate k true ++ false ∷ w) (λ _ → false)

pre-at : ∀ k u z j → pre (replicate k true ++ u) z (k + j) ≡ pre u z j
pre-at zero u z j = refl
pre-at (suc k) u z j = pre-at k u z j

ones-pre : ∀ k u z → Ones k (pre (replicate k true ++ u) z)
ones-pre zero u z = tt
ones-pre (suc k) u z = refl , ones-pre k u z

match-pre : ∀ w z → Match w (pre w z)
match-pre [] z = tt
match-pre (b ∷ w) z = refl , match-pre w z

canon-in : ∀ k w → Cell k w (canon k w)
canon-in k w = (ones-pre k u z , trans (cong x (sym (+-identityʳ k))) (pre-at k u z 0))
  , Match-≗ w e (match-pre w z)
  where
  u = false ∷ w
  z : Cantor
  z _ = false
  x = canon k w
  e : ∀ j → pre w z j ≡ dropC (suc k) x j
  e j = trans (sym (pre-at k u z (suc j))) (cong x (+-suc k j))

----------------------------------------------------------------------------
-- every cylinder is decided on the cells of a large enough depth

cyl-refine : ∀ {C} → Cyl C → ∀ k → Σ ℕ λ n → ∀ w → length w ≡ n →
  (∀ x → Cell k w x → C x) ⊎ (∀ x → Cell k w x → C x → ⊥)
cyl-refine {C} c k with cyl-fin c
... | N , p = N , λ w lw → go w lw (dec-cyl c (canon k w))
  where
  ag : ∀ w → length w ≡ N → ∀ {x y} → Cell k w x → Cell k w y → Agree N x y
  ag w lw cx cy i h = cell-agree cx cy i (subst (i <_) (sym lw) h)
  go : ∀ w → length w ≡ N → Dec (C (canon k w)) →
    (∀ x → Cell k w x → C x) ⊎ (∀ x → Cell k w x → C x → ⊥)
  go w lw (yes y) = inj₁ (λ x cx → p _ x (ag w lw (canon-in k w) cx) y)
  go w lw (no n) = inj₂ (λ x cx Cx → n (p x _ (ag w lw cx (canon-in k w)) Cx))
