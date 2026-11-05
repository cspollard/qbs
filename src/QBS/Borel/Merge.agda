{-# OPTIONS --safe --without-K #-}

-- Bit interleaving on Cantor space: merge a b takes its even bits from a and its odd bits from b
-- (defined by recursion, so that the tail of merge a b is merge b (tail a) by `refl`).
-- Only pointwise facts are used (no function extensionality): finite cylinders are rectangles
-- C₁ × C₂ with respect to merge, and sections of Borel sets are Borel.
module QBS.Borel.Merge where

open import Data.Bool.Base using (Bool)
open import Data.Bool.Properties using (_≟_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (toSum)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Borel.Core
open import QBS.Borel.PiLambda using (Cyl; cylTop; cylAnd; cylResp; ⊤ᵖ)

-- as `Codata.Guarded.Stream.interleave`: the tail of `mergeC a b` is `mergeC b (tail a)`
mergeC : Cantor → Cantor → Cantor
mergeC a b zero = a zero
mergeC a b (suc n) = mergeC b (λ k → a (suc k)) n

mergeC-even : ∀ n a s → mergeC a s (n + n) ≡ a n
mergeC-even zero a s = ≡.refl
mergeC-even (suc n) a s =
  ≡.trans (≡.cong (mergeC a s) (≡.cong suc (+-suc n n))) (mergeC-even n (λ k → a (suc k)) (λ k → s (suc k)))

mergeC-odd : ∀ n a s → mergeC a s (suc (n + n)) ≡ s n
mergeC-odd n a s = mergeC-even n s (λ k → a (suc k))

-- every index is a double or one more
even-or-odd : ∀ n → Σ ℕ (λ k → (n ≡ k + k) ⊎ (n ≡ suc (k + k)))
even-or-odd zero = zero , inj₁ ≡.refl
even-or-odd (suc n) with even-or-odd n
... | k , inj₁ e = k , inj₂ (≡.cong suc e)
... | k , inj₂ e = suc k , inj₁ (≡.trans (≡.cong suc e) (≡.cong suc (≡.sym (+-suc k k))))

-- constant propositions (with a decision) are Borel
borel-const : ∀ (P : Set) → P ⊎ (P → ⊥) → Borel (λ (_ : Cantor) → P)
borel-const P (inj₁ p) = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
borel-const P (inj₂ np) = resp (λ x → (λ b → ⊥-elim b) , (λ p → np p)) ⊥-borel

bool-dec : ∀ (x y : Bool) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
bool-dec x y = toSum (x ≟ y)

-- merge is measurable in both arguments (also jointly with the arguments varying with k)
measurable-merge : ∀ {a b : Cantor → Cantor} → Measurable a → Measurable b →
  Measurable (λ k → mergeC (a k) (b k))
measurable-merge ma mb zero β = ma zero β
measurable-merge ma mb (suc n) β = measurable-merge mb (λ m → ma (suc m)) n β

measurable-merge₁ : ∀ a → Measurable (mergeC a)
measurable-merge₁ a = measurable-merge (λ n β → borel-const (a n ≡ β) (bool-dec _ _)) gen

measurable-merge₂ : ∀ b → Measurable (λ a → mergeC a b)
measurable-merge₂ b = measurable-merge gen (λ n β → borel-const (b n ≡ β) (bool-dec _ _))

-- finite cylinders are decidable and Borel
Cyl-dec : ∀ {C} → Cyl C → ∀ x → C x ⊎ (C x → ⊥)
Cyl-dec cylTop x = inj₁ tt
Cyl-dec (cylAnd c n b) x with Cyl-dec c x | bool-dec (x n) b
... | inj₁ u | inj₁ e = inj₁ (u , e)
... | inj₂ nu | _ = inj₂ (λ (u , _) → nu u)
... | _ | inj₂ ne = inj₂ (λ (_ , e) → ne e)
Cyl-dec (cylResp e c) x with Cyl-dec c x
... | inj₁ u = inj₁ (proj₁ (e x) u)
... | inj₂ nu = inj₂ (λ v → nu (proj₂ (e x) v))

Cyl-borel : ∀ {C} → Cyl C → Borel C
Cyl-borel cylTop = ⊤-borel
Cyl-borel (cylAnd c n b) = inter₂ (Cyl-borel c) (gen n b)
Cyl-borel (cylResp e c) = resp e (Cyl-borel c)

-- a finite cylinder is a rectangle for merge
Rect : (Cantor → Cantor → Cantor) → Pred → Set₁
Rect m U = Σ Pred (λ C₁ → Σ Pred (λ C₂ →
  Cyl C₁ × Cyl C₂ × (∀ a s → U (m a s) → C₁ a × C₂ s) × (∀ a s → C₁ a → C₂ s → U (m a s))))

-- adding one coordinate constraint to a rectangle (split on the parity of n by a variable)
rect-step : ∀ {V} (n : ℕ) (β : Bool) → Rect mergeC V → Rect mergeC (λ x → V x × (x n ≡ β))
rect-step n β r with even-or-odd n
rect-step .(k + k) β (C₁ , C₂ , c₁ , c₂ , fw , bw) | k , inj₁ ≡.refl =
  (λ a → C₁ a × (a k ≡ β)) , C₂ , cylAnd c₁ k β , c₂
  , (λ a s (v , e) → let (p₁ , p₂) = fw a s v in (p₁ , ≡.trans (≡.sym (mergeC-even k a s)) e) , p₂)
  , (λ a s (p₁ , e) p₂ → bw a s p₁ p₂ , ≡.trans (mergeC-even k a s) e)
rect-step .(suc (k + k)) β (C₁ , C₂ , c₁ , c₂ , fw , bw) | k , inj₂ ≡.refl =
  C₁ , (λ s → C₂ s × (s k ≡ β)) , c₁ , cylAnd c₂ k β
  , (λ a s (v , e) → let (p₁ , p₂) = fw a s v in p₁ , (p₂ , ≡.trans (≡.sym (mergeC-odd k a s)) e))
  , (λ a s p₁ (p₂ , e) → bw a s p₁ p₂ , ≡.trans (mergeC-odd k a s) e)

Cyl-rect : ∀ {U} → Cyl U → Rect mergeC U
Cyl-rect cylTop = ⊤ᵖ , ⊤ᵖ , cylTop , cylTop , (λ _ _ _ → tt , tt) , (λ _ _ _ _ → tt)
Cyl-rect (cylAnd {V} c n β) = rect-step {V} n β (Cyl-rect {V} c)
Cyl-rect (cylResp {U} {V} e c) with Cyl-rect {U} c
... | C₁ , C₂ , c₁ , c₂ , fw , bw =
  C₁ , C₂ , c₁ , c₂ , (λ a s v → fw a s (proj₂ (e (mergeC a s)) v)) , (λ a s p₁ p₂ → proj₁ (e (mergeC a s)) (bw a s p₁ p₂))

-- the same with the arguments of merge swapped (explicit projections, so the components of the
-- flipped decomposition are definitionally the components of the original one)
Cyl-rect-flip : ∀ {U} → Cyl U → Rect (λ a s → mergeC s a) U
Cyl-rect-flip {U} c =
  proj₁ (proj₂ r) , proj₁ r , proj₁ (proj₂ (proj₂ (proj₂ r))) , proj₁ (proj₂ (proj₂ r))
  , (λ a s u → proj₂ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))) s a u) , proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))) s a u))
  , (λ a s p₂ p₁ → proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))) s a p₁ p₂)
  where r = Cyl-rect c
