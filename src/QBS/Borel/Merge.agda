{-# OPTIONS --safe --without-K #-}

-- Bit interleaving on Cantor space: merge a b takes its even bits from a and its odd bits from b.
-- Only pointwise facts are used (no function extensionality): finite cylinders are rectangles
-- C₁ × C₂ with respect to merge, and sections of Borel sets are Borel.
module QBS.Borel.Merge where

open import Function.Base using (id; _∘_; const)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Bool.Properties using (_≟_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toSum)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Borel.Core
open import QBS.Borel.PiLambda using (Cyl; cylTop; cylAnd; cylResp; ∁; ⊤ᵖ; ⊥ᵖ)

-- is n even, and n div 2
ev : ℕ → Bool
ev zero = true
ev (suc zero) = false
ev (suc (suc n)) = ev n

hf : ℕ → ℕ
hf zero = zero
hf (suc zero) = zero
hf (suc (suc n)) = suc (hf n)

mergeBit : Bool → Bool → Bool → Bool
mergeBit true x y = x
mergeBit false x y = y

mergeC : Cantor → Cantor → Cantor
mergeC a b n = mergeBit (ev n) (a (hf n)) (b (hf n))

-- constant propositions (with a decision) are Borel
borel-const : ∀ (P : Set) → P ⊎ (P → ⊥) → Borel (λ (_ : Cantor) → P)
borel-const P (inj₁ p) = resp (λ x → (λ _ → p) , (λ _ → tt)) ⊤-borel
borel-const P (inj₂ np) = resp (λ x → (λ b → ⊥-elim b) , (λ p → np p)) ⊥-borel

bool-dec : ∀ (x y : Bool) → (x ≡ y) ⊎ ((x ≡ y) → ⊥)
bool-dec x y = toSum (x ≟ y)

-- merge is measurable in each argument
measurable-merge₁ : ∀ a → Measurable (mergeC a)
measurable-merge₁ a n β with ev n
... | true = borel-const (a (hf n) ≡ β) (bool-dec _ _)
... | false = gen (hf n) β

measurable-merge₂ : ∀ b → Measurable (λ a → mergeC a b)
measurable-merge₂ b n β with ev n
... | true = gen (hf n) β
... | false = borel-const (b (hf n) ≡ β) (bool-dec _ _)

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

mergeC-even : ∀ n a s → ev n ≡ true → mergeC a s n ≡ a (hf n)
mergeC-even n a s e = ≡.cong (λ b → mergeBit b (a (hf n)) (s (hf n))) e

mergeC-odd : ∀ n a s → ev n ≡ false → mergeC a s n ≡ s (hf n)
mergeC-odd n a s e = ≡.cong (λ b → mergeBit b (a (hf n)) (s (hf n))) e

-- adding one coordinate constraint to a rectangle (split on the parity of n by a variable)
rect-step : ∀ {V} (n : ℕ) (β : Bool) (d : Bool) → ev n ≡ d → Rect mergeC V → Rect mergeC (λ x → V x × (x n ≡ β))
rect-step n β true en (C₁ , C₂ , c₁ , c₂ , fw , bw) =
  (λ a → C₁ a × (a (hf n) ≡ β)) , C₂ , cylAnd c₁ (hf n) β , c₂
  , (λ a s (v , e) → let (p₁ , p₂) = fw a s v in (p₁ , ≡.trans (≡.sym (mergeC-even n a s en)) e) , p₂)
  , (λ a s (p₁ , e) p₂ → bw a s p₁ p₂ , ≡.trans (mergeC-even n a s en) e)
rect-step n β false en (C₁ , C₂ , c₁ , c₂ , fw , bw) =
  C₁ , (λ s → C₂ s × (s (hf n) ≡ β)) , c₁ , cylAnd c₂ (hf n) β
  , (λ a s (v , e) → let (p₁ , p₂) = fw a s v in p₁ , (p₂ , ≡.trans (≡.sym (mergeC-odd n a s en)) e))
  , (λ a s p₁ (p₂ , e) → bw a s p₁ p₂ , ≡.trans (mergeC-odd n a s en) e)

Cyl-rect : ∀ {U} → Cyl U → Rect mergeC U
Cyl-rect cylTop = ⊤ᵖ , ⊤ᵖ , cylTop , cylTop , (λ _ _ _ → tt , tt) , (λ _ _ _ _ → tt)
Cyl-rect (cylAnd {V} c n β) = rect-step {V} n β (ev n) ≡.refl (Cyl-rect {V} c)
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
