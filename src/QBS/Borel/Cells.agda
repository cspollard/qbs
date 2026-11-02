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
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import QBS.Borel.Core using (Cantor; Pred; Borel)
open import QBS.Borel.PiLambda using (Cyl)
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
-- blocks and cells are cylinders; the all-true point is Borel

cylBlk : ∀ k → Cyl (Blk k)
cylBlk = ?

cylCell : ∀ k w → Cyl (Cell k w)
cylCell = ?

borelBlk : ∀ k → Borel (Blk k)
borelBlk k = Cyl-borel (cylBlk k)

borelCell : ∀ k w → Borel (Cell k w)
borelCell k w = Cyl-borel (cylCell k w)

borelTop : Borel Top
borelTop = ?

----------------------------------------------------------------------------
-- the blocks and the all-true point are disjoint; the cells of one depth partition a block

blk-unique : ∀ {j k x} → Blk j x → Blk k x → j ≡ k
blk-unique = ?

top-blk : ∀ {k x} → Top x → Blk k x → ⊥
top-blk = ?

cell-blk : ∀ {k w x} → Cell k w x → Blk k x
cell-blk (b , _) = b

cell-words : ∀ k n x → Blk k x → Σ Word (λ w → (w ∈ words n) × Cell k w x)
cell-words = ?

cell-unique : ∀ {k w v x} → length w ≡ length v → Cell k w x → Cell k v x → w ≡ v
cell-unique = ?

-- every cylinder is decided on the cells of a large enough depth
cyl-refine : ∀ {C} → Cyl C → ∀ k → Σ ℕ λ n → ∀ w → length w ≡ n →
  (∀ x → Cell k w x → C x) ⊎ (∀ x → Cell k w x → C x → ⊥)
cyl-refine = ?
