{-# OPTIONS --safe --without-K #-}

-- Cantor's pairing function ℕ × ℕ ≅ ℕ: `pair a b = tri (a + b) + b`, and `unpair`
-- walks the diagonals one step at a time.
module QBS.Model.Pairing where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-suc; +-identityʳ; n∸n≡0; m+n∸n≡m; ≤-refl; ≤-trans; n≤1+n; m≤n+m)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong)

-- triangular numbers
tri : ℕ → ℕ
tri zero = zero
tri (suc n) = suc n + tri n

pair : ℕ → ℕ → ℕ
pair a b = tri (a + b) + b

-- the next point on the diagonal enumeration
next : ℕ × ℕ → ℕ × ℕ
next (zero , b) = suc b , zero
next (suc a , b) = a , suc b

unpair : ℕ → ℕ × ℕ
unpair zero = zero , zero
unpair (suc n) = next (unpair n)

-- m ∸ b is a successor when b < m
sub : ∀ m b → suc b ≤ m → m ∸ b ≡ suc (m ∸ suc b)
sub (suc m) zero _ = refl
sub (suc m) (suc b) (s≤s le) = sub m b le

next-sub : ∀ m b → suc b ≤ m → next (m ∸ b , b) ≡ (m ∸ suc b , suc b)
next-sub m b le = cong (λ x → next (x , b)) (sub m b le)

-- unpair (tri m + b) walks b steps down the m-th diagonal
unpair-diag : ∀ m b → b ≤ m → unpair (tri m + b) ≡ (m ∸ b , b)
unpair-tri : ∀ m → unpair (tri m) ≡ (m , zero)

unpair-diag m zero le = trans (cong unpair (+-identityʳ (tri m))) (unpair-tri m)
unpair-diag m (suc b) le =
  trans (cong (λ x → unpair x) (+-suc (tri m) b))
    (trans (cong next (unpair-diag m b (≤-trans (n≤1+n b) le)))
           (next-sub m b le))

unpair-tri zero = refl
unpair-tri (suc m) =
  trans (cong (λ x → unpair (suc x)) (+-comm m (tri m)))
    (trans (cong next (unpair-diag m m ≤-refl))
           (cong (λ k → next (k , m)) (n∸n≡0 m)))

unpair-pair : ∀ a b → unpair (pair a b) ≡ (a , b)
unpair-pair a b =
  trans (unpair-diag (a + b) b (m≤n+m b a))
        (cong (λ k → k , b) (m+n∸n≡m a b))

pair′ : ℕ × ℕ → ℕ
pair′ (a , b) = pair a b

pair-next : ∀ p → pair′ (next p) ≡ suc (pair′ p)
pair-next (zero , b) =
  trans (+-identityʳ (tri (suc b + zero)))
    (trans (cong (λ x → tri (suc x)) (+-identityʳ b)) (cong suc (+-comm b (tri b))))
pair-next (suc a , b) = trans (cong (λ x → tri x + suc b) (+-suc a b)) (+-suc (tri (suc (a + b))) b)

pair-unpair : ∀ n → pair′ (unpair n) ≡ n
pair-unpair zero = refl
pair-unpair (suc n) = trans (pair-next (unpair n)) (cong suc (pair-unpair n))
