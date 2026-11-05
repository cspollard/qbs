{-# OPTIONS --safe --without-K #-}

-- Vectors and matrices over a commutative ring (plan 05, item 51), for mean vectors and covariance matrices of random
-- vectors; instantiated at the signed values (`Analysis/Signed.signedRing`).  Model independent, like
-- `Analysis/Estimator`.
--   * `Vec n = Fin n → R`, `Mat m n = Fin m → Fin n → R`, pointwise equalities `_≈V_`, `_≈M_`;
--   * `Σ n f = f 0 + (f 1 + (… + 0))`, with `Σ-cong`, `Σ-0`, `Σ-+`, `Σ-scale`, `Σ-swap` (the order of a double sum);
--   * `_+V_`, `_·_` (dot product), `_*Mv_`, `_*M_`, transpose `_ᵀ`, the identity matrix `idM`, the quadratic form
--     `quad A x = xᵀ A x`;
--   * laws: `*Mv-+` (distributivity), `*Mv-assoc` ((AB)x = A(Bx)), `*M-assoc`, `ᵀ-*M` ((AB)ᵀ = BᵀAᵀ), `ᵀ-ᵀ`,
--     `idM-*Mv`.
-- Route: induction on n for the Σ lemmas (`Σ-swap` from `Σ-+`); the matrix laws are Σ lemmas pointwise.
--   Skeleton: holes first.
module QBS.Analysis.SgLinAlg where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)

module SgLinAlg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R using (Carrier; _≈_; _+_; _*_; 0#; 1#)

  Vec : ℕ → Set c
  Vec n = Fin n → Carrier

  Mat : ℕ → ℕ → Set c
  Mat m n = Fin m → Fin n → Carrier

  infix 4 _≈V_ _≈M_
  _≈V_ : ∀ {n} → Vec n → Vec n → Set ℓ
  x ≈V y = ∀ i → x i ≈ y i

  _≈M_ : ∀ {m n} → Mat m n → Mat m n → Set ℓ
  A ≈M B = ∀ i j → A i j ≈ B i j

  -- finite sums
  Σ : ∀ n → (Fin n → Carrier) → Carrier
  Σ zero f = 0#
  Σ (suc n) f = f zero + Σ n (λ i → f (suc i))

  Σ-cong : ∀ n {f g : Fin n → Carrier} → (∀ i → f i ≈ g i) → Σ n f ≈ Σ n g
  Σ-cong = ?

  Σ-0 : ∀ n → Σ n (λ _ → 0#) ≈ 0#
  Σ-0 = ?

  Σ-+ : ∀ n (f g : Fin n → Carrier) → Σ n (λ i → f i + g i) ≈ Σ n f + Σ n g
  Σ-+ = ?

  Σ-scale : ∀ n c (f : Fin n → Carrier) → c * Σ n f ≈ Σ n (λ i → c * f i)
  Σ-scale = ?

  Σ-swap : ∀ m n (f : Fin m → Fin n → Carrier) → Σ m (λ i → Σ n (f i)) ≈ Σ n (λ j → Σ m (λ i → f i j))
  Σ-swap = ?

  -- vector and matrix operations
  infixl 6 _+V_
  _+V_ : ∀ {n} → Vec n → Vec n → Vec n
  (x +V y) i = x i + y i

  infixl 7 _·_ _*Mv_ _*M_
  _·_ : ∀ {n} → Vec n → Vec n → Carrier
  _·_ {n} x y = Σ n (λ i → x i * y i)

  _*Mv_ : ∀ {m n} → Mat m n → Vec n → Vec m
  (A *Mv x) i = A i · x

  _*M_ : ∀ {m n k} → Mat m n → Mat n k → Mat m k
  _*M_ {n = n} A B i j = Σ n (λ l → A i l * B l j)

  infix 8 _ᵀ
  _ᵀ : ∀ {m n} → Mat m n → Mat n m
  (A ᵀ) i j = A j i

  idM : ∀ {n} → Mat n n
  idM zero zero = 1#
  idM zero (suc j) = 0#
  idM (suc i) zero = 0#
  idM (suc i) (suc j) = idM i j

  quad : ∀ {n} → Mat n n → Vec n → Carrier
  quad A x = x · (A *Mv x)

  -- laws
  *Mv-+ : ∀ {m n} (A : Mat m n) (x y : Vec n) → A *Mv (x +V y) ≈V A *Mv x +V A *Mv y
  *Mv-+ = ?

  *Mv-assoc : ∀ {m n k} (A : Mat m n) (B : Mat n k) (x : Vec k) → (A *M B) *Mv x ≈V A *Mv (B *Mv x)
  *Mv-assoc = ?

  *M-assoc : ∀ {m n k l} (A : Mat m n) (B : Mat n k) (C : Mat k l) → (A *M B) *M C ≈M A *M (B *M C)
  *M-assoc = ?

  ᵀ-*M : ∀ {m n k} (A : Mat m n) (B : Mat n k) → (A *M B) ᵀ ≈M B ᵀ *M A ᵀ
  ᵀ-*M = ?

  ᵀ-ᵀ : ∀ {m n} (A : Mat m n) → (A ᵀ) ᵀ ≈M A
  ᵀ-ᵀ = ?

  idM-*Mv : ∀ {n} (x : Vec n) → idM *Mv x ≈V x
  idM-*Mv = ?
