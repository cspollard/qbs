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
-- Route: induction on n for the Σ lemmas (`Σ-swap` from `Σ-+`); the matrix laws are Σ lemmas pointwise.  Small
-- hand-written equational steps (no ring solver); `interchange` from stdlib for the middle-four swap, and a local
-- `Σ-scaleʳ` (right scaling) for `*Mv-assoc`.
module QBS.Analysis.SgLinAlg where

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Properties.CommutativeSemigroup using (interchange)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)

module SgLinAlg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R using (Carrier; _≈_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; +-identityˡ; +-identityʳ
    ; *-comm; *-assoc; *-identityʳ; distribˡ; zeroˡ; +-commutativeSemigroup; setoid)
  open import Relation.Binary.Reasoning.Setoid setoid

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
  Σ-cong zero h = refl
  Σ-cong (suc n) h = +-cong (h zero) (Σ-cong n (λ i → h (suc i)))

  Σ-0 : ∀ n → Σ n (λ _ → 0#) ≈ 0#
  Σ-0 zero = refl
  Σ-0 (suc n) = trans (+-cong refl (Σ-0 n)) (+-identityˡ 0#)

  Σ-+ : ∀ n (f g : Fin n → Carrier) → Σ n (λ i → f i + g i) ≈ Σ n f + Σ n g
  Σ-+ zero f g = sym (+-identityˡ 0#)
  Σ-+ (suc n) f g = trans (+-cong refl (Σ-+ n (λ i → f (suc i)) (λ i → g (suc i))))
    (sym (interchange +-commutativeSemigroup (f zero) _ (g zero) _))

  Σ-scale : ∀ n c (f : Fin n → Carrier) → c * Σ n f ≈ Σ n (λ i → c * f i)
  Σ-scale zero c f = trans (*-comm c 0#) (zeroˡ c)
  Σ-scale (suc n) c f = trans (distribˡ c (f zero) _) (+-cong refl (Σ-scale n c (λ i → f (suc i))))

  Σ-scaleʳ : ∀ n c (f : Fin n → Carrier) → Σ n f * c ≈ Σ n (λ i → f i * c)
  Σ-scaleʳ n c f = trans (*-comm _ c) (trans (Σ-scale n c f) (Σ-cong n (λ i → *-comm c (f i))))

  Σ-swap : ∀ m n (f : Fin m → Fin n → Carrier) → Σ m (λ i → Σ n (f i)) ≈ Σ n (λ j → Σ m (λ i → f i j))
  Σ-swap zero n f = sym (Σ-0 n)
  Σ-swap (suc m) n f = trans (+-cong refl (Σ-swap m n (λ i → f (suc i)))) (sym (Σ-+ n (f zero) _))

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
  *Mv-+ {n = n} A x y i = trans (Σ-cong n (λ l → distribˡ (A i l) (x l) (y l)))
    (Σ-+ n (λ l → A i l * x l) (λ l → A i l * y l))

  *Mv-assoc : ∀ {m n k} (A : Mat m n) (B : Mat n k) (x : Vec k) → (A *M B) *Mv x ≈V A *Mv (B *Mv x)
  *Mv-assoc {n = n} {k} A B x i = begin
    Σ k (λ q → Σ n (λ l → A i l * B l q) * x q)
      ≈⟨ Σ-cong k (λ q → Σ-scaleʳ n (x q) (λ l → A i l * B l q)) ⟩
    Σ k (λ q → Σ n (λ l → (A i l * B l q) * x q))
      ≈⟨ Σ-swap k n (λ q l → (A i l * B l q) * x q) ⟩
    Σ n (λ l → Σ k (λ q → (A i l * B l q) * x q))
      ≈⟨ Σ-cong n (λ l → trans (Σ-cong k (λ q → *-assoc _ _ _)) (sym (Σ-scale k (A i l) (λ q → B l q * x q)))) ⟩
    Σ n (λ l → A i l * Σ k (λ q → B l q * x q)) ∎

  *M-assoc : ∀ {m n k l} (A : Mat m n) (B : Mat n k) (C : Mat k l) → (A *M B) *M C ≈M A *M (B *M C)
  *M-assoc A B C i j = *Mv-assoc A B (λ q → C q j) i

  ᵀ-*M : ∀ {m n k} (A : Mat m n) (B : Mat n k) → (A *M B) ᵀ ≈M B ᵀ *M A ᵀ
  ᵀ-*M {n = n} A B i j = Σ-cong n (λ l → *-comm (A j l) (B l i))

  ᵀ-ᵀ : ∀ {m n} (A : Mat m n) → (A ᵀ) ᵀ ≈M A
  ᵀ-ᵀ A i j = refl

  idM-*Mv : ∀ {n} (x : Vec n) → idM *Mv x ≈V x
  idM-*Mv {suc n} x zero = trans (+-cong (trans (*-comm 1# (x zero)) (*-identityʳ (x zero)))
    (Σ-cong n (λ l → zeroˡ (x (suc l))))) (trans (+-cong refl (Σ-0 n)) (+-identityʳ _))
  idM-*Mv {suc n} x (suc i) = trans (+-cong (zeroˡ (x zero)) (idM-*Mv (λ l → x (suc l)) i)) (+-identityˡ _)
