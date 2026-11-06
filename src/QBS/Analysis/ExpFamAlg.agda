{-# OPTIONS --safe --without-K #-}

-- Commutative ring algebra for exponential families (plan ExpFam, item 56).  Model-independent algebra over any
-- commutative ring (instantiated at `Signed.signedRing` for continuous families and with natural powers):
--   * `_++F_`: concatenation of families indexed by `Fin m` and `Fin n`;
--   * `Σ-concat`: finite sum over a concatenated family splits into the sum of the two parts;
--   * `sumV T = λ j → Σ N (λ i → T i j)`, the vector sum of a sample `T : Fin N → Vec k`, with `sumV-cong` and
--     `sumV-concat` (distributing over concatenation);
--   * `·-sumV`: ⟨η, Σᵢ Tᵢ⟩ ≈ Σᵢ ⟨η, Tᵢ⟩, dot product distributes over sample summation;
--   * `scaleA N A = Σ N (λ _ → A)`, the log-partition of N draws, with `scaleA-+`;
--   * `Param k = Vec k × ℕ`, natural conjugate parameters (χ, ν);
--   * `updateSample (χ, ν) T = (χ +V sumV T, ν + N)`, with `updateSample-sequential`: updating on T₁ then on T₂
--     equals updating on their concatenation `T₁ ++F T₂`;
--   * `ExpFamNat`: natural-exponent counterpart for discrete exponential families (`Inference/ExpFamily`).
-- Route: induction on m for `Σ-concat` and `scaleA-+`; `·-sumV` by `Σ-scale` and `Σ-swap` from `Analysis/SgLinAlg`;
-- `updateSample-sequential` from `sumV-concat` and associativity of vector and natural addition.
module QBS.Analysis.ExpFamAlg where

open import Level using (Level)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.Nat.Base as Nat
open Nat using (ℕ; zero; suc)
import Data.Nat.Properties as NatProp
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Analysis.SgLinAlg using (module SgLinAlg)

infixr 5 _++F_
_++F_ : ∀ {ℓ : Level} {m n : ℕ} {X : Set ℓ} → (Fin m → X) → (Fin n → X) → Fin (m Nat.+ n) → X
(_++F_ {ℓ} {zero} {n} {X} f g) i = g i
(_++F_ {ℓ} {suc m} {n} {X} f g) zero = f zero
(_++F_ {ℓ} {suc m} {n} {X} f g) (suc i) = (_++F_ {ℓ} {m} {n} {X} (λ j → f (suc j)) g) i

module ExpFamAlg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R using (Carrier; _≈_; _+_; _*_; 0#; 1#; +-cong; +-assoc; +-identityˡ; sym; trans; refl; setoid)
  open SgLinAlg R using (Vec; _≈V_; _+V_; _·_; Σ; Σ-cong; Σ-scale; Σ-swap)
  open import Relation.Binary.Reasoning.Setoid setoid

  Σ-concat : ∀ m n (f : Fin m → Carrier) (g : Fin n → Carrier) →
    Σ (m Nat.+ n) (f ++F g) ≈ Σ m f + Σ n g
  Σ-concat zero n f g = sym (+-identityˡ (Σ n g))
  Σ-concat (suc m) n f g = trans (+-cong refl (Σ-concat m n (λ j → f (suc j)) g))
    (sym (+-assoc (f zero) _ _))

  sumV : ∀ {N k} → (Fin N → Vec k) → Vec k
  sumV {N} T j = Σ N (λ i → T i j)

  sumV-cong : ∀ {N k} {T U : Fin N → Vec k} → (∀ i → T i ≈V U i) → sumV T ≈V sumV U
  sumV-cong {N} eq j = Σ-cong N (λ i → eq i j)

  sumV-concat : ∀ {m n k} (T₁ : Fin m → Vec k) (T₂ : Fin n → Vec k) →
    sumV (T₁ ++F T₂) ≈V sumV T₁ +V sumV T₂
  sumV-concat {zero} T₁ T₂ j = sym (+-identityˡ (sumV T₂ j))
  sumV-concat {suc m} T₁ T₂ j = trans (+-cong refl (sumV-concat (λ l → T₁ (suc l)) T₂ j))
    (sym (+-assoc (T₁ zero j) _ _))

  ·-sumV : ∀ {N k} (η : Vec k) (T : Fin N → Vec k) → η · sumV T ≈ Σ N (λ i → η · T i)
  ·-sumV {N} {k} η T = begin
    Σ k (λ j → η j * Σ N (λ i → T i j))
      ≈⟨ Σ-cong k (λ j → Σ-scale N (η j) (λ i → T i j)) ⟩
    Σ k (λ j → Σ N (λ i → η j * T i j))
      ≈⟨ Σ-swap k N (λ j i → η j * T i j) ⟩
    Σ N (λ i → Σ k (λ j → η j * T i j)) ∎

  scaleA : ℕ → Carrier → Carrier
  scaleA N A = Σ N (λ _ → A)

  scaleA-cong : ∀ N {A B} → A ≈ B → scaleA N A ≈ scaleA N B
  scaleA-cong N eq = Σ-cong N (λ _ → eq)

  scaleA-+ : ∀ m n A → scaleA (m Nat.+ n) A ≈ scaleA m A + scaleA n A
  scaleA-+ zero n A = sym (+-identityˡ (scaleA n A))
  scaleA-+ (suc m) n A = trans (+-cong refl (scaleA-+ m n A)) (sym (+-assoc A _ _))

  Param : ℕ → Set c
  Param k = Vec k × ℕ

  infix 4 _≈P_
  _≈P_ : ∀ {k} → Param k → Param k → Set ℓ
  (χ₁ , ν₁) ≈P (χ₂ , ν₂) = (χ₁ ≈V χ₂) × (ν₁ ≡ ν₂)

  ≈P-refl : ∀ {k} {p : Param k} → p ≈P p
  ≈P-refl = (λ _ → refl) , ≡.refl

  updateSample : ∀ {N k} → Param k → (Fin N → Vec k) → Param k
  updateSample {N} (χ , ν) T = (χ +V sumV T , ν Nat.+ N)

  updateSample-cong : ∀ {N k} {p q : Param k} {T U : Fin N → Vec k} →
    p ≈P q → (∀ i → T i ≈V U i) → updateSample p T ≈P updateSample q U
  updateSample-cong {N} (hχ , ≡.refl) hT =
    (λ j → +-cong (hχ j) (sumV-cong hT j)) , ≡.refl

  updateSample-sequential : ∀ {m n k} (p : Param k) (T₁ : Fin m → Vec k) (T₂ : Fin n → Vec k) →
    updateSample (updateSample p T₁) T₂ ≈P updateSample p (T₁ ++F T₂)
  updateSample-sequential {m} {n} {k} (χ , ν) T₁ T₂ = hχ , hν
    where
      hχ : ((χ +V sumV T₁) +V sumV T₂) ≈V (χ +V sumV (T₁ ++F T₂))
      hχ j = trans (+-assoc (χ j) (sumV T₁ j) (sumV T₂ j))
        (+-cong refl (sym (sumV-concat T₁ T₂ j)))

      hν : (ν Nat.+ m) Nat.+ n ≡ ν Nat.+ (m Nat.+ n)
      hν = NatProp.+-assoc ν m n

module ExpFamNat where
  open Nat using (_+_)
  open import Data.Nat.Properties using (+-assoc)

  length-++ : ∀ {X : Set} (xs ys : List X) → length (xs ++ ys) ≡ length xs + length ys
  length-++ [] ys = ≡.refl
  length-++ (x ∷ xs) ys = ≡.cong suc (length-++ xs ys)

  Vecℕ : ℕ → Set
  Vecℕ k = Fin k → ℕ

  _+Vℕ_ : ∀ {k} → Vecℕ k → Vecℕ k → Vecℕ k
  (x +Vℕ y) j = x j + y j

  Σℕ : ∀ n → (Fin n → ℕ) → ℕ
  Σℕ zero f = 0
  Σℕ (suc n) f = f zero + Σℕ n (λ i → f (suc i))

  sumVℕ : ∀ {N k} → (Fin N → Vecℕ k) → Vecℕ k
  sumVℕ {N} T j = Σℕ N (λ i → T i j)

  Σℕ-concat : ∀ m n (f : Fin m → ℕ) (g : Fin n → ℕ) →
    Σℕ (m + n) (f ++F g) ≡ Σℕ m f + Σℕ n g
  Σℕ-concat zero n f g = ≡.refl
  Σℕ-concat (suc m) n f g = ≡.trans (≡.cong (f zero +_) (Σℕ-concat m n (λ j → f (suc j)) g))
    (≡.sym (+-assoc (f zero) _ _))

  sumVℕ-concat : ∀ {m n k} (T₁ : Fin m → Vecℕ k) (T₂ : Fin n → Vecℕ k) →
    ∀ j → sumVℕ (T₁ ++F T₂) j ≡ sumVℕ T₁ j + sumVℕ T₂ j
  sumVℕ-concat {zero} T₁ T₂ j = ≡.refl
  sumVℕ-concat {suc m} T₁ T₂ j = ≡.trans (≡.cong (T₁ zero j +_) (sumVℕ-concat (λ l → T₁ (suc l)) T₂ j))
    (≡.sym (+-assoc (T₁ zero j) _ _))

  sumList : ∀ {k} {X : Set} → (X → Vecℕ k) → List X → Vecℕ k
  sumList T [] j = 0
  sumList T (x ∷ xs) j = T x j + sumList T xs j

  sumList-++ : ∀ {k} {X : Set} (T : X → Vecℕ k) (xs ys : List X) →
    ∀ j → sumList T (xs ++ ys) j ≡ sumList T xs j + sumList T ys j
  sumList-++ T [] ys j = ≡.refl
  sumList-++ T (x ∷ xs) ys j = ≡.trans (≡.cong (T x j +_) (sumList-++ T xs ys j))
    (≡.sym (+-assoc (T x j) _ _))

  Paramℕ : ℕ → Set
  Paramℕ k = Vecℕ k × ℕ

  infix 4 _≈Pℕ_
  _≈Pℕ_ : ∀ {k} → Paramℕ k → Paramℕ k → Set
  (χ₁ , ν₁) ≈Pℕ (χ₂ , ν₂) = (∀ j → χ₁ j ≡ χ₂ j) × (ν₁ ≡ ν₂)

  updateList : ∀ {k} {X : Set} → Paramℕ k → (X → Vecℕ k) → List X → Paramℕ k
  updateList (χ , ν) T xs = (χ +Vℕ sumList T xs , ν + length xs)

  updateList-++ : ∀ {k} {X : Set} (p : Paramℕ k) (T : X → Vecℕ k) (xs ys : List X) →
    updateList (updateList p T xs) T ys ≈Pℕ updateList p T (xs ++ ys)
  updateList-++ (χ , ν) T xs ys = hχ , hν
    where
      hχ : ∀ j → ((χ +Vℕ sumList T xs) +Vℕ sumList T ys) j ≡ (χ +Vℕ sumList T (xs ++ ys)) j
      hχ j = ≡.trans (+-assoc (χ j) (sumList T xs j) (sumList T ys j))
        (≡.cong (χ j +_) (≡.sym (sumList-++ T xs ys j)))

      hν : (ν + length xs) + length ys ≡ ν + length (xs ++ ys)
      hν = ≡.trans (+-assoc ν (length xs) (length ys))
        (≡.cong (ν +_) (≡.sym (length-++ xs ys)))
