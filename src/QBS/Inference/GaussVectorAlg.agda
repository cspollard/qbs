{-# OPTIONS --safe --without-K #-}

-- Ring-level lemmas on the identity matrix and matrix congruences (helper for `GaussVector`; plan 05 item 53).
--   * `idM-diag`, `idM-off`, `idM-sym`: the entries of `idM` (1 on the diagonal, 0 off it, symmetric);
--   * `*M-idM`: A I ≈ A; `*Mv-0`: A 0 ≈ 0; `*Mv-cong`, `*M-cong`: congruence of the products in their arguments;
--   * `var-cancel`, `unvar`: (v + m m) − m m ≈ v and (x − e e) + e e ≈ x, relating variance and second moment;
--     `second-moment` (x − e e ≈ w, e ≈ z give x ≈ w + z z); `≈M-trans`.
-- Route: induction on the indices for `idM-diag`, `idM-off`, `idM-sym`; `*M-idM` from `SgLinAlg.idM-*Mv` and `idM-sym`;
-- the rest is `SgLinAlg.Σ-cong` and ring identities.
module QBS.Inference.GaussVectorAlg where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality.Core using (_≢_; refl)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)

module GaussVectorAlg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R using (Carrier; _≈_; _+_; _*_; -_; 0#; 1#; sym; trans; +-cong; *-cong; *-comm; zeroʳ
    ; +-assoc; +-identityʳ; -‿inverseʳ; -‿inverseˡ) renaming (refl to rf)
  open SgLinAlg R

  idM-diag : ∀ {n} (i : Fin n) → idM i i ≈ 1#
  idM-diag zero = rf
  idM-diag (suc i) = idM-diag i

  idM-off : ∀ {n} (i j : Fin n) → i ≢ j → idM i j ≈ 0#
  idM-off zero zero ne with ne refl
  ... | ()
  idM-off zero (suc j) ne = rf
  idM-off (suc i) zero ne = rf
  idM-off (suc i) (suc j) ne = idM-off i j (λ { refl → ne refl })

  idM-sym : ∀ {n} (i j : Fin n) → idM i j ≈ idM j i
  idM-sym zero zero = rf
  idM-sym zero (suc j) = rf
  idM-sym (suc i) zero = rf
  idM-sym (suc i) (suc j) = idM-sym i j

  *M-idM : ∀ {m n} (M : Mat m n) → M *M idM ≈M M
  *M-idM {n = n} M i j = trans (Σ-cong n (λ l → trans (*-cong rf (idM-sym l j)) (*-comm (M i l) (idM j l))))
    (idM-*Mv (M i) j)

  *Mv-0 : ∀ {m n} (M : Mat m n) → M *Mv (λ _ → 0#) ≈V (λ _ → 0#)
  *Mv-0 {n = n} M i = trans (Σ-cong n (λ l → zeroʳ (M i l))) (Σ-0 n)

  *Mv-cong : ∀ {m n} (M : Mat m n) {x y : Vec n} → x ≈V y → M *Mv x ≈V M *Mv y
  *Mv-cong {n = n} M e i = Σ-cong n (λ l → *-cong rf (e l))

  *M-cong : ∀ {m n k} {M M′ : Mat m n} {N N′ : Mat n k} → M ≈M M′ → N ≈M N′ → M *M N ≈M M′ *M N′
  *M-cong {n = n} e e′ i j = Σ-cong n (λ l → *-cong (e i l) (e′ l j))

  var-cancel : ∀ v m → (v + m * m) + - (m * m) ≈ v
  var-cancel v m = trans (+-assoc v _ _) (trans (+-cong rf (-‿inverseʳ _)) (+-identityʳ v))

  unvar : ∀ x e → (x + - (e * e)) + e * e ≈ x
  unvar x e = trans (+-assoc x _ _) (trans (+-cong rf (-‿inverseˡ _)) (+-identityʳ x))

  second-moment : ∀ {x e w z} → x + - (e * e) ≈ w → e ≈ z → x ≈ w + z * z
  second-moment {x} {e} {w} {z} hv he = trans (sym (unvar x e)) (+-cong hv (*-cong he he))

  ≈M-trans : ∀ {m n} {A B C : Mat m n} → A ≈M B → B ≈M C → A ≈M C
  ≈M-trans e e′ i j = trans (e i j) (e′ i j)
