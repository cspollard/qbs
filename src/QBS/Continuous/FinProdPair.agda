{-# OPTIONS --safe --without-K #-}

-- Two-coordinate marginals of the n-fold product measure (helper for `Independence.Indep-pair`).
--   * `fst-pair`: pushing s ⊗ t along (x, y) ↦ (x, g y) gives s ⊗ g₊t;
--   * `pairⁿ`: for probability measures μᵢ and i ≠ j, the pair of coordinates (xᵢ, xⱼ) of `FinProd.prodⁿ` has law μᵢ ⊗ μⱼ.
-- Route: induction on n through the four cases on (i, j): (0, j+1) is `fst-pair` and `FinProd.margⁿ`; (i+1, 0) swaps
-- (`ProdMap.swapM`); (i+1, j+1) pushes forward along snd (`FinProd.snd-law`) and recurses.
module QBS.Continuous.FinProdPair where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (_≢_; refl; cong)
open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)

module FinProdPair (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#) renaming (refl to refl≈; trans to trans≈; sym to sym≈)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; _≈ᴹ_; mapM; module C)
  open Product (lemOf lem₁) using (prodPre; prod-cong)
  open ProdMap (lemOf lem₁) using (mapM-id; mapM-comp; mapM-cong; mapM-ext; _×H_; map-prod; swapQ; swapM)
  open FinProd lem₁ using (ΠQ; projQ; prodⁿ; margⁿ; mass-prodⁿ; snd-law; tl; tlμ)
  open QBS
  open Hom

  -- (x, y) ↦ (x, g y)
  fst-pair : ∀ {X Y Z : QBS S} (g : Hom S Y Z) (s : C.Pre (XW X)) (t : C.Pre (XW Y)) →
    _≈ᴹ_ {_×Q_ S X Z} (mapM {_×Q_ S X Y} {_×Q_ S X Z} (pairQ S (fstQ S) (_∘H_ S g (sndQ S))) (prodPre {X} {Y} s t))
      (prodPre {X} {Z} s (mapM {Y} {Z} g t))
  fst-pair {X} {Y} {Z} g s t = λ h → trans≈ (mapM-ext {_×Q_ S X Y} {_×Q_ S X Z} (pairQ S (fstQ S) (_∘H_ S g (sndQ S)))
      (_×H_ {X} {Y} {X} {Z} (idH S) g) (prodPre {X} {Y} s t) (λ p → Setoid.refl (Carrier (_×Q_ S X Z))) h)
    (trans≈ (map-prod {X} {Y} {X} {Z} (idH S) g s t h) (prod-cong {X} {Z} (mapM-id {X} s) (λ k → refl≈) h))

  -- the pair of coordinates (xᵢ, xⱼ), as a space and as a map
  P2 : ∀ n (Xs : Fin n → QBS S) (i j : Fin n) → QBS S
  P2 n Xs i j = _×Q_ S (Xs i) (Xs j)

  q2 : ∀ n (Xs : Fin n → QBS S) (i j : Fin n) → Hom S (ΠQ n Xs) (P2 n Xs i j)
  q2 n Xs i j = pairQ S (projQ n Xs i) (projQ n Xs j)

  -- the law of the pair, as a statement about probability measures μ
  Law2 : ∀ n (Xs : Fin n → QBS S) (i j : Fin n) → (∀ k → C.Pre (XW (Xs k))) → Set₁
  Law2 n Xs i j μ = _≈ᴹ_ {P2 n Xs i j} (mapM {ΠQ n Xs} {P2 n Xs i j} (q2 n Xs i j) (prodⁿ n Xs μ))
    (prodPre {Xs i} {Xs j} (μ i) (μ j))

  -- the pair (x₀, x_{j+1}) has law μ₀ ⊗ μ_{j+1}
  pair-zs : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) → ∀ j → Law2 (suc n) Xs zero (suc j) μ
  pair-zs n Xs μ h j f = trans≈
    (fst-pair {Xs zero} {ΠQ n (tl Xs)} {Xs (suc j)} (projQ n (tl Xs) j) (μ zero) (prodⁿ n (tl Xs) (tlμ μ)) f)
    (prod-cong {Xs zero} {Xs (suc j)} (λ k → refl≈) (margⁿ n (tl Xs) (tlμ μ) (λ k → h (suc k)) j) f)

  -- pushing forward along snd drops the first factor
  snd-M : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) →
    _≈ᴹ_ {ΠQ n (tl Xs)} (mapM {ΠQ (suc n) Xs} {ΠQ n (tl Xs)} (sndQ S) (prodⁿ (suc n) Xs μ)) (prodⁿ n (tl Xs) (tlμ μ))
  snd-M n Xs μ h f = trans≈ (∫ᴹ-map {ΠQ (suc n) Xs} {ΠQ n (tl Xs)} (sndQ S) (prodⁿ (suc n) Xs μ) f)
    (snd-law {Xs zero} {ΠQ n (tl Xs)} (μ zero) (prodⁿ n (tl Xs) (tlμ μ)) (h zero) f)

  -- the pair (x_{i+1}, x₀) has law μ_{i+1} ⊗ μ₀: swap the pair (x₀, x_{i+1})
  pair-sz : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) → ∀ i → Law2 (suc n) Xs (suc i) zero μ
  pair-sz n Xs μ h i f = trans≈
    (mapM-ext {ΠQ (suc n) Xs} {P2 (suc n) Xs (suc i) zero} (q2 (suc n) Xs (suc i) zero)
      (_∘H_ S (swapQ {Xs zero} {Xs (suc i)}) (q2 (suc n) Xs zero (suc i))) (prodⁿ (suc n) Xs μ)
      (λ p → Setoid.refl (Carrier (P2 (suc n) Xs (suc i) zero))) f)
    (trans≈ (sym≈ (mapM-comp {ΠQ (suc n) Xs} {P2 (suc n) Xs zero (suc i)} {P2 (suc n) Xs (suc i) zero}
      (q2 (suc n) Xs zero (suc i)) (swapQ {Xs zero} {Xs (suc i)}) (prodⁿ (suc n) Xs μ) f))
    (trans≈ (mapM-cong {P2 (suc n) Xs zero (suc i)} {P2 (suc n) Xs (suc i) zero} (swapQ {Xs zero} {Xs (suc i)})
      (pair-zs n Xs μ h i) f) (swapM {Xs zero} {Xs (suc i)} (μ zero) (μ (suc i)) f)))

  -- the pair (x_{i+1}, x_{j+1}): push forward along snd and recurse
  pair-ss : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) → ∀ i j →
    Law2 n (tl Xs) i j (tlμ μ) → Law2 (suc n) Xs (suc i) (suc j) μ
  pair-ss n Xs μ h i j ih f = trans≈
    (mapM-ext {ΠQ (suc n) Xs} {P2 (suc n) Xs (suc i) (suc j)} (q2 (suc n) Xs (suc i) (suc j))
      (_∘H_ S (q2 n (tl Xs) i j) (sndQ S)) (prodⁿ (suc n) Xs μ) (λ p → Setoid.refl (Carrier (P2 (suc n) Xs (suc i) (suc j)))) f)
    (trans≈ (sym≈ (mapM-comp {ΠQ (suc n) Xs} {ΠQ n (tl Xs)} {P2 (suc n) Xs (suc i) (suc j)} (sndQ S) (q2 n (tl Xs) i j)
      (prodⁿ (suc n) Xs μ) f))
    (trans≈ (mapM-cong {ΠQ n (tl Xs)} {P2 (suc n) Xs (suc i) (suc j)} (q2 n (tl Xs) i j) (snd-M n Xs μ h) f) (ih f)))

  pairⁿ : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) → ∀ i j → i ≢ j → Law2 n Xs i j μ
  pairⁿ (suc n) Xs μ h zero zero ne = ⊥-elim (ne refl)
  pairⁿ (suc n) Xs μ h zero (suc j) ne = pair-zs n Xs μ h j
  pairⁿ (suc n) Xs μ h (suc i) zero ne = pair-sz n Xs μ h i
  pairⁿ (suc n) Xs μ h (suc i) (suc j) ne =
    pair-ss n Xs μ h i j (pairⁿ n (tl Xs) (tlμ μ) (λ k → h (suc k)) i j (λ e → ne (cong suc e)))
