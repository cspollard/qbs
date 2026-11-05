{-# OPTIONS --safe --without-K #-}

-- Finite products of quasi-Borel spaces and of s-finite measures (plan 05, item 43).  For a family `Xs : Fin n → QBS S`:
--   * `ΠQ n Xs`, the product X₀ × (X₁ × (… × 1)), by recursion on n (the homogeneous Xⁿ is `ΠQ n (λ _ → X)`), with
--     the projections `projQ` and tupling `tupleQ` (`proj-tuple`);
--   * `prodT n Xs g = (x₀, …) ↦ ∏ᵢ gᵢ(xᵢ)`, the product of tests, and `∏ⁿ`, the product of n values;
--   * `prodⁿ n Xs μ = μ₀ ⊗ (μ₁ ⊗ (… ⊗ δ))`, the n-fold product measure (`Product.prodPre`, ending in the Dirac measure at
--     the point of 1), with `∫-rectⁿ` (∫ ∏ᵢ gᵢ(xᵢ) d⊗ⁿ ≈ ∏ᵢ ∫ gᵢ dμᵢ), `margⁿ` (for probability measures the i-th
--     coordinate has law μᵢ) and `prodⁿ-cong`.
-- Route: induction on n; `∫-rectⁿ` from `Product.∫-rect` and `SFinite.∫ᴹ-η`, `margⁿ` from `∫ᴹ-map`, `Product.marg₁`/`marg₂`
-- and the masses, `prodⁿ-cong` from `Product.prod-cong`.
--   Skeleton: holes first.
module QBS.Continuous.FinProd where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.Bundles using (Setoid)
open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ; 1Q; !Q)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Product using (module Product)

module FinProd (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; _≈ᴹ_; mapM; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Product (lemOf lem₁) using (prodPre)
  open QBS
  open Hom

  -- X₀ × (X₁ × (… × 1))
  ΠQ : ∀ n → (Fin n → QBS S) → QBS S
  ΠQ zero Xs = 1Q S
  ΠQ (suc n) Xs = _×Q_ S (Xs zero) (ΠQ n (λ i → Xs (suc i)))

  projQ : ∀ n Xs (i : Fin n) → Hom S (ΠQ n Xs) (Xs i)
  projQ (suc n) Xs zero = fstQ S
  projQ (suc n) Xs (suc i) = _∘H_ S (projQ n (λ j → Xs (suc j)) i) (sndQ S)

  tupleQ : ∀ {Z : QBS S} n Xs → (∀ i → Hom S Z (Xs i)) → Hom S Z (ΠQ n Xs)
  tupleQ zero Xs f = !Q S
  tupleQ (suc n) Xs f = pairQ S (f zero) (tupleQ n (λ j → Xs (suc j)) (λ j → f (suc j)))

  proj-tuple : ∀ {Z : QBS S} n Xs (f : ∀ i → Hom S Z (Xs i)) i z →
    Setoid._≈_ (Carrier (Xs i)) (map (projQ n Xs i) ⟨$⟩ (map (tupleQ n Xs f) ⟨$⟩ z)) (map (f i) ⟨$⟩ z)
  proj-tuple = ?

  -- ∏ᵢ gᵢ(xᵢ), and the product of n values
  prodT : ∀ n Xs → (∀ i → Hom S (Xs i) WQ) → Hom S (ΠQ n Xs) WQ
  prodT zero Xs g = constW {1Q S} 1#
  prodT (suc n) Xs g = mulH {ΠQ (suc n) Xs} (_∘H_ S (g zero) (fstQ S))
    (_∘H_ S (prodT n (λ j → Xs (suc j)) (λ j → g (suc j))) (sndQ S))

  ∏ⁿ : ∀ n → (Fin n → ∣A∣) → ∣A∣
  ∏ⁿ zero a = 1#
  ∏ⁿ (suc n) a = a zero * ∏ⁿ n (λ j → a (suc j))

  -- μ₀ ⊗ (μ₁ ⊗ (… ⊗ δ))
  prodⁿ : ∀ n Xs → (∀ i → C.Pre (XW (Xs i))) → C.Pre (XW (ΠQ n Xs))
  prodⁿ zero Xs μ = C.ηPre {XW (1Q S)} (1# , tt)
  prodⁿ (suc n) Xs μ = prodPre {Xs zero} {ΠQ n (λ j → Xs (suc j))} (μ zero) (prodⁿ n (λ j → Xs (suc j)) (λ j → μ (suc j)))

  ∫-rectⁿ : ∀ n Xs μ g → ∫ᴹ {ΠQ n Xs} (prodⁿ n Xs μ) (prodT n Xs g) ≈ ∏ⁿ n (λ i → ∫ᴹ {Xs i} (μ i) (g i))
  ∫-rectⁿ = ?

  -- for probability measures, the i-th coordinate has law μᵢ
  margⁿ : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) →
    ∀ i → _≈ᴹ_ {Xs i} (mapM {ΠQ n Xs} {Xs i} (projQ n Xs i) (prodⁿ n Xs μ)) (μ i)
  margⁿ = ?

  prodⁿ-cong : ∀ n Xs μ ν → (∀ i → _≈ᴹ_ {Xs i} (μ i) (ν i)) → _≈ᴹ_ {ΠQ n Xs} (prodⁿ n Xs μ) (prodⁿ n Xs ν)
  prodⁿ-cong = ?
