{-# OPTIONS --safe --without-K #-}

-- Finite products of quasi-Borel spaces and of s-finite measures (n-fold products and their marginals).  For a family `Xs : Fin n → QBS S`:
--   * `ΠQ n Xs`, the product X₀ × (X₁ × (… × 1)), by recursion on n (the homogeneous Xⁿ is `ΠQ n (λ _ → X)`), with
--     the projections `projQ` and tupling `tupleQ` (`proj-tuple`);
--   * `prodT n Xs g = (x₀, …) ↦ ∏ᵢ gᵢ(xᵢ)`, the product of tests, and `∏ⁿ`, the product of n values;
--   * `prodⁿ n Xs μ = μ₀ ⊗ (μ₁ ⊗ (… ⊗ δ))`, the n-fold product measure (`Product.prodPre`, ending in the Dirac measure at
--     the point of 1), with `∫-rectⁿ` (∫ ∏ᵢ gᵢ(xᵢ) d⊗ⁿ ≈ ∏ᵢ ∫ gᵢ dμᵢ), `margⁿ` (for probability measures the i-th
--     coordinate has law μᵢ) and `prodⁿ-cong`.
-- Route: induction on n; `∫-rectⁿ` from `Product.∫-rect` and `SFinite.∫ᴹ-η`, `margⁿ` from `∫ᴹ-map`, `Product.marg₁`/`marg₂`
-- and the masses, `prodⁿ-cong` from `Product.prod-cong`.
module QBS.Continuous.FinProd where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (zero; suc)
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
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.Product using (module Product)

module FinProd (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; *-cong; *-identityˡ; *-identityʳ) renaming (Carrier to ∣A∣)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; ∫ᴹ-η; _≈ᴹ_; mapM; module C)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open SFiniteSum (lemOf lem₁) using (scalePre; ∫ᴹ-scale)
  open Product (lemOf lem₁) using (prodPre; ∫-rect; marg₁; marg₂; prod-cong)
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
  proj-tuple zero Xs f ()
  proj-tuple (suc n) Xs f zero z = Setoid.refl (Carrier (Xs zero))
  proj-tuple (suc n) Xs f (suc i) z = proj-tuple n (λ j → Xs (suc j)) (λ j → f (suc j)) i z

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
  ∫-rectⁿ zero Xs μ g = ∫ᴹ-η {1Q S} tt (constW {1Q S} 1#)
  ∫-rectⁿ (suc n) Xs μ g = trans (∫-rect {Xs zero} {ΠQ n (λ j → Xs (suc j))} (μ zero) (prodⁿ n (λ j → Xs (suc j)) (λ j → μ (suc j)))
    (g zero) (prodT n (λ j → Xs (suc j)) (λ j → g (suc j))))
    (*-cong refl (∫-rectⁿ n (λ j → Xs (suc j)) (λ j → μ (suc j)) (λ j → g (suc j))))

  -- the total mass of ⊗ⁿ of probability measures is 1
  mass-prodⁿ : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) → ∫ᴹ {ΠQ n Xs} (prodⁿ n Xs μ) (constW {ΠQ n Xs} 1#) ≈ 1#
  mass-prodⁿ zero Xs μ h = ∫ᴹ-η {1Q S} tt (constW {1Q S} 1#)
  mass-prodⁿ (suc n) Xs μ h = trans (∫ᴹ-cong {ΠQ (suc n) Xs} (prodⁿ (suc n) Xs μ) {constW {ΠQ (suc n) Xs} 1#}
    {mulH {ΠQ (suc n) Xs} (_∘H_ S (constW {Xs zero} 1#) (fstQ S)) (_∘H_ S (constW {ΠQ n (λ j → Xs (suc j))} 1#) (sndQ S))}
    (λ _ → sym (*-identityʳ _)))
    (trans (∫-rect {Xs zero} {ΠQ n (λ j → Xs (suc j))} (μ zero) (prodⁿ n (λ j → Xs (suc j)) (λ j → μ (suc j))) (constW {Xs zero} 1#)
      (constW {ΠQ n (λ j → Xs (suc j))} 1#))
      (trans (*-cong (h zero) (mass-prodⁿ n (λ j → Xs (suc j)) (λ j → μ (suc j)) (λ j → h (suc j)))) (*-identityˡ _)))

  -- probability factors drop out of the marginals
  fst-law : ∀ {X Y : QBS S} (s : C.Pre (XW X)) (t : C.Pre (XW Y)) → ∫ᴹ {Y} t (constW {Y} 1#) ≈ 1# →
    ∀ f → ∫ᴹ {_×Q_ S X Y} (prodPre {X} {Y} s t) (_∘H_ S f (fstQ S)) ≈ ∫ᴹ {X} s f
  fst-law {X} {Y} s t h f = trans (sym (∫ᴹ-map {_×Q_ S X Y} {X} (fstQ S) (prodPre {X} {Y} s t) f))
    (trans (marg₁ {X} {Y} s t f) (trans (∫ᴹ-scale {X} (∫ᴹ {Y} t (constW {Y} 1#)) s f) (trans (*-cong h refl) (*-identityˡ _))))

  snd-law : ∀ {X Y : QBS S} (s : C.Pre (XW X)) (t : C.Pre (XW Y)) → ∫ᴹ {X} s (constW {X} 1#) ≈ 1# →
    ∀ f → ∫ᴹ {_×Q_ S X Y} (prodPre {X} {Y} s t) (_∘H_ S f (sndQ S)) ≈ ∫ᴹ {Y} t f
  snd-law {X} {Y} s t h f = trans (sym (∫ᴹ-map {_×Q_ S X Y} {Y} (sndQ S) (prodPre {X} {Y} s t) f))
    (trans (marg₂ {X} {Y} s t f) (trans (∫ᴹ-scale {Y} (∫ᴹ {X} s (constW {X} 1#)) t f) (trans (*-cong h refl) (*-identityˡ _))))

  -- tails of a family of spaces and of measures
  tl : ∀ {n} → (Fin (suc n) → QBS S) → Fin n → QBS S
  tl Xs j = Xs (suc j)

  tlμ : ∀ {n} {Xs : Fin (suc n) → QBS S} → (∀ i → C.Pre (XW (Xs i))) → ∀ j → C.Pre (XW (tl Xs j))
  tlμ μ j = μ (suc j)

  -- for probability measures, the i-th coordinate has law μᵢ
  margⁿ : ∀ n Xs μ → (∀ i → ∫ᴹ {Xs i} (μ i) (constW {Xs i} 1#) ≈ 1#) →
    ∀ i → _≈ᴹ_ {Xs i} (mapM {ΠQ n Xs} {Xs i} (projQ n Xs i) (prodⁿ n Xs μ)) (μ i)
  margⁿ (suc n) Xs μ h zero f = trans (∫ᴹ-map {ΠQ (suc n) Xs} {Xs zero} (fstQ S) (prodⁿ (suc n) Xs μ) f)
    (fst-law {Xs zero} {ΠQ n (tl Xs)} (μ zero) (prodⁿ n (tl Xs) (tlμ μ)) (mass-prodⁿ n (tl Xs) (tlμ μ) (λ j → h (suc j))) f)
  margⁿ (suc n) Xs μ h (suc i) f = trans (∫ᴹ-map {ΠQ (suc n) Xs} {Xs (suc i)} (projQ (suc n) Xs (suc i)) (prodⁿ (suc n) Xs μ) f)
    (trans (snd-law {Xs zero} {ΠQ n (tl Xs)} (μ zero) (prodⁿ n (tl Xs) (tlμ μ)) (h zero) (_∘H_ S f (projQ n (tl Xs) i)))
    (trans (sym (∫ᴹ-map {ΠQ n (tl Xs)} {Xs (suc i)} (projQ n (tl Xs) i) (prodⁿ n (tl Xs) (tlμ μ)) f))
      (margⁿ n (tl Xs) (tlμ μ) (λ j → h (suc j)) i f)))

  prodⁿ-cong : ∀ n Xs μ ν → (∀ i → _≈ᴹ_ {Xs i} (μ i) (ν i)) → _≈ᴹ_ {ΠQ n Xs} (prodⁿ n Xs μ) (prodⁿ n Xs ν)
  prodⁿ-cong zero Xs μ ν e f = refl
  prodⁿ-cong (suc n) Xs μ ν e = prod-cong {Xs zero} {ΠQ n (λ j → Xs (suc j))} (e zero)
    (prodⁿ-cong n (λ j → Xs (suc j)) (λ j → μ (suc j)) (λ j → ν (suc j)) (λ j → e (suc j)))
