{-# OPTIONS --safe --without-K #-}

-- Finite products of probability measures (the probability-monad counterpart of `FinProd.prodⁿ`; enabler for `Inference/GaussVector`).  For probability
-- measures pᵢ on Xᵢ (`Continuous/Monad`):
--   * `prodPⁿ n Xs p = p₀ ⊗ᵖ (p₁ ⊗ᵖ (… ⊗ᵖ δ))`, a probability measure on `FinProd.ΠQ n Xs`, by the recursion of
--     `FinProd.prodⁿ` with `ExpectationProduct._⊗ᵖ_`;
--   * its embedding is the s-finite product of the embeddings (`ι-prodⁿ`);
--   * the coordinate projections are an iid family under p^{⊗n} with the law of p (`proj-iid`, `Continuous/IID`), so
--     every probability law has a canonical iid family of every length.
-- Route: `ι-prodⁿ` by induction on n, with `ProdBridge.ι-⊗` and `Product.prod-cong`, at 0 the embedding of a point
-- mass; `proj-iid`: the tuple of the projections is the identity pointwise (`tuple-proj`, from `tuple-∘` by induction on n), so
-- its law is the embedding (`ProdMap.mapM-ext`, `∫ᴹ-map`), then `ι-prodⁿ`.
module QBS.Continuous.FinProdProb where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.Core
open import QBS.Limits using (1Q; sndQ)
open import Data.Unit.Polymorphic.Base using (tt)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.ExpectationProduct using (module ExpectationProduct)

module FinProdProb (lem₁ : LEM₁) where
  open SFinite (lemOf lem₁) using (_≈ᴹ_; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ι-unit)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ; tl)
  open ProdMap (lemOf lem₁) using (mapM-ext)
  open Product (lemOf lem₁) using (prod-cong)
  open SFinite (lemOf lem₁) using (∫ᴹ-map)
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (refl; trans)
  open ProdBridge lem₁ using (ι-⊗)
  open IID lem₁ using (≈ᴹ-trans)
  open IID lem₁ using (IID)
  open ExpectationProduct lem₁ using (_⊗ᵖ_)
  open QBS
  open Hom

  tlp : ∀ {n} {Xs : Fin (suc n) → QBS S} → (∀ i → C.Pre (Xs i)) → ∀ j → C.Pre (tl Xs j)
  tlp p j = p (suc j)

  -- p₀ ⊗ (p₁ ⊗ (… ⊗ δ))
  prodPⁿ : ∀ n Xs → (∀ i → C.Pre (Xs i)) → C.Pre (ΠQ n Xs)
  prodPⁿ zero Xs p = C.ηPre {1Q S} tt
  prodPⁿ (suc n) Xs p = p zero ⊗ᵖ prodPⁿ n (λ j → Xs (suc j)) (λ j → p (suc j))

  ι-prodⁿ : ∀ n Xs (p : ∀ i → C.Pre (Xs i)) →
    _≈ᴹ_ {ΠQ n Xs} (ιPre {ΠQ n Xs} (prodPⁿ n Xs p)) (prodⁿ n Xs (λ i → ιPre {Xs i} (p i)))
  ι-prodⁿ zero Xs p h = ι-unit {1Q S} tt h
  ι-prodⁿ (suc n) Xs p = ≈ᴹ-trans {ΠQ (suc n) Xs} (ι-⊗ (p zero) (prodPⁿ n (tl Xs) (tlp p)))
    (prod-cong {Xs zero} {ΠQ n (tl Xs)} (λ _ → refl) (ι-prodⁿ n (tl Xs) (tlp p)))

  -- the tuple of the projections of g is g
  tuple-∘ : ∀ {Z : QBS S} n Xs (g : Hom S Z (ΠQ n Xs)) (z : ∣ Z ∣) →
    Setoid._≈_ (Carrier (ΠQ n Xs)) (map (tupleQ n Xs (λ i → _∘H_ S (projQ n Xs i) g)) ⟨$⟩ z) (map g ⟨$⟩ z)
  tuple-∘ zero Xs g z = Setoid.refl (Carrier (ΠQ zero Xs))
  tuple-∘ {Z} (suc n) Xs g z = Setoid.refl (Carrier (Xs zero)) , tuple-∘ {Z} n (tl Xs) (_∘H_ S (sndQ S) g) z

  -- the tuple of the projections is the identity
  tuple-proj : ∀ n Xs (x : ∣ ΠQ n Xs ∣) →
    Setoid._≈_ (Carrier (ΠQ n Xs)) (map (tupleQ n Xs (projQ n Xs)) ⟨$⟩ x) x
  tuple-proj n Xs x = tuple-∘ {ΠQ n Xs} n Xs (idH S {ΠQ n Xs}) x

  -- the coordinates of p^{⊗n} are iid with law p
  proj-iid : ∀ {Y : QBS S} (p : C.Pre Y) n →
    IID (prodPⁿ n (λ _ → Y) (λ _ → p)) (ιPre {Y} p) n (projQ n (λ _ → Y))
  proj-iid {Y} p n f = trans
    (mapM-ext {ΠQ n (λ _ → Y)} {ΠQ n (λ _ → Y)} (tupleQ n (λ _ → Y) (projQ n (λ _ → Y))) (idH S {ΠQ n (λ _ → Y)})
      (ιPre {ΠQ n (λ _ → Y)} (prodPⁿ n (λ _ → Y) (λ _ → p))) (tuple-proj n (λ _ → Y)) f)
    (trans (∫ᴹ-map {ΠQ n (λ _ → Y)} {ΠQ n (λ _ → Y)} (idH S {ΠQ n (λ _ → Y)})
      (ιPre {ΠQ n (λ _ → Y)} (prodPⁿ n (λ _ → Y) (λ _ → p))) f)
      (trans refl (ι-prodⁿ n (λ _ → Y) (λ _ → p) f)))
