{-# OPTIONS --safe --without-K #-}

-- Finite products of probability measures (plan 05, item 53a; enabler for `Inference/GaussVector`).  For probability
-- measures pᵢ on Xᵢ (`Continuous/Monad`):
--   * `prodPⁿ n Xs p = p₀ ⊗ᵖ (p₁ ⊗ᵖ (… ⊗ᵖ δ))`, a probability measure on `FinProd.ΠQ n Xs`, by the recursion of
--     `FinProd.prodⁿ` with `ExpectationProduct._⊗ᵖ_`;
--   * its embedding is the s-finite product of the embeddings (`ι-prodⁿ`);
--   * the coordinate projections are an iid family under p^{⊗n} with the law of p (`proj-iid`, `Continuous/IID`), so
--     every probability law has a canonical iid family of every length.
-- Route: `ι-prodⁿ` by induction on n, with `ProdBridge.ι-⊗` and `Product.prod-cong`, at 0 the embedding of a point
-- mass; `proj-iid`: the tuple of the projections is the identity pointwise (`tuple-proj`, by induction on n), so
-- its law is the embedding (`ProdMap.mapM-ext`, `∫ᴹ-map`), then `ι-prodⁿ`.
--   Skeleton: holes first.
module QBS.Continuous.FinProdProb where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.Core
open import QBS.Limits using (1Q)
open import Data.Unit.Polymorphic.Base using (tt)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.ExpectationProduct using (module ExpectationProduct)

module FinProdProb (lem₁ : LEM₁) where
  open SFinite (lemOf lem₁) using (_≈ᴹ_; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ)
  open IID lem₁ using (IID)
  open ExpectationProduct lem₁ using (_⊗ᵖ_)
  open QBS
  open Hom

  -- p₀ ⊗ (p₁ ⊗ (… ⊗ δ))
  prodPⁿ : ∀ n Xs → (∀ i → C.Pre (Xs i)) → C.Pre (ΠQ n Xs)
  prodPⁿ zero Xs p = C.ηPre {1Q S} tt
  prodPⁿ (suc n) Xs p = p zero ⊗ᵖ prodPⁿ n (λ j → Xs (suc j)) (λ j → p (suc j))

  ι-prodⁿ : ∀ n Xs (p : ∀ i → C.Pre (Xs i)) →
    _≈ᴹ_ {ΠQ n Xs} (ιPre {ΠQ n Xs} (prodPⁿ n Xs p)) (prodⁿ n Xs (λ i → ιPre {Xs i} (p i)))
  ι-prodⁿ = ?

  -- the tuple of the projections is the identity
  tuple-proj : ∀ n Xs (x : ∣ ΠQ n Xs ∣) →
    Setoid._≈_ (Carrier (ΠQ n Xs)) (map (tupleQ n Xs (projQ n Xs)) ⟨$⟩ x) x
  tuple-proj = ?

  -- the coordinates of p^{⊗n} are iid with law p
  proj-iid : ∀ {Y : QBS S} (p : C.Pre Y) n →
    IID (prodPⁿ n (λ _ → Y) (λ _ → p)) (ιPre {Y} p) n (projQ n (λ _ → Y))
  proj-iid = ?
