{-# OPTIONS --safe --without-K #-}

-- The probability monad's product and push-forward inside the s-finite measures (plan 05, item 44).  For probability
-- measures p, q (`Continuous/Monad`) and their embeddings `SFiniteIncl.ιPre`:
--   * `ι-⊗`: ιPre (p ⊗ᵖ q) ≈ᴹ ιPre p ⊗ ιPre q, relating `ExpectationProduct._⊗ᵖ_` (strength, then join) to
--     `Product.prodPre` (double strength);
--   * `ι-map`: ιPre (f ∗ p) ≈ᴹ f ∗ ιPre p;
--   * `ι-mass`: ιPre p has mass 1.
-- Route: through integrals, not definitions: `ι-map` is `SFiniteIncl.ι-nat`; `ι-⊗` from `SFiniteIncl.ι-mult` and
-- `ι-strong` (ιPre commutes with join and strength), `Product.∫-prod′` and `SFiniteStrong.∫ᴹ-σ`; `ι-mass` from
-- `Dominated.prob-mass`.
--   Skeleton: holes first.
module QBS.Continuous.ProdBridge where

open import QBS.Core
open import QBS.Limits using (_×Q_)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.Product using (module Product)
open import QBS.Inference.ExpectationProduct using (module ExpectationProduct)

module ProdBridge (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 1#)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; _≈ᴹ_; mapM; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Product (lemOf lem₁) using (prodPre)
  open ExpectationProduct lem₁ using (_⊗ᵖ_)

  ι-map : ∀ {X Y : QBS S} (f : Hom S X Y) (p : C.Pre X) → _≈ᴹ_ {Y} (ιPre {Y} (C.mapPre {X} {Y} f p)) (mapM {X} {Y} f (ιPre {X} p))
  ι-map = ?

  ι-mass : ∀ {X : QBS S} (p : C.Pre X) → ∫ᴹ {X} (ιPre {X} p) (constW {X} 1#) ≈ 1#
  ι-mass = ?

  ι-⊗ : ∀ {X Y : QBS S} (p : C.Pre X) (q : C.Pre Y) →
    _≈ᴹ_ {_×Q_ S X Y} (ιPre {_×Q_ S X Y} (p ⊗ᵖ q)) (prodPre {X} {Y} (ιPre {X} p) (ιPre {Y} q))
  ι-⊗ = ?
