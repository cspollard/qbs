{-# OPTIONS --safe --without-K #-}

-- Exchangeable laws (plan 05, item 49).  For s-finite measures on Xⁿ⁺¹ (`FinProd.ΠQ`):
--   * `swapQ n k`, the transposition of coordinates k and k + 1 (adjacent transpositions generate all permutations);
--     `Exch n p`: p is invariant under every adjacent transposition; it respects ≈ᴹ (`Exch-≈`), and adjacent
--     coordinates of an exchangeable law have the same law (`Exch-marg`);
--   * product laws μ^{⊗(n+1)} are exchangeable, for any s-finite μ (`prodⁿ-exch`);
--   * mixtures of exchangeable laws are exchangeable (`Exch-mix`), so the data marginal of a conditionally iid model
--     under any prior is exchangeable (`condIID-exch`, the easy half of de Finetti);
--   * on a probability P, an iid family of random variables has an exchangeable joint law (`IID-exch`, `ExchRV`).
-- Route: `prodⁿ-exch` by induction on k: at k = 0 the law μ ⊗ (μ ⊗ r) is invariant under (x, (y, z)) ↦ (y, (x, z)),
-- by `Product.∫-prod`/`∫-prod′` on the nested integrals; at k + 1, `ProdMap.map-prod` (id × swap) and
-- `Product.prod-cong` with the induction hypothesis.  `Exch-mix` from `SFinite.∫ᴹ-join`, `∫ᴹ-map` and `∫ᴹ-cong`
-- pointwise in θ (`ProdMap.mapM-comp`, `TH` against `mapM`); `condIID-exch` is `Exch-mix` with `Exch-≈` and
-- `prodⁿ-exch`; `IID-exch` is `Exch-≈` with `prodⁿ-exch`; `Exch-marg` from `FinProd.proj-tuple`-style projections of
-- `swapQ` and `mapM-comp`.
--   Skeleton: holes first.
module QBS.Continuous.Exchangeable where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; inject₁)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.CondIID using (module CondIID)

module Exchangeable (lem₁ : LEM₁) where
  open SFinite (lemOf lem₁) using (XW; TQ; _≈ᴹ_; mapM; module C)
  open ProdMap (lemOf lem₁) using (_×H_)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ)
  open Independence lem₁ using (law)
  open IID lem₁ using (IID)
  open CondIID lem₁ using (CondIID; margM)
  open QBS
  open Hom

  -- the transposition of coordinates k and k + 1 of Xⁿ⁺¹
  swapQ : ∀ {X : QBS S} n → Fin n → Hom S (ΠQ (suc n) (λ _ → X)) (ΠQ (suc n) (λ _ → X))
  swapQ {X} (suc n) zero = pairQ S (_∘H_ S (fstQ S) (sndQ S)) (pairQ S (fstQ S) (_∘H_ S (sndQ S) (sndQ S)))
  swapQ {X} (suc n) (suc k) = _×H_ {X} {ΠQ (suc n) (λ _ → X)} (idH S {X}) (swapQ n k)

  -- exchangeability
  Exch : ∀ {X : QBS S} n → C.Pre (XW (ΠQ (suc n) (λ _ → X))) → Set₁
  Exch {X} n p = ∀ k → _≈ᴹ_ {ΠQ (suc n) (λ _ → X)} (mapM {ΠQ (suc n) (λ _ → X)} {ΠQ (suc n) (λ _ → X)} (swapQ n k) p) p

  Exch-≈ : ∀ {X : QBS S} n (p q : C.Pre (XW (ΠQ (suc n) (λ _ → X)))) → _≈ᴹ_ {ΠQ (suc n) (λ _ → X)} p q → Exch n p → Exch n q
  Exch-≈ = ?

  Exch-marg : ∀ {X : QBS S} n (p : C.Pre (XW (ΠQ (suc n) (λ _ → X)))) → Exch n p → ∀ k →
    _≈ᴹ_ {X} (mapM {ΠQ (suc n) (λ _ → X)} {X} (projQ (suc n) (λ _ → X) (inject₁ k)) p)
      (mapM {ΠQ (suc n) (λ _ → X)} {X} (projQ (suc n) (λ _ → X) (suc k)) p)
  Exch-marg = ?

  -- product laws are exchangeable
  prodⁿ-exch : ∀ {X : QBS S} n (μ : C.Pre (XW X)) → Exch n (prodⁿ (suc n) (λ _ → X) (λ _ → μ))
  prodⁿ-exch = ?

  -- mixtures of exchangeable laws
  Exch-mix : ∀ {Θ X : QBS S} n (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ (ΠQ (suc n) (λ _ → X)))) →
    (∀ θ → Exch n (map M ⟨$⟩ θ)) → Exch n (margM π M)
  Exch-mix = ?

  -- conditionally iid under a prior ⇒ exchangeable
  condIID-exch : ∀ {Θ X : QBS S} n (π : C.Pre (XW Θ)) (K : Hom S Θ (TQ X)) M → CondIID K (suc n) M → Exch n (margM π M)
  condIID-exch = ?

  -- iid random variables are exchangeable
  module _ {Ω : QBS S} (P : C.Pre Ω) where

    ExchRV : ∀ {Y : QBS S} n → (Fin (suc n) → Hom S Ω Y) → Set₁
    ExchRV {Y} n Xs = Exch n (law P (tupleQ (suc n) (λ _ → Y) Xs))

    IID-exch : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID P μ (suc n) Xs → ExchRV n Xs
    IID-exch = ?
