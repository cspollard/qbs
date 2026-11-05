{-# OPTIONS --safe --without-K #-}

-- Exchangeable laws (plan 05, item 49).  For s-finite measures on Xⁿ⁺¹ (`FinProd.ΠQ`):
--   * `swapQ n k`, the transposition of coordinates k and k + 1 (adjacent transpositions generate all permutations);
--     `Exch n p`: p is invariant under every adjacent transposition; it respects ≈ᴹ (`Exch-≈`), and adjacent
--     coordinates of an exchangeable law have the same law (`Exch-marg`);
--   * product laws μ^{⊗(n+1)} are exchangeable, for any s-finite μ (`prodⁿ-exch`);
--   * mixtures of exchangeable laws are exchangeable (`Exch-mix`), so the data marginal of a conditionally iid model
--     under any prior is exchangeable (`condIID-exch`, the easy half of de Finetti);
--   * on a probability P, an iid family of random variables has an exchangeable joint law (`IID-exch`, `ExchRV`).
-- Route: `prodⁿ-exch` by induction on k: at k = 0, `ExchangeableSwap.swap3` (both sides integrate to the same iterated
-- integral, by `Product.∫-prod`/`∫-prod′`); at k + 1, `ProdMap.map-prod` (id × swap) and `Product.prod-cong` with the
-- induction hypothesis.  `Exch-mix` from `SFinite.∫ᴹ-join`, `∫ᴹ-map` and `∫ᴹ-cong` pointwise in θ; `condIID-exch` is
-- `Exch-mix` with `Exch-≈` and `prodⁿ-exch`; `IID-exch` is `Exch-≈` with `prodⁿ-exch`; `Exch-marg` from `proj-swap`
-- (the projection to coordinate k after the swap is the projection to k + 1), `ProdMap.mapM-comp` and `mapM-ext`.
module QBS.Continuous.Exchangeable where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; inject₁)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (proj₂)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.Core
open import QBS.Limits using (_×Q_; fstQ; sndQ; pairQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.ExchangeableSwap using (module ExchangeableSwap)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.CondIID using (module CondIID)

module Exchangeable (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open SFinite (lemOf lem₁) using (XW; TQ; ∫ᴹ; ∫ᶠ; ∫ᴹ-map; ∫ᴹ-join; ∫ᴹ-cong; _≈ᴹ_; mapM; joinPre; module C)
  open Product (lemOf lem₁) using (prodPre; prod-cong)
  open ExchangeableSwap (lemOf lem₁) using (swap3)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open ProdMap (lemOf lem₁) using (_×H_; mapM-comp; mapM-cong; mapM-ext; map-prod)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ)
  open Independence lem₁ using (law)
  open IID lem₁ using (IID; ≈ᴹ-trans; ≈ᴹ-sym)
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
  Exch-≈ {X} n p q e x k = ≈ᴹ-trans {ΠQ (suc n) (λ _ → X)} (mapM-cong {ΠQ (suc n) (λ _ → X)} {ΠQ (suc n) (λ _ → X)} (swapQ n k)
    (≈ᴹ-sym {ΠQ (suc n) (λ _ → X)} e)) (≈ᴹ-trans {ΠQ (suc n) (λ _ → X)} (x k) e)

  -- the transposition exchanges the coordinates
  proj-swap : ∀ {X : QBS S} n (k : Fin n) y →
    Setoid._≈_ (Carrier X) (map (projQ (suc n) (λ _ → X) (inject₁ k)) ⟨$⟩ (map (swapQ n k) ⟨$⟩ y))
      (map (projQ (suc n) (λ _ → X) (suc k)) ⟨$⟩ y)
  proj-swap {X} (suc n) zero y = Setoid.refl (Carrier X)
  proj-swap {X} (suc n) (suc k) y = proj-swap {X} n k (proj₂ y)

  Exch-marg : ∀ {X : QBS S} n (p : C.Pre (XW (ΠQ (suc n) (λ _ → X)))) → Exch n p → ∀ k →
    _≈ᴹ_ {X} (mapM {ΠQ (suc n) (λ _ → X)} {X} (projQ (suc n) (λ _ → X) (inject₁ k)) p)
      (mapM {ΠQ (suc n) (λ _ → X)} {X} (projQ (suc n) (λ _ → X) (suc k)) p)
  Exch-marg {X} n p x k = ≈ᴹ-trans {X} (mapM-cong {ΠQ (suc n) (λ _ → X)} {X} pr (≈ᴹ-sym {ΠQ (suc n) (λ _ → X)} (x k)))
    (≈ᴹ-trans {X} (mapM-comp {ΠQ (suc n) (λ _ → X)} {ΠQ (suc n) (λ _ → X)} {X} (swapQ n k) pr p)
      (mapM-ext {ΠQ (suc n) (λ _ → X)} {X} (_∘H_ S pr (swapQ n k)) (projQ (suc n) (λ _ → X) (suc k)) p (proj-swap n k)))
    where pr = projQ (suc n) (λ _ → X) (inject₁ k)

  -- product laws are exchangeable
  prodⁿ-exch : ∀ {X : QBS S} n (μ : C.Pre (XW X)) → Exch n (prodⁿ (suc n) (λ _ → X) (λ _ → μ))
  prodⁿ-exch {X} (suc n) μ zero = swap3 {X} {X} {ΠQ n (λ _ → X)} μ μ (prodⁿ n (λ _ → X) (λ _ → μ))
  prodⁿ-exch {X} (suc n) μ (suc k) = ≈ᴹ-trans {ΠQ (suc (suc n)) (λ _ → X)}
    (map-prod {X} {ΠQ (suc n) (λ _ → X)} {X} {ΠQ (suc n) (λ _ → X)} (idH S {X}) (swapQ n k) μ (prodⁿ (suc n) (λ _ → X) (λ _ → μ)))
    (prod-cong {X} {ΠQ (suc n) (λ _ → X)} (≈-id μ) (prodⁿ-exch n μ k))
    where
      ≈-id : ∀ μ′ → _≈ᴹ_ {X} (mapM {X} {X} (idH S {X}) μ′) μ′
      ≈-id μ′ h = trans (∫ᴹ-map {X} {X} (idH S {X}) μ′ h) (∫ᴹ-cong {X} μ′ (λ y → refl))

  -- mixtures of exchangeable laws
  Exch-mix : ∀ {Θ X : QBS S} n (π : C.Pre (XW Θ)) (M : Hom S Θ (TQ (ΠQ (suc n) (λ _ → X)))) →
    (∀ θ → Exch n (map M ⟨$⟩ θ)) → Exch n (margM π M)
  Exch-mix {Θ} {X} n π M ex k f = trans (∫ᴹ-map {PX} {PX} (swapQ n k) (margM π M) f)
    (trans (∫ᴹ-join {PX} (mapM {Θ} {TQ PX} M π) (_∘H_ S f (swapQ n k)))
      (trans (∫ᴹ-map {Θ} {TQ PX} M π (∫ᶠ {PX} (_∘H_ S f (swapQ n k))))
        (trans (∫ᴹ-cong {Θ} π {_∘H_ S (∫ᶠ {PX} (_∘H_ S f (swapQ n k))) M} {_∘H_ S (∫ᶠ {PX} f) M} pw)
          (sym (trans (∫ᴹ-join {PX} (mapM {Θ} {TQ PX} M π) f) (∫ᴹ-map {Θ} {TQ PX} M π (∫ᶠ {PX} f)))))))
    where
      PX = ΠQ (suc n) (λ _ → X)
      pw : ∀ θ → ∫ᴹ {PX} (map M ⟨$⟩ θ) (_∘H_ S f (swapQ n k)) ≈ ∫ᴹ {PX} (map M ⟨$⟩ θ) f
      pw θ = trans (sym (∫ᴹ-map {PX} {PX} (swapQ n k) (map M ⟨$⟩ θ) f)) (ex θ k f)

  -- conditionally iid under a prior ⇒ exchangeable
  condIID-exch : ∀ {Θ X : QBS S} n (π : C.Pre (XW Θ)) (K : Hom S Θ (TQ X)) M → CondIID K (suc n) M → Exch n (margM π M)
  condIID-exch {Θ} {X} n π K M c = Exch-mix {Θ} {X} n π M
    (λ θ → Exch-≈ {X} n (prodⁿ (suc n) (λ _ → X) (λ _ → map K ⟨$⟩ θ)) (map M ⟨$⟩ θ) (≈ᴹ-sym {ΠQ (suc n) (λ _ → X)} (c θ))
      (prodⁿ-exch {X} n (map K ⟨$⟩ θ)))

  -- iid random variables are exchangeable
  module _ {Ω : QBS S} (P : C.Pre Ω) where

    ExchRV : ∀ {Y : QBS S} n → (Fin (suc n) → Hom S Ω Y) → Set₁
    ExchRV {Y} n Xs = Exch n (law P (tupleQ (suc n) (λ _ → Y) Xs))

    IID-exch : ∀ {Y : QBS S} (μ : C.Pre (XW Y)) n Xs → IID P μ (suc n) Xs → ExchRV n Xs
    IID-exch {Y} μ n Xs d = Exch-≈ {Y} n (prodⁿ (suc n) (λ _ → Y) (λ _ → μ)) (law P (tupleQ (suc n) (λ _ → Y) Xs))
      (≈ᴹ-sym {ΠQ (suc n) (λ _ → Y)} d) (prodⁿ-exch {Y} n μ)
