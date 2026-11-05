{-# OPTIONS --safe --without-K #-}

-- The coin coordinates are iid (plan 05, item 47).  On Cantor space ℛ with the fair coin as a probability
-- (`coinPre`; `coin = ιPre coinPre` in the s-finite layer):
--   * `coordH i : ℛ ⇒ ℛ` is the i-th coordinate `CoinCoords.coord i = evens ∘ oddsⁱ` as a morphism;
--   * the first n coordinates are iid with the law of the coin (`coins-iid`, so `IID.IID-indep` makes them mutually
--     independent, upgrading the pairwise `CoinCoords.J-indep`); every prefix of the sequence (`coins-iidSeq`);
--   * for a sampler s : Θ × ℛ ⇒ X (`Inference/Sampler`) and θ, the draws s(θ, coord i r) are iid with the law of one
--     draw (`draws-iid`), so the samplers' observations are iid in the sense of `Continuous/IID`.
-- Route: induction on n.  The tuple of the first n + 1 coordinates is (evens, tuple of the first n coordinates ∘ odds),
-- so its law is the push-forward of the coin along (evens, odds) followed by id × tuple (`ProdMap.map-prod`);
-- `CoinIndep.fairCoin-indep` makes the law of (evens, odds) the product coin ⊗ coin (`Product.prodPre`, through
-- `ProdBridge`/`SFiniteIncl` and the `J`/`Fun` integral of the coin, as in `CoinCoords.J-split`), and
-- `CoinCoords.J-evens`/`J-odds` give the marginals.  `draws-iid` is `IID.IID-map` of `coins-iid`.
--   Skeleton: holes first.
module QBS.Continuous.CoinCoordsJoint where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (ℕ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (pairQ)
open import QBS.BoolQ using (module BoolOn)
open import QBS.Analysis.CoinIntegral using (lemOf; module Daniell)
open import QBS.Borel.Source using (measₛ)
import QBS.Probes as Probes
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.CoinCoords using (module CoinCoords)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.Sampler using (module Sampler)

module CoinCoordsJoint (lem₁ : LEM₁) where
  open SFinite (lemOf lem₁) using (XW; mapM; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open FairCoin lem₁ using (fairCoin)
  open Daniell lem₁ using (L-one)
  open CoinCoords lem₁ using (coord; measurable-coord)
  open IID lem₁ using (IID; IIDSeq)
  open BoolOn S using (constQ)
  open Sampler lem₁ using () renaming (Sampler to SamplerQ)
  open QBS
  open Hom

  ℛ : QBS S
  ℛ = Probes.ℛQ S

  -- the fair coin on Cantor space
  coinPre : C.Pre ℛ
  coinPre = C.mk (map (idH S {ℛ})) (Probes.unprobe S (idH S {ℛ})) fairCoin L-one

  coin : C.Pre (XW ℛ)
  coin = ιPre {ℛ} coinPre

  -- the i-th coordinate as a morphism
  coordH : ℕ → Hom S ℛ ℛ
  coordH i = Probes.probe S {ℛ} {measₛ (coord i) (measurable-coord i)} (measurable-coord i)

  -- the coordinates are iid
  coins-iid : ∀ n → IID coinPre coin n (λ i → coordH (toℕ i))
  coins-iid = ?

  coins-iidSeq : IIDSeq coinPre coin coordH
  coins-iidSeq = ?

  -- the draws of a sampler at θ
  drawH : ∀ {Θ X : QBS S} → SamplerQ Θ X → ∣ Θ ∣ → Hom S ℛ X
  drawH {Θ} {X} s θ = _∘H_ S s (pairQ S {ℛ} {Θ} {ℛ} (constQ {ℛ} {Θ} θ) (idH S {ℛ}))

  draws-iid : ∀ {Θ X : QBS S} (s : SamplerQ Θ X) θ n →
    IID coinPre (mapM {ℛ} {X} (drawH s θ) coin) n (λ i → _∘H_ S (drawH s θ) (coordH (toℕ i)))
  draws-iid = ?
