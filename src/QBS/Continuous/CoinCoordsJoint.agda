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
module QBS.Continuous.CoinCoordsJoint where

open import Data.Fin.Base using (Fin; toℕ; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Core
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_)
open import QBS.Limits using (_×Q_; 1Q)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (evensR; oddsR; measurable-odds; merge-evens; merge-odds)
open import QBS.Continuous.SignedTransport using (module SignedTransport)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Unit.Polymorphic.Base using (tt)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JFubini using (module JFubini)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Continuous.CoinIndep using (module CoinIndep)
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
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel)
  open OmegaSemiring A using (_≈_; refl; sym; trans)
  open SFinite (lemOf lem₁) using (XW; mapM; ∫ᴹ; ∫ᴹ-map; ∫ᴹ-cong; ∫ᴹ-η; _≈ᴹ_; module C)
  open SignedTransport lem₁ using (∫ι)
  open Meas (lemOf lem₁) using (Meas; Meas-ext)
  open SFiniteStrong (lemOf lem₁) using (fixH)
  open Tensor A (lemOf lem₁) using (tensor₁)
  open JFubini (lemOf lem₁) using (J-tensor₁)
  open JParam (lemOf lem₁) using (J-agree)
  open CoinIndep lem₁ using (fairCoin-indep)
  open Product (lemOf lem₁) using (prodPre; ∫-prod′; intR; intR-pt; prod-cong; cmul)
  open OmegaSemiring A using (1#; *-cong; *-identityʳ)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Weights (lemOf lem₁) using (constW)
  open ProdMap (lemOf lem₁) using (mapM-id; mapM-comp; mapM-cong; mapM-ext; _×H_; map-prod)
  open FinProd lem₁ using (ΠQ; tupleQ; prodⁿ)
  open ProdBridge lem₁ using (ι-mass)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open FairCoin lem₁ using (fairCoin)
  open Daniell lem₁ using (L-one)
  open CoinCoords lem₁ using (coord; measurable-coord)
  open IID lem₁ using (IID; IIDSeq; IID-map)
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

  oddsH : Hom S ℛ ℛ
  oddsH = Probes.probe S {ℛ} {measₛ oddsR measurable-odds} measurable-odds

  -- r ↦ (evens r, odds r)
  pairEO : Hom S ℛ (_×Q_ S ℛ ℛ)
  pairEO = pairQ S {ℛ} {ℛ} {ℛ} (coordH 0) oddsH

  -- the integral of the coin of a test is the J-integral of its values
  ∫coin : ∀ g → ∫ᴹ {ℛ} coin g ≈ J fairCoin (λ r → map g ⟨$⟩ r) (map-random g (Probes.unprobe S (idH S {ℛ})))
  ∫coin g = ∫ι coinPre g

  -- the left side of `split`: the law of (evens, odds), as an iterated J-integral
  split-lhs : ∀ h → ∫ᴹ {_×Q_ S ℛ ℛ} (mapM {ℛ} {_×Q_ S ℛ ℛ} pairEO coin) h ≈
    J fairCoin (λ r → map h ⟨$⟩ (evensR r , oddsR r)) (map-random (_∘H_ S h pairEO) (Probes.unprobe S (idH S {ℛ})))
  split-lhs h = trans (∫ᴹ-map {ℛ} {_×Q_ S ℛ ℛ} pairEO coin h) (∫coin (_∘H_ S h pairEO))

  -- the right side of `split`, as an iterated J-integral
  intR-J : ∀ h r → map (intR {ℛ} {ℛ} coin h) ⟨$⟩ r ≈
    J fairCoin (λ s → map h ⟨$⟩ (r , s)) (map-random (fixH {ℛ} {ℛ} r h) (Probes.unprobe S (idH S {ℛ})))
  intR-J h r = trans (intR-pt {ℛ} {ℛ} coin h r) (∫coin (fixH {ℛ} {ℛ} r h))

  rhsM : ∀ h → Meas (λ r → J fairCoin (λ s → map h ⟨$⟩ (r , s)) (map-random (fixH {ℛ} {ℛ} r h) (Probes.unprobe S (idH S {ℛ}))))
  rhsM h = Meas-ext {λ r → map (intR {ℛ} {ℛ} coin h) ⟨$⟩ (map (idH S {ℛ}) ⟨$⟩ r)} (intR-J h)
    (map-random (intR {ℛ} {ℛ} coin h) {map (idH S {ℛ})} (Probes.unprobe S (idH S {ℛ})))

  split-rhs : ∀ h → ∫ᴹ {_×Q_ S ℛ ℛ} (prodPre {ℛ} {ℛ} coin coin) h ≈
    J fairCoin (λ r → J fairCoin (λ s → map h ⟨$⟩ (r , s)) (map-random (fixH {ℛ} {ℛ} r h) (Probes.unprobe S (idH S {ℛ})))) (rhsM h)
  split-rhs h = trans (∫-prod′ {ℛ} {ℛ} coin coin h) (trans (∫coin (intR {ℛ} {ℛ} coin h))
    (J-cong fairCoin (map-random (intR {ℛ} {ℛ} coin h) (Probes.unprobe S (idH S {ℛ}))) (rhsM h) (intR-J h)))

  split : _≈ᴹ_ {_×Q_ S ℛ ℛ} (mapM {ℛ} {_×Q_ S ℛ ℛ} pairEO coin) (prodPre {ℛ} {ℛ} coin coin)
  split h = trans (split-lhs h) (trans (sym (J-agree (tensor₁ fairCoin fairCoin) fairCoin _ (λ F → fairCoin-indep F)))
    (trans (J-tensor₁ fairCoin fairCoin _) (trans (J-cong fairCoin _ _ (λ r → J-cong fairCoin _ _
      (λ s → Func.cong (map h) (merge-evens r s , merge-odds r s)))) (sym (split-rhs h)))))

  -- the first n coordinates as a tuple
  T : ∀ n → Hom S ℛ (ΠQ n (λ _ → ℛ))
  T n = tupleQ n (λ _ → ℛ) (λ i → coordH (toℕ i))

  -- tuples of pointwise equal coordinates are equal
  tuple-ext : ∀ n {Z Z′ X : QBS S} (F : Fin n → Hom S Z X) (G : Fin n → Hom S Z′ X) z z′ →
    (∀ j → Setoid._≈_ (Carrier X) (map (F j) ⟨$⟩ z) (map (G j) ⟨$⟩ z′)) →
    Setoid._≈_ (Carrier (ΠQ n (λ _ → X))) (map (tupleQ n (λ _ → X) F) ⟨$⟩ z) (map (tupleQ n (λ _ → X) G) ⟨$⟩ z′)
  tuple-ext zero F G z z′ e = Setoid.refl (Carrier (ΠQ zero (λ _ → ℛ)))
  tuple-ext (suc n) F G z z′ e = e zero , tuple-ext n (λ j → F (suc j)) (λ j → G (suc j)) z z′ (λ j → e (suc j))

  -- one more coordinate: (evens, odds) splits the coin, then the tail is the first n coordinates of the odd half
  coins-step : ∀ n → IID coinPre coin n (λ i → coordH (toℕ i)) → IID coinPre coin (suc n) (λ i → coordH (toℕ i))
  coins-step n ih h = trans
    (mapM-ext {ℛ} {ΠQ (suc n) (λ _ → ℛ)} (T (suc n)) (_∘H_ S (_×H_ {ℛ} {ℛ} {ℛ} {ΠQ n (λ _ → ℛ)} (idH S {ℛ}) (T n)) pairEO) coin
      (λ ω → Setoid.refl (Carrier ℛ) , tuple-ext n (λ j → coordH (suc (toℕ j))) (λ j → coordH (toℕ j)) ω (oddsR ω)
        (λ j → Setoid.refl (Carrier ℛ))) h)
    (trans (sym (mapM-comp {ℛ} {_×Q_ S ℛ ℛ} pairEO (_×H_ {ℛ} {ℛ} {ℛ} {ΠQ n (λ _ → ℛ)} (idH S {ℛ}) (T n)) coin h))
      (trans (mapM-cong {_×Q_ S ℛ ℛ} (_×H_ {ℛ} {ℛ} {ℛ} {ΠQ n (λ _ → ℛ)} (idH S {ℛ}) (T n)) split h)
        (trans (map-prod {ℛ} {ℛ} {ℛ} {ΠQ n (λ _ → ℛ)} (idH S {ℛ}) (T n) coin coin h)
          (prod-cong {ℛ} {ΠQ n (λ _ → ℛ)} (mapM-id {ℛ} coin) ih h))))

  -- the coordinates are iid
  coins-iid : ∀ n → IID coinPre coin n (λ i → coordH (toℕ i))
  coins-iid zero h = trans (∫ᴹ-map {ℛ} {1Q S} (T 0) coin h)
    (trans (∫ᴹ-cong {ℛ} coin {_∘H_ S h (T 0)} {mulH {ℛ} (constW {ℛ} c) (constW {ℛ} 1#)} (λ ω → sym (*-identityʳ _)))
      (trans (cmul {ℛ} coin c (constW {ℛ} 1#)) (trans (*-cong refl (ι-mass {ℛ} coinPre))
        (trans (*-identityʳ _) (sym (∫ᴹ-η {1Q S} tt h))))))
    where c = map h ⟨$⟩ tt
  coins-iid (suc n) = coins-step n (coins-iid n)

  coins-iidSeq : IIDSeq coinPre coin coordH
  coins-iidSeq = coins-iid

  -- the draws of a sampler at θ
  drawH : ∀ {Θ X : QBS S} → SamplerQ Θ X → ∣ Θ ∣ → Hom S ℛ X
  drawH {Θ} {X} s θ = _∘H_ S s (pairQ S {ℛ} {Θ} {ℛ} (constQ {ℛ} {Θ} θ) (idH S {ℛ}))

  draws-iid : ∀ {Θ X : QBS S} (s : SamplerQ Θ X) θ n →
    IID coinPre (mapM {ℛ} {X} (drawH s θ) coin) n (λ i → _∘H_ S (drawH s θ) (coordH (toℕ i)))
  draws-iid {Θ} {X} s θ n = IID-map {ℛ} coinPre {ℛ} {X} coin n (λ i → coordH (toℕ i)) (drawH s θ) (coins-iid n)
