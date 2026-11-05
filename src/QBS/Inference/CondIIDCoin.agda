{-# OPTIONS --safe --without-K #-}

-- The flips of a coin with unknown bias as an instance of `CondIID` and `Exchangeable` (plan 05, items 48–49).  The
-- hand-built kernel `CoinUniformPriorN.Kn n : AQ ⇒ T (Fl n)` of the probability monad, moved to the s-finite measures
-- (`SFiniteIncl.ιH`) and to Boolⁿ⁺¹ (`flat`, Fl n ≅ ΠQ (n + 1) Bool):
--   * `KnS n`, θ ↦ the n + 1 flips, is conditionally iid with the one-flip kernel `coinK` (`Kn-iid`):
--     Kn ≈ Bernoulli(θ)^{⊗(n+1)};
--   * the marginal `CoinUniformPriorN.margN` (bias integrated out against the uniform prior) is `CondIID.margM` of
--     `KnS` (`margN-marg`), hence exchangeable (`margN-exch`), although the flips are not independent (Laplace's
--     rule, `CoinUniformPriorN.succession`).
-- Route: `Kn-iid` by induction on n: `nextK` is σ, then T of `flipPairN`, then join; through ιH (`SFiniteIncl.ι-mult`,
-- `ι-strong`, `ι-nat`) it becomes the double strength `CondIID.ψH` of `coinK θ` and `KnS n θ` up to ≈ᴹ (compare
-- integrals: `SFinite.∫ᴹ-join`, `∫ᴹ-map`, `SFiniteStrong.∫ᴹ-σ`), then `CondIID.ψ-at` and `Product.prod-cong` with the
-- induction hypothesis; at n = 0, `flat` pairs with the point of 1 (`Product` with the Dirac measure, `∫ᴹ-η`).
-- `margN-marg` from `ι-mult`, `ι-nat` and `ProdMap.mapM-comp`; `margN-exch` is `Exchangeable.condIID-exch` with
-- `Exch-≈`.
--   Skeleton: holes first.
module QBS.Inference.CondIIDCoin where

open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Core
open import QBS.Limits using (_×Q_; pairQ; !Q)
open import QBS.BoolQ using (module BoolOn)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ProdMap using (module ProdMap)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.Exchangeable using (module Exchangeable)
open import QBS.Inference.CoinUniformPrior using (module CoinUniformPrior)
open import QBS.Inference.CoinUniformPriorN using (module CoinUniformPriorN)
open import QBS.Inference.CondIID using (module CondIID)

module CondIIDCoin (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open UnitInterval A using (AQ)
  open Uniform lem₁ using (uniform)
  open SFinite (lemOf lem₁) using (XW; TQ; TH; _≈ᴹ_; mapM)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ιH)
  open ProdMap (lemOf lem₁) using (_×H_)
  open FinProd lem₁ using (ΠQ)
  open Exchangeable lem₁ using (Exch)
  open CoinUniformPrior lem₁ using (coinKernel)
  open CoinUniformPriorN lem₁ using (Fl; Kn; margN)
  open CondIID lem₁ using (CondIID; margM)
  open BoolOn S using (BoolQ)
  open QBS
  open Hom

  -- n + 1 flips as a point of Boolⁿ⁺¹
  flat : ∀ n → Hom S (Fl n) (ΠQ (suc n) (λ _ → BoolQ))
  flat zero = pairQ S (idH S {BoolQ}) (!Q S)
  flat (suc n) = _×H_ {BoolQ} {Fl n} (idH S {BoolQ}) (flat n)

  -- the kernels in the s-finite measures
  coinK : Hom S AQ (TQ BoolQ)
  coinK = _∘H_ S (ιH BoolQ) coinKernel

  KnS : ∀ n → Hom S AQ (TQ (ΠQ (suc n) (λ _ → BoolQ)))
  KnS n = _∘H_ S (TH (flat n)) (_∘H_ S (ιH (Fl n)) (Kn n))

  -- the flips are conditionally iid given the bias
  Kn-iid : ∀ n → CondIID coinK (suc n) (KnS n)
  Kn-iid = ?

  -- under the uniform prior: the marginal, and exchangeability
  margN-marg : ∀ n → _≈ᴹ_ {ΠQ (suc n) (λ _ → BoolQ)} (mapM {Fl n} {ΠQ (suc n) (λ _ → BoolQ)} (flat n) (ιPre {Fl n} (margN n)))
    (margM (ιPre {AQ} uniform) (KnS n))
  margN-marg = ?

  margN-exch : ∀ n → Exch n (mapM {Fl n} {ΠQ (suc n) (λ _ → BoolQ)} (flat n) (ιPre {Fl n} (margN n)))
  margN-exch = ?
