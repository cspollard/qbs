{-# OPTIONS --safe --without-K #-}

-- The flips of a coin with unknown bias as an instance of `CondIID` and `Exchangeable` (plan 05, items 48–49).  The
-- hand-built kernel `CoinUniformPriorN.Kn n : AQ ⇒ T (Fl n)` of the probability monad, moved to the s-finite measures
-- (`SFiniteIncl.ιH`) and to Boolⁿ⁺¹ (`flat`, Fl n ≅ ΠQ (n + 1) Bool):
--   * `KnS n`, θ ↦ the n + 1 flips, is conditionally iid with the one-flip kernel `coinK` (`Kn-iid`):
--     Kn ≈ Bernoulli(θ)^{⊗(n+1)};
--   * the marginal `CoinUniformPriorN.margN` (bias integrated out against the uniform prior) is `CondIID.margM` of
--     `KnS` (`margN-marg`), hence exchangeable (`margN-exch`), although the flips are not independent (Laplace's
--     rule, `CoinUniformPriorN.succession`).
-- Route: `Kn-iid` by induction on n through the integrals (`kn`): one step of `nextK` through `SFiniteIncl.ιPre` is
-- `CondIIDCoinStep.nextK-ι` (`ι-mult`, `ι-nat`, `ι-strong`, `∫ᴹ-join`, `∫ᴹ-map`, `∫ᴹ-σ`), compared with
-- `Product.∫-prod′` for μ ⊗ μ^{⊗(n+1)} (`intR-pt`); at n = 0 the product is with the Dirac measure (`∫ᴹ-η`).
-- `margN-marg` from `ι-mult`, `ι-nat` and `∫ᴹ-map`; `margN-exch` is `Exchangeable.condIID-exch` with `Exch-≈`.
module QBS.Inference.CondIIDCoin where

open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Core
open import QBS.Limits using (_×Q_; pairQ; !Q; 1Q)
open import QBS.BoolQ using (module BoolOn)
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
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.IID using (module IID)
open import QBS.Inference.CondIID using (module CondIID)
open import QBS.Inference.CondIIDCoinStep using (module CondIIDCoinStep)
open import QBS.Classical using (LEM₁)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.Weights using (module Weights)

module CondIIDCoin (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open UnitInterval A using (AQ)
  open Uniform lem₁ using (uniform)
  open OmegaSemiring A using (_≈_; 1#; refl; sym; trans)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; TQ; TH; ∫ᴹ; ∫ᶠ; ∫ᴹ-map; ∫ᴹ-join; ∫ᴹ-cong; ∫ᴹ-η; _≈ᴹ_; mapM; joinPre; module C)
  open Product (lemOf lem₁) using (prodPre; intR; intR-pt; ∫-prod′)
  open SFiniteStrong (lemOf lem₁) using (fixH)
  open IID lem₁ using (≈ᴹ-sym)
  open CondIIDCoinStep lem₁ using (nextK-ι)
  open SFiniteIncl (lemOf lem₁) using (ιPre; ιH; ι-nat; ι-mult)
  open ProdMap (lemOf lem₁) using (_×H_)
  open FinProd lem₁ using (ΠQ; prodⁿ)
  open Exchangeable lem₁ using (Exch; Exch-≈; condIID-exch)
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
  -- abbreviations
  Bn : ℕ → QBS S
  Bn n = ΠQ (suc n) (λ _ → BoolQ)

  μθ : ∣ AQ ∣ → C.Pre (XW BoolQ)
  μθ θ = ιPre {BoolQ} (map coinKernel ⟨$⟩ θ)

  νθ : ∀ n → ∣ AQ ∣ → C.Pre (XW (Bn n))
  νθ n θ = prodⁿ (suc n) (λ _ → BoolQ) (λ _ → μθ θ)

  κθ : ∀ n → ∣ AQ ∣ → C.Pre (XW (Fl n))
  κθ n θ = ιPre {Fl n} (map (Kn n) ⟨$⟩ θ)

  kn-pw : ∀ n θ → _≈ᴹ_ {Bn n} (mapM {Fl n} {Bn n} (flat n) (κθ n θ)) (νθ n θ) → (h : Hom S (Bn (suc n)) WQ) → ∀ b →
    map (intR {BoolQ} {Fl n} (κθ n θ) (_∘H_ S h (flat (suc n)))) ⟨$⟩ b ≈ map (intR {BoolQ} {Bn n} (νθ n θ) h) ⟨$⟩ b
  kn-pw n θ ih h b = trans (intR-pt {BoolQ} {Fl n} κ (_∘H_ S h (flat (suc n))) b)
    (trans (∫ᴹ-cong {Fl n} κ {fixH {BoolQ} {Fl n} b (_∘H_ S h (flat (suc n)))} {_∘H_ S hb (flat n)} (λ y → refl))
      (trans (sym (∫ᴹ-map {Fl n} {Bn n} (flat n) κ hb)) (trans (ih hb) (sym (intR-pt {BoolQ} {Bn n} (νθ n θ) h b)))))
    where
      κ = κθ n θ
      hb = fixH {BoolQ} {Bn n} b h

  kn : ∀ n θ → _≈ᴹ_ {Bn n} (mapM {Fl n} {Bn n} (flat n) (κθ n θ)) (νθ n θ)
  kn zero θ h = trans (∫ᴹ-map {BoolQ} {Bn zero} (flat zero) (μθ θ) h)
    (trans (∫ᴹ-cong {BoolQ} (μθ θ) {_∘H_ S h (flat zero)} {intR {BoolQ} {1Q S} δ h}
      (λ b → sym (trans (intR-pt {BoolQ} {1Q S} δ h b) (∫ᴹ-η {1Q S} tt (fixH {BoolQ} {1Q S} b h)))))
      (sym (∫-prod′ {BoolQ} {1Q S} (μθ θ) δ h)))
    where δ = C.ηPre {XW (1Q S)} (1# , tt)
  kn (suc n) θ h = trans (∫ᴹ-map {Fl (suc n)} {Bn (suc n)} (flat (suc n)) (κθ (suc n) θ) h)
    (trans (nextK-ι {Fl n} (Kn n) θ (_∘H_ S h (flat (suc n))))
      (trans (∫ᴹ-cong {BoolQ} (μθ θ) {intR {BoolQ} {Fl n} (κθ n θ) (_∘H_ S h (flat (suc n)))} {intR {BoolQ} {Bn n} (νθ n θ) h}
        (kn-pw n θ (kn n θ) h))
        (sym (∫-prod′ {BoolQ} {Bn n} (μθ θ) (νθ n θ) h))))

  Kn-iid : ∀ n → CondIID coinK (suc n) (KnS n)
  Kn-iid n θ = kn n θ

  -- under the uniform prior: the marginal, and exchangeability
  marg-pw : ∀ n (f : Hom S (Bn n) WQ) θ →
    ∫ᴹ {Fl n} (κθ n θ) (_∘H_ S f (flat n)) ≈ ∫ᴹ {Bn n} (map (KnS n) ⟨$⟩ θ) f
  marg-pw n f θ = sym (∫ᴹ-map {Fl n} {Bn n} (flat n) (κθ n θ) f)

  margM-int : ∀ n (f : Hom S (Bn n) WQ) →
    ∫ᴹ {Bn n} (margM (ιPre {AQ} uniform) (KnS n)) f ≈ ∫ᴹ {AQ} (ιPre {AQ} uniform) (_∘H_ S (∫ᶠ {Bn n} f) (KnS n))
  margM-int n f = trans (∫ᴹ-join {Bn n} (mapM {AQ} {TQ (Bn n)} (KnS n) (ιPre {AQ} uniform)) f)
    (∫ᴹ-map {AQ} {TQ (Bn n)} (KnS n) (ιPre {AQ} uniform) (∫ᶠ {Bn n} f))

  margN-marg : ∀ n → _≈ᴹ_ {Bn n} (mapM {Fl n} {Bn n} (flat n) (ιPre {Fl n} (margN n))) (margM (ιPre {AQ} uniform) (KnS n))
  margN-marg n f = trans (∫ᴹ-map {Fl n} {Bn n} (flat n) (ιPre {Fl n} (margN n)) f)
    (trans (ι-mult {Fl n} q fl)
      (trans (∫ᴹ-join {Fl n} (ιPre {TQ (Fl n)} (C.mapPre {C.TQ (Fl n)} {TQ (Fl n)} (ιH (Fl n)) q)) fl)
        (trans (ι-nat {C.TQ (Fl n)} {TQ (Fl n)} (ιH (Fl n)) q (∫ᶠ {Fl n} fl))
          (trans (∫ᴹ-map {C.TQ (Fl n)} {TQ (Fl n)} (ιH (Fl n)) (ιPre {C.TQ (Fl n)} q) (∫ᶠ {Fl n} fl))
            (trans (ι-nat {AQ} {C.TQ (Fl n)} (Kn n) uniform (T fl))
              (trans (∫ᴹ-map {AQ} {C.TQ (Fl n)} (Kn n) (ιPre {AQ} uniform) (T fl))
                (trans (∫ᴹ-cong {AQ} (ιPre {AQ} uniform) {_∘H_ S (T fl) (Kn n)} {_∘H_ S (∫ᶠ {Bn n} f) (KnS n)} (marg-pw n f))
                  (sym (margM-int n f)))))))))
    where
      q = C.mapPre {AQ} {C.TQ (Fl n)} (Kn n) uniform
      fl = _∘H_ S f (flat n)
      T = λ g → _∘H_ S (∫ᶠ {Fl n} g) (ιH (Fl n))

  margN-exch : ∀ n → Exch n (mapM {Fl n} {ΠQ (suc n) (λ _ → BoolQ)} (flat n) (ιPre {Fl n} (margN n)))
  margN-exch n = Exch-≈ {BoolQ} n (margM (ιPre {AQ} uniform) (KnS n)) (mapM {Fl n} {Bn n} (flat n) (ιPre {Fl n} (margN n)))
    (≈ᴹ-sym {Bn n} (margN-marg n)) (condIID-exch {AQ} {BoolQ} n (ιPre {AQ} uniform) coinK (KnS n) (Kn-iid n))
