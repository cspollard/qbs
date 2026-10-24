{-# OPTIONS --safe --without-K #-}

-- From a Borel probability measure ν (a σ-additive set function) to a Daniell functional on all
-- measurable functions: the Lebesgue integral as a supremum of integrals of simple minorants
-- (`Analysis/CoinIntegral.agda`, generic in ν), with `I (functional ν) (χ U) ≈ ν U`.
-- Together with `Indicators.I-⋃` (the converse direction) this is the Riesz–Daniell
-- correspondence; see `Analysis/Riesz.agda`.
module QBS.Analysis.Functional where

open import Data.Empty using (⊥; ⊥-elim)
open import Level using (lift)
open import Data.Sum.Base using (_⊎_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda using (⊥ᵖ)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Fun
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Measure
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinCont using (module Cont)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.CoinSimple using (module Simple)
open import QBS.Analysis.CoinIntegral

module Functional (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (B : BM.BorelMeasure (lemOf lem₁)) where
  open DaniellB lem₁ B
  open Simple (lemOf lem₁) B
  open Integration A
  open Measurable A using (Fun-≤1)
  open LevelSets (lemOf lem₁) using (LS)
  open Series A
  open Sf
  open Cont (lemOf lem₁) B using (complete; ∫-complete)
  open BM.BorelMeasure B using (μ; μ-⊥)
  open Indicators A (lemOf lem₁) using (χ; χ-in; χ-out; χ-≤1; Fun-χ)
  open OmegaSemiring A renaming (Carrier to ∣A∣; zero to zero-sr)

  functional : Measure
  functional = record
    { I = λ h f → L h
    ; I-cong = λ e f f′ → L-cong e
    ; I-mono = λ f f′ le → L-mono le
    ; I-add = λ {h} {h₁} {h₂} f f₁ f₂ e →
        Add.L-add {h} {h₁} {h₂} e (LS f₁) (LS f₂) (Fun-≤1 f₁) (Fun-≤1 f₂)
    ; I-scale = λ {h} {h′} c f f′ e → Scale.L-scale {h} {h′} c e (LS f) (Fun-≤1 f) (Fun-≤1 f′)
    ; I-sup = λ {h} hs fs inc f e → SupLaw.L-sup {h} hs inc e (LS f) (λ n → LS (fs n)) (Fun-≤1 f)
    ; I-sub = λ f → OmegaSemiring.≤-reflexive A L-one
    }

  -- the integral of an indicator is the measure of the set
  module Ind {U : Pred} (bU : Borel U) where
    W : ℕ → Pred
    W zero = U
    W (suc _) = ⊥ᵖ

    bW : ∀ n → Borel (W n)
    bW zero = bU
    bW (suc _) = ⊥-borel

    Wdj : Disjoint W
    Wdj x zero zero _ _ = ≡.refl
    Wdj x zero (suc n) _ ()
    Wdj x (suc m) n () _

    ts : Sf
    ts = complete W bW Wdj (λ _ → 1#)

    ∫ts : ∫ ts ≈ μ bU
    ∫ts = trans (∫-complete W bW Wdj (λ _ → 1#))
      (trans (∑ᶠ-single {λ a → 1# * μ (bW a)} 0
               (λ { zero ne → ⊥-elim (ne ≡.refl) ; (suc n) _ → trans (*-cong refl (μ-⊥)) (zeroʳ 1#) }))
             (*-identityˡ (μ bU)))

    ts-minor : Minor (χ U) ts
    ts-minor zero x v = 0-least
    ts-minor (suc zero) x u = ≤-reflexive (sym (χ-in U (lift x) u))
    ts-minor (suc (suc a)) x ()

    ind≥ : μ bU ≤ L (χ U)
    ind≥ = ≤-trans (≤-reflexive (sym ∫ts)) (L-ub {χ U} {ts} ts-minor)

    ind≤ : L (χ U) ≤ μ bU
    ind≤ = L-lub {χ U} {μ bU} (λ s mn → ≤-trans (∫-mono s ts (hyp s mn)) (≤-reflexive ∫ts))
      where
        hyp : ∀ s → Minor (χ U) s → ∀ i j x → V s i x → V ts j x → ρ s i ≤ ρ ts j
        hyp s mn i zero x vi vj = ≤-trans (mn i x vi) (≤-reflexive (χ-out U (lift x) (λ u → vj (zero , u))))
        hyp s mn i (suc zero) x vi vj = ≤-trans (mn i x vi) (χ-≤1 U (lift x))
        hyp s mn i (suc (suc a)) x vi ()

    L-ind : L (χ U) ≈ μ bU
    L-ind = ≤-antisym ind≤ ind≥


  -- the integral of an indicator is the measure of the set
  functional-ind : ∀ {U} (bU : Borel U) → I functional (χ U) (Fun-χ bU) ≈ μ bU
  functional-ind bU = Ind.L-ind bU

  -- it has total mass one
  functional-prob : IsProb functional
  functional-prob = L-one
