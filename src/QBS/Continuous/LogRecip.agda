{-# OPTIONS --safe --without-K #-}

-- The reciprocal of a lower real, as a cut (plan 03, "Signed layer", helper for `SignedLog`):
--   q ∈ recC w  iff  ∃ p > q, ∀ s ∈ w, p · s < 1      (so recC (expC x) = negExp x by definition).
--   * `recC-anti`, `recC-cong`;
--   * `recC-mul : recC w ⊗ w ≋ 1` when w is bounded by a rational and has a positive element, the argument of
--     `NegExp.negExp-expC` for an arbitrary cut: `near-maxG` is `NegExp.near-max` with the cut and its positive element
--     as parameters (a near-maximal element by LEM, via the chain lemmas `climb` and `bump` of `NegExp`), and `reachG`
--     is `NegExp.reach`;
--   * `recC-lt1` : if oneC ⊑ w and every q ∈ recC w ... gives `recC w ⊑ 1` (from `NegExp.bound1`);
--   * `Meas-recC` : r ↦ recC (h r) is threshold-measurable when h is.
module QBS.Continuous.LogRecip where

open import Level using (lift)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.ExpLower using (pos-inv; P-id)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Borel.Core using (inter₂)
open import QBS.Classical using (LEM₀)

recC : Cut → Cut
recC w = record
  { mem = λ q → Σ ℚᵘ (λ p → q < p × (∀ s → mem w s → p * s < 1ℚᵘ))
  ; down = λ le (p , lt , f) → p , ≤-<-trans le lt , f
  ; open′ = λ (p , lt , f) → let q′ , q<q′ , q′<p = dense lt in q′ , q<q′ , p , q′<p , f
  ; neg = λ {q} lt → 0ℚᵘ , lt , λ s _ → ≃-<ˡ (≃-sym (*-zeroˡ s)) 0<1 }

recC-anti : ∀ {w w′} → w ⊑ w′ → recC w′ ⊑ recC w
recC-anti ww = mk⊑ (λ q (p , lt , f) → p , lt , λ s m → f s (ap ww s m))

recC-cong : ∀ {w w′} → w ≋ w′ → recC w ≋ recC w′
recC-cong (a , b) = recC-anti b , recC-anti a

module LogRecip (lem : LEM₀) where
  open NegExp lem using (pos-step; scale-lt; chain-base; climb; bump; bound1; borel-imp)

  -- the product is below 1
  recC-mul≤1 : ∀ w → recC w ⊗ w ⊑ oneC
  recC-mul≤1 w = mk⊑ λ { q (inj₁ lt) → <-trans lt 0<1
    ; q (inj₂ (r , s , 0<r , 0<s , (p , r<p , f) , ms , h)) →
        ≤-<-trans h (<-trans (*-mono-<-posʳ 0<s r<p) (f s ms)) }

  -- if there is no near-maximal element, every positive element has a larger one
  stepG : ∀ (S : Cut) ρ → 0ℚᵘ < ρ → (Σ ℚᵘ (λ s → mem S s × 0ℚᵘ < s × (∀ s′ → mem S s′ → ρ * s′ < s)) → ⊥) →
    ∀ s → mem S s → 0ℚᵘ < s → Σ ℚᵘ (λ s′ → mem S s′ × s ≤ ρ * s′)
  stepG S ρ 0<ρ no s ms 0<s with lem (Σ ℚᵘ (λ s′ → mem S s′ × s ≤ ρ * s′))
  ... | inj₁ w = w
  ... | inj₂ none = ⊥-elim (no (s , ms , 0<s , λ s′ ms′ → not-≤⇒< (λ le → none (s′ , ms′ , le))))

  -- the chain s₀ + n (1 − ρ) s₀ ≤ sₙ
  chainG : ∀ (S : Cut) {s₀ ρ} → 0ℚᵘ < ρ → ρ < 1ℚᵘ → 0ℚᵘ < s₀ → mem S s₀ →
    (∀ s → mem S s → 0ℚᵘ < s → Σ ℚᵘ (λ s′ → mem S s′ × s ≤ ρ * s′)) →
    ∀ n → Σ ℚᵘ (λ s → mem S s × s₀ + nat n * ((1ℚᵘ + - ρ) * s₀) ≤ s)
  chainG S {s₀} 0<ρ ρ<1 0<s₀ m₀ step zero =
    s₀ , m₀ , ≤-≃ (≃-trans (+-cong (≃-refl {s₀}) (*-zeroˡ _)) (+-identityʳ s₀))
  chainG S {s₀} 0<ρ ρ<1 0<s₀ m₀ step (suc n) with chainG S 0<ρ ρ<1 0<s₀ m₀ step n
  ... | s , ms , h with step s ms (<-≤-trans 0<s₀ (chain-base n (*-pos (pos-diff ρ<1) 0<s₀) h))
  ... | s′ , ms′ , hs = s′ , ms′ , bump n 0<ρ ρ<1 0<s₀ h hs

  -- a near-maximal element of a bounded cut with a positive element
  near-maxG : ∀ (S : Cut) B → (∀ s → mem S s → s < B) → ∀ {s₀} → 0ℚᵘ < s₀ → mem S s₀ → ∀ ρ → 0ℚᵘ < ρ → ρ < 1ℚᵘ →
    Σ ℚᵘ (λ s → mem S s × 0ℚᵘ < s × (∀ s′ → mem S s′ → ρ * s′ < s))
  near-maxG S B bd {s₀} 0<s₀ m₀ ρ 0<ρ ρ<1
    with lem (Σ ℚᵘ (λ s → mem S s × 0ℚᵘ < s × (∀ s′ → mem S s′ → ρ * s′ < s)))
  ... | inj₁ w = w
  ... | inj₂ no = ⊥-elim (<-irrefl ≃-refl (≤-<-trans (≤-trans arch-le (≤-trans (≤-≃ (≃-sym (+-identityˡ (nat k * c))))
        (≤-trans (+-mono-≤ (<-≤ 0<s₀) (≤-refl {nat k * c})) lo))) (bd _ ms₁)))
    where
      c = (1ℚᵘ + - ρ) * s₀
      0<c = *-pos (pos-diff ρ<1) 0<s₀
      ch = chainG S 0<ρ ρ<1 0<s₀ m₀ (stepG S ρ 0<ρ no)
      k = proj₁ (arch B 0<c)
      arch-le = proj₂ (arch B 0<c)
      ms₁ = proj₁ (proj₂ (ch k))
      lo = proj₂ (proj₂ (ch k))

  reachG : ∀ (S : Cut) {q q′ s} → 0ℚᵘ ≤ q → q < q′ → 0ℚᵘ < s → mem S s →
    (∀ s′ → mem S s′ → q′ * s′ < s) → mem (recC S ⊗ S) q
  reachG S {q} {q′} {s} 0≤q q<q′ 0<s ms hs =
    inj₂ (r , s , 0<r , 0<s , (q′ * t , r<p , λ s′ ms′ → scale-lt 0<t ht (hs s′ ms′)) , ms
         , ≤-trans (≤-≃ (≃-sym qts)) (<-≤ (*-mono-<-posʳ 0<s qt<r)))
    where
      t = proj₁ (inv 0<s)
      ht = proj₂ (inv 0<s)
      0<t = pos-inv 0<s ht
      rr = dense (*-mono-<-posʳ 0<t q<q′)
      r = proj₁ rr
      qt<r = proj₁ (proj₂ rr)
      r<p = proj₂ (proj₂ rr)
      0≤qt : 0ℚᵘ ≤ q * t
      0≤qt = ≤-trans (≤-≃ (≃-sym (*-zeroˡ t))) (*-mono-≤-nnʳ (<-≤ 0<t) 0≤q)
      0<r = ≤-<-trans 0≤qt qt<r
      qts : (q * t) * s ≃ q
      qts = ≃-trans (*-assoc q t s) (≃-trans (*-cong (≃-refl {q}) ht) (P-id q))

  1≤recC-mul : ∀ w B → (∀ s → mem w s → s < B) → ∀ {s₀} → 0ℚᵘ < s₀ → mem w s₀ → oneC ⊑ recC w ⊗ w
  1≤recC-mul w B bd 0<s₀ m₀ = mk⊑ go
    where
      go : ∀ q → q < 1ℚᵘ → mem (recC w ⊗ w) q
      go q lt with neg-or-nonneg q
      ... | inj₁ q<0 = inj₁ q<0
      ... | inj₂ 0≤q with dense lt
      ... | q′ , q<q′ , q′<1 with near-maxG w B bd 0<s₀ m₀ q′ (≤-<-trans 0≤q q<q′) q′<1
      ... | s , ms , 0<s , hs = reachG w 0≤q q<q′ 0<s ms hs

  recC-mul : ∀ w B → (∀ s → mem w s → s < B) → ∀ {s₀} → 0ℚᵘ < s₀ → mem w s₀ → recC w ⊗ w ≋ oneC
  recC-mul w B bd 0<s₀ m₀ = recC-mul≤1 w , 1≤recC-mul w B bd 0<s₀ m₀

  -- if every s < 1 is in w then recC w is below 1
  recC-lt1 : ∀ {w} → oneC ⊑ w → recC w ⊑ oneC
  recC-lt1 {w} ow = mk⊑ (λ q (p , lt , f) → <-≤-trans lt (bound1 (λ s s<1 → f s (ap ow s s<1))))

  open Meas lem using (Meas; ex-enum; all-enum)
  open LevelSets lem using (Lvl; borel-prop)

  Meas-recC : ∀ {h} → Meas h → Meas (λ r → recC (h r))
  Meas-recC {h} mh q = ex-enum (λ p c → q < p × (∀ s → Lvl h s c → p * s < 1ℚᵘ))
    (λ p → inter₂ (borel-prop (q < p)) (all-enum (λ s c → Lvl h s c → p * s < 1ℚᵘ)
      (λ s → borel-imp (p * s < 1ℚᵘ) (mh s))))
