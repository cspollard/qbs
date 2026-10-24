{-# OPTIONS --safe --without-K #-}

-- Self-similarity of the binary expansion: prepending a bit b to r gives
--   expansion (b :: r) ≈ sel b ½ + ½ · expansion r.
module QBS.Analysis.ExpansionCons where

open import Level using (suc; zero; lift; lower)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Cons using (consR)
open import QBS.Analysis.Omega
open import QBS.Analysis.BinaryExpansion using (module Expansion)

module ExpansionCons (A : OmegaSemiring (suc zero)) (half : OmegaSemiring.Carrier A)
    (hh : OmegaSemiring._≈_ A (OmegaSemiring._+_ A half half) (OmegaSemiring.1# A)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Expansion A half hh
  open SetoidReasoning setoid

  sel-scale : ∀ c h w → sel c (h * w) ≈ h * sel c w
  sel-scale true h w = refl
  sel-scale false h w = sym (zeroʳ h)

  part-cons : ∀ b N r → part (ℕ.suc N) (consR b r) ≈ sel b half + half * part N r
  part-cons b ℕ.zero r = begin
    0# + sel b (half * 1#)       ≈⟨ +-identityˡ _ ⟩
    sel b (half * 1#)            ≈⟨ lemma b ⟩
    sel b half + half * 0#       ∎
    where
      lemma : ∀ c → sel c (half * 1#) ≈ sel c half + half * 0#
      lemma true = sym (trans (+-cong (sym (*-identityʳ half)) (zeroʳ half)) (+-identityʳ _))
      lemma false = sym (trans (+-cong refl (zeroʳ half)) (+-identityʳ 0#))
  part-cons b (ℕ.suc N) r = begin
    part (ℕ.suc N) (consR b r) + bitW (ℕ.suc N) (consR b r)
      ≈⟨ +-cong (part-cons b N r) (sel-scale (lower r N) half (half * hpow N)) ⟩
    (sel b half + half * part N r) + half * bitW N r
      ≈⟨ +-assoc _ _ _ ⟩
    sel b half + (half * part N r + half * bitW N r)
      ≈⟨ +-cong refl (sym (distribˡ half _ _)) ⟩
    sel b half + half * (part N r + bitW N r) ∎

  -- the supremum of the partial sums, shifted by one
  ⨆-shift : ∀ c (inc : Increasing c) (inc′ : Increasing (λ N → c (ℕ.suc N))) →
    ⨆ c inc ≈ ⨆ (λ N → c (ℕ.suc N)) inc′
  ⨆-shift c inc inc′ = ≤-antisym
    (⨆-lub c inc (λ n → ≤-trans (inc n) (⨆-ub _ inc′ n)))
    (⨆-lub _ inc′ (λ n → ⨆-ub c inc (ℕ.suc n)))

  expansion-cons : ∀ b r → expansion (consR b r) ≈ sel b half + half * expansion r
  expansion-cons b r = begin
    expansion (consR b r)
      ≈⟨ ⨆-shift (λ N → part N (consR b r)) (part-inc (consR b r)) (λ N → part-inc (consR b r) (ℕ.suc N)) ⟩
    ⨆ (λ N → part (ℕ.suc N) (consR b r)) (λ N → part-inc (consR b r) (ℕ.suc N))
      ≈⟨ ⨆-cong _ incS (λ N → part-cons b N r) ⟩
    ⨆ (λ N → sel b half + half * part N r) incS
      ≈⟨ sym (+-⨆ (sel b half) (λ N → half * part N r) incH incS) ⟩
    sel b half + ⨆ (λ N → half * part N r) incH
      ≈⟨ +-cong refl (sym (*-⨆ half (λ N → part N r) (part-inc r) incH)) ⟩
    sel b half + half * expansion r ∎
    where
      incH : Increasing (λ N → half * part N r)
      incH N = *-mono half (part-inc r N)
      incS : Increasing (λ N → sel b half + half * part N r)
      incS N = +-mono ≤-refl (incH N)
