{-# OPTIONS --safe --without-K #-}

-- Threshold sets of measurable lower-real functions: {x | h x ≤ t} is Borel (the complement of
-- the union over rationals q of {q < h x} ∩ {q ∉ t}), plus two facts about the lower reals:
-- comparison with ½ is total, and ½ is not ≤ 0.
module QBS.Analysis.Threshold where

open import Level using (lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality.Core as ≡

open import Data.Rational.Unnormalised.Base using (_<_)
open import QBS.Analysis.RationalLemmas
open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsArch using (halfC)
open import QBS.Analysis.LevelSets
open import QBS.Classical using (LEM₀)
open Cut
open _⊑_

module Threshold (lem : LEM₀) where
  open LevelSets lem using (LS; Lvl; borel-prop)
  open Measurable (LowerRealsOmega lem) using (Fun)

  -- the order on cuts as a proposition in Set
  Le : Cut → Cut → Set
  Le x y = ∀ q → mem x q → mem y q

  Le→⊑ : ∀ {x y} → Le x y → x ⊑ y
  Le→⊑ = mk⊑

  ⊑→Le : ∀ {x y} → x ⊑ y → Le x y
  ⊑→Le = ap

  Below : (R₁ → Cut) → Cut → Pred
  Below h t c = Le (h (lift c)) t

  Below-borel : ∀ {h} → Fun h → ∀ t → Borel (Below h t)
  Below-borel {h} f t = resp e (compl (⋃ cells))
    where
      cells : ∀ k → Borel (λ c → Lvl h (enumQ k) c × (mem t (enumQ k) → ⊥))
      cells k = inter₂ (LS f (enumQ k)) (borel-prop (mem t (enumQ k) → ⊥))

      fwd : ∀ x → ((Σ ℕ (λ k → Lvl h (enumQ k) x × (mem t (enumQ k) → ⊥))) → ⊥) → Le (h (lift x)) t
      fwd x nex q mq with lem (mem t q)
      ... | inj₁ yes = yes
      ... | inj₂ no with enumQ-surj q
      ...   | k , ≡.refl = ⊥-elim (nex (k , mq , no))

      e : (λ x → (Σ ℕ (λ k → Lvl h (enumQ k) x × (mem t (enumQ k) → ⊥))) → ⊥) ≐ Below h t
      e x = fwd x , (λ le (k , m , nm) → nm (le (enumQ k) m))

  -- comparison with ½ is total
  tot-half : ∀ t → t ⊑ halfC ⊎ halfC ⊑ t
  tot-half t with lem (Σ ℚᵘ (λ q → mem t q × ((q < ½) → ⊥)))
  ... | inj₂ none = inj₁ (mk⊑ λ q m → dec q m (lem (q < ½)))
    where dec : ∀ q → mem t q → (q < ½) ⊎ ((q < ½) → ⊥) → q < ½
          dec q m (inj₁ lt) = lt
          dec q m (inj₂ nlt) = ⊥-elim (none (q , m , nlt))
  ... | inj₁ (q , m , nlt) = inj₂ (mk⊑ λ p lt → down t (<-≤ (<-≤-trans lt (½≤q (≤-or-> ½ q)))) m)
    where ½≤q : (Data.Rational.Unnormalised.Base._≤_ ½ q) ⊎ (q < ½) → Data.Rational.Unnormalised.Base._≤_ ½ q
          ½≤q (inj₁ le) = le
          ½≤q (inj₂ lt) = ⊥-elim (nlt lt)

  half≰0 : halfC ⊑ zeroC → ⊥
  half≰0 h = <-irrefl ≃-refl (ap h 0ℚᵘ 0<½)
