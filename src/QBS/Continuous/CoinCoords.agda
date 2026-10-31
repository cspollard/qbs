{-# OPTIONS --safe --without-K #-}

-- Independent coordinates of the fair coin.  `x ↦ (evens x, odds x)` splits the coin into two independent coins
-- (`CoinIndep.fairCoin-indep`); iterating on the odd half gives coordinates `coord i x = evens (odds^i x)`, which are
-- pairwise independent, each with the law of the coin.  Stated for non-negative measurable functions first
-- (`J-indep`), then for bounded signed ones (`E-indep`).
module QBS.Continuous.CoinCoords where

import Level as L
open import Level using (lift; lower)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)

open import QBS.Borel.Core using (Cantor; Measurable)
open import QBS.Borel.Source using (R₁) renaming (down to downR)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Variance using (module Variance)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (evens; odds; evensR; oddsR; mergeR; measurable-evens; measurable-odds; merge-evens; merge-odds)
open import QBS.Analysis.JFubini using (module JFubini)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Borel.Core using (measurable-∘)
open import QBS.Borel.Merge using (measurable-merge₁)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.CoinIndep
open import QBS.Classical using (LEM₁)

module CoinCoords (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-cong; J-irrel; J-scale)
  open Meas (lemOf lem₁) using (Meas; Meas-pre; Meas-⊗; Meas-const; Meas-resp)
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; *-cong; *-comm; *-identityʳ; *-identityˡ)
  open FairCoin lem₁ using (fairCoin)
  open CoinIndep lem₁ using (fairCoin-indep; fairCoin-prob)
  open JFubini (lemOf lem₁) using (J-tensor₁)
  open JParam (lemOf lem₁) using (J-agree)
  open Tensor A (lemOf lem₁) using (tensor₁)
  open SignedIntegral (lemOf lem₁) using (J-const)

  ≡⇒≈ : ∀ {a b} → a ≡.≡ b → a ≈ b
  ≡⇒≈ ≡.refl = refl

  -- the shift past one coordinate, and the i-th coordinate
  shift : ℕ → R₁ → R₁
  shift zero r = r
  shift (suc i) r = shift i (oddsR r)

  coord : ℕ → R₁ → R₁
  coord i r = evensR (shift i r)

  -- measurability of functions of the halves, and of the i-th coordinate
  pe : ∀ {φ} → Meas φ → Meas (λ r → φ (evensR r))
  pe {φ} p = Meas-pre {φ} {evensR} p measurable-evens

  po : ∀ {φ} → Meas φ → Meas (λ r → φ (oddsR r))
  po {φ} p = Meas-pre {φ} {oddsR} p measurable-odds

  measurable-coord : ∀ i → Measurable (downR (coord i))
  measurable-coord zero = measurable-evens
  measurable-coord (suc i) = measurable-∘ measurable-odds (measurable-coord i)

  pc : ∀ {φ} → Meas φ → ∀ i → Meas (λ r → φ (coord i r))
  pc {φ} p i = Meas-pre {φ} {coord i} p (measurable-coord i)

  -- 1. the halves are independent
  split-meas : ∀ {φ ψ} → Meas φ → Meas ψ → Meas (λ r → φ (evensR r) * ψ (oddsR r))
  split-meas {φ} {ψ} p q = Meas-⊗ {λ r → φ (evensR r)} {λ r → ψ (oddsR r)} (pe {φ} p) (po {ψ} q)

  -- merging the two halves back together recovers both factors
  split-merge : ∀ {φ ψ} → Meas φ → Meas ψ → ∀ r s → φ (evensR (mergeR r s)) * ψ (oddsR (mergeR r s)) ≈ φ r * ψ s
  split-merge {φ} {ψ} p q r s = *-cong (Meas-resp p (lower (merge-evens r s))) (Meas-resp q (lower (merge-odds r s)))

  -- the inner integral: φ is constant in the inner variable
  split-inner : ∀ {φ ψ} (p : Meas φ) (q : Meas ψ) r →
    J fairCoin (λ s → φ (evensR (mergeR r s)) * ψ (oddsR (mergeR r s)))
      (Meas-pre {λ r′ → φ (evensR r′) * ψ (oddsR r′)} {mergeR r} (split-meas p q) (measurable-merge₁ (lower r)))
      ≈ φ r * J fairCoin ψ q
  split-inner {φ} {ψ} p q r =
    trans (J-cong fairCoin _ (Meas-⊗ {λ _ → φ r} {ψ} (Meas-const (φ r)) q) (split-merge {φ} {ψ} p q r)) (J-scale fairCoin (φ r) {ψ} q)

  -- the outer integral of `φ · const`
  split-outer : ∀ {φ ψ} (p : Meas φ) (q : Meas ψ) →
    J fairCoin (λ r → φ r * J fairCoin ψ q) (Meas-⊗ {φ} {λ _ → J fairCoin ψ q} p (Meas-const (J fairCoin ψ q)))
      ≈ J fairCoin φ p * J fairCoin ψ q
  split-outer {φ} {ψ} p q =
    trans (J-cong fairCoin (Meas-⊗ {φ} {λ _ → J fairCoin ψ q} p (Meas-const (J fairCoin ψ q)))
                   (Meas-⊗ {λ _ → J fairCoin ψ q} {φ} (Meas-const (J fairCoin ψ q)) p)
                   (λ r → *-comm (φ r) (J fairCoin ψ q)))
      (trans (J-scale fairCoin (J fairCoin ψ q) {φ} p) (*-comm (J fairCoin ψ q) (J fairCoin φ p)))

  J-split : ∀ {φ ψ} (p : Meas φ) (q : Meas ψ) →
    J fairCoin (λ r → φ (evensR r) * ψ (oddsR r)) (split-meas p q) ≈ J fairCoin φ p * J fairCoin ψ q
  J-split {φ} {ψ} p q = trans
    (sym (J-agree (tensor₁ fairCoin fairCoin) fairCoin (split-meas p q) (λ F → fairCoin-indep F)))
    (trans (J-tensor₁ fairCoin fairCoin (split-meas p q))
      (trans (J-cong fairCoin _ (Meas-⊗ {φ} {λ _ → J fairCoin ψ q} p (Meas-const (J fairCoin ψ q))) (split-inner p q))
        (split-outer p q)))

  -- 2. each half, and each coordinate, has the law of the coin
  J-evens : ∀ {φ} (p : Meas φ) → J fairCoin (λ r → φ (evensR r)) (pe {φ} p) ≈ J fairCoin φ p
  J-evens {φ} p = trans
    (J-cong fairCoin (pe {φ} p) (Meas-⊗ {λ r → φ (evensR r)} {λ r → 1#} (pe {φ} p) (po {λ _ → 1#} (Meas-const 1#)))
        (λ r → sym (*-identityʳ (φ (evensR r)))))
    (trans (J-split {φ} {λ _ → 1#} p (Meas-const 1#))
      (trans (*-cong refl (J-const fairCoin-prob 1#)) (*-identityʳ (J fairCoin φ p))))

  J-odds : ∀ {φ} (p : Meas φ) → J fairCoin (λ r → φ (oddsR r)) (po {φ} p) ≈ J fairCoin φ p
  J-odds {φ} p = trans
    (J-cong fairCoin (po {φ} p) (Meas-⊗ {λ r → 1#} {λ r → φ (oddsR r)} (pe {λ _ → 1#} (Meas-const 1#)) (po {φ} p))
        (λ r → sym (*-identityˡ (φ (oddsR r)))))
    (trans (J-split {λ _ → 1#} {φ} (Meas-const 1#) p)
      (trans (*-cong (J-const fairCoin-prob 1#) refl) (*-identityˡ (J fairCoin φ p))))

  J-coord : ∀ {φ} (p : Meas φ) i → J fairCoin (λ r → φ (coord i r)) (pc {φ} p i) ≈ J fairCoin φ p
  J-coord {φ} p zero = J-evens p
  J-coord {φ} p (suc i) = trans (J-irrel fairCoin (pc {φ} p (suc i)) (po {λ r → φ (coord i r)} (pc {φ} p i)))
    (trans (J-odds {λ r → φ (coord i r)} (pc {φ} p i)) (J-coord p i))

  -- 3. coordinates: one factor in coordinate i, one in a later coordinate j
  J-indep : ∀ {φ ψ} (p : Meas φ) (q : Meas ψ) i j (h : i < j) →
    J fairCoin (λ r → φ (coord i r) * ψ (coord j r))
        (Meas-⊗ {λ r → φ (coord i r)} {λ r → ψ (coord j r)} (pc {φ} p i) (pc {ψ} q j))
      ≈ J fairCoin φ p * J fairCoin ψ q
  J-indep {φ} {ψ} p q zero (suc j) h =
    trans (J-irrel fairCoin (Meas-⊗ {λ r → φ (coord zero r)} {λ r → ψ (coord (suc j) r)} (pc {φ} p zero) (pc {ψ} q (suc j)))
                            (Meas-⊗ {λ r → φ (evensR r)} {λ r → ψ (coord j (oddsR r))} (pe {φ} p)
                                (po {λ r → ψ (coord j r)} (pc {ψ} q j))))
      (trans (J-split {φ} {λ r → ψ (coord j r)} p (pc {ψ} q j)) (*-cong refl (J-coord q j)))
  J-indep {φ} {ψ} p q (suc i) (suc j) (s≤s h) =
    trans (J-irrel fairCoin (Meas-⊗ {λ r → φ (coord (suc i) r)} {λ r → ψ (coord (suc j) r)} (pc {φ} p (suc i)) (pc {ψ} q (suc j)))
                            (po {λ r → φ (coord i r) * ψ (coord j r)}
                                (Meas-⊗ {λ r → φ (coord i r)} {λ r → ψ (coord j r)} (pc {φ} p i) (pc {ψ} q j))))
      (trans (J-odds {λ r → φ (coord i r) * ψ (coord j r)}
          (Meas-⊗ {λ r → φ (coord i r)} {λ r → ψ (coord j r)} (pc {φ} p i) (pc {ψ} q j)))
        (J-indep p q i j h))

  ----------------------------------------------------------------------------
  -- bounded signed functions

  open Bounded A using (_≃_; _*S_; finite; mk≃)
  open BoundedRing (lemOf lem₁) using (≃-parts; mul⁺; mul⁻)
  open Lebesgue (lemOf lem₁) using (J-add)
  open OmegaSemiring A using (_+_; 0#; +-cong)
  open SignedIntegral (lemOf lem₁)
  open SF
  open Variance (lemOf lem₁) using (Bdd; _*SF_[_])

  -- precomposition with the i-th coordinate
  coordSF : ℕ → SF fairCoin → SF fairCoin
  coordSF i f = record
    { f⁺ = λ r → f⁺ f (coord i r) ; f⁻ = λ r → f⁻ f (coord i r)
    ; f⁺-meas = pc {f⁺ f} (f⁺-meas f) i ; f⁻-meas = pc {f⁻ f} (f⁻-meas f) i
    ; f⁺-int = SubSemiring.Is-resp finite (sym (J-coord (f⁺-meas f) i)) (f⁺-int f)
    ; f⁻-int = SubSemiring.Is-resp finite (sym (J-coord (f⁻-meas f) i)) (f⁻-int f) }

  coordSF-bdd : ∀ i f → Bdd f → Bdd (coordSF i f)
  coordSF-bdd i f (N , b) = N , λ r → b (coord i r)

  -- same law
  E-coord : ∀ i f → E (coordSF i f) ≃ E f
  E-coord i f = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong {J fairCoin (λ r → f⁺ f (coord i r)) (pc {f⁺ f} (f⁺-meas f) i) + J fairCoin (f⁻ f) (f⁻-meas f)}
            {J fairCoin (f⁺ f) (f⁺-meas f) + J fairCoin (λ r → f⁻ f (coord i r)) (pc {f⁻ f} (f⁻-meas f) i)} {0#} {0#}
            (+-cong (J-coord (f⁺-meas f) i) (sym (J-coord (f⁻-meas f) i))) refl)

  -- the two parts of the product, integrated: kept as separate lemmas so that the types stay small
  prod⁺ : ∀ i j → i < j → (f g : SF fairCoin) (bf : Bdd f) →
    J fairCoin (f⁺ (coordSF i f *SF coordSF j g [ coordSF-bdd i f bf ]))
        (f⁺-meas (coordSF i f *SF coordSF j g [ coordSF-bdd i f bf ]))
      ≈ J fairCoin (f⁺ f) (f⁺-meas f) * J fairCoin (f⁺ g) (f⁺-meas g) + J fairCoin (f⁻ f) (f⁻-meas f) * J fairCoin
          (f⁻ g) (f⁻-meas g)
  prod⁺ i j h f g bf = trans (mul⁺ (coordSF i f) (coordSF j g) (coordSF-bdd i f bf))
    (+-cong (J-indep {f⁺ f} {f⁺ g} (f⁺-meas f) (f⁺-meas g) i j h) (J-indep {f⁻ f} {f⁻ g} (f⁻-meas f) (f⁻-meas g) i j h))

  prod⁻ : ∀ i j → i < j → (f g : SF fairCoin) (bf : Bdd f) →
    J fairCoin (f⁻ (coordSF i f *SF coordSF j g [ coordSF-bdd i f bf ]))
        (f⁻-meas (coordSF i f *SF coordSF j g [ coordSF-bdd i f bf ]))
      ≈ J fairCoin (f⁺ f) (f⁺-meas f) * J fairCoin (f⁻ g) (f⁻-meas g) + J fairCoin (f⁻ f) (f⁻-meas f) * J fairCoin
          (f⁺ g) (f⁺-meas g)
  prod⁻ i j h f g bf = trans (mul⁻ (coordSF i f) (coordSF j g) (coordSF-bdd i f bf))
    (+-cong (J-indep {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g) i j h) (J-indep {f⁻ f} {f⁺ g} (f⁻-meas f) (f⁺-meas g) i j h))

  -- the expectation of a product of functions of two different coordinates is the product of expectations
  E-indep : ∀ i j → i < j → (f g : SF fairCoin) (bf : Bdd f) →
    E (coordSF i f *SF coordSF j g [ coordSF-bdd i f bf ]) ≃ E f *S E g
  E-indep i j h f g bf = ≃-parts (prod⁺ i j h f g bf) (prod⁻ i j h f g bf)



