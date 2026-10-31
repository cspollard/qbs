{-# OPTIONS --safe --without-K #-}

-- Independence of the even and odd bits of the fair coin: the product of two fair coins,
-- interleaved by `mergeC`, is the fair coin (`tensor₁ fairCoin fairCoin ≈ fairCoin` on every
-- measurable function).  Both agree on finite cylinders because the dyadic measure of an
-- interleaving of clopen trees is the product of their measures (`Analysis/Interleave.agda`).
module QBS.Continuous.CoinIndep where

open import Data.Empty using (⊥)
open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.PiLambda using (Cyl)
open import QBS.Borel.Merge using (Cyl-borel; Cyl-rect; mergeC)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Uniqueness using (module Uniqueness)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.Clopen using (Cl; eval; eval-ext)
open import QBS.Analysis.ClopenMeasure using (module Premeasure)
open import QBS.Analysis.OpenMeasure using (and-intro; and-elim)
open import QBS.Analysis.CoinSets using (module CoinSets)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.Interleave
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Continuous.Sample using (evens; odds; merge-split)
open import QBS.Continuous.FairCoin
open import QBS.Classical using (LEM₁)

module CoinIndep (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  open FairCoin lem₁
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Integration A
  open Measurable A using (Fun)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ)
  open Tensor A (lemOf lem₁)
  open CoinSets (lemOf lem₁) using (cyl→tree)
  open Product (lowerRealsArch (lemOf lem₁)) using (μ0-interleave)
  open Premeasure (lowerRealsArch (lemOf lem₁)) using (μ0; μ0-ext)
  open Uniqueness A (lemOf lem₁) using (agree-fun)

  private
    bool-ext : ∀ {x y : Bool} → (x ≡ true → y ≡ true) → (y ≡ true → x ≡ true) → x ≡ y
    bool-ext {true} {true} f g = ≡.refl
    bool-ext {true} {false} f g with f ≡.refl
    ... | ()
    bool-ext {false} {true} f g with g ≡.refl
    ... | ()
    bool-ext {false} {false} f g = ≡.refl

  -- the clopen tree of a cylinder accepts the merge of `a` and `s` iff the trees of its two factors accept `a`, resp. `s`
  tree-fw : ∀ {U} (c : Cyl U) (a s : Cantor) →
    eval (proj₁ (cyl→tree c)) (mergeC a s) ≡ true →
    eval (proj₁ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c))) a
      ∧ eval (proj₁ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c))) s ≡ true
  tree-fw c a s h =
    let (p₁ , p₂) = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (Cyl-rect c))))) a s (proj₂ (proj₂ (cyl→tree c) (mergeC a s)) h)
    in and-intro (proj₁ (proj₂ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c)) a) p₁)
                 (proj₁ (proj₂ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c)) s) p₂)

  tree-bw : ∀ {U} (c : Cyl U) (a s : Cantor) →
    eval (proj₁ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c))) a
      ∧ eval (proj₁ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c))) s ≡ true →
    eval (proj₁ (cyl→tree c)) (mergeC a s) ≡ true
  tree-bw c a s h =
    let (e₁ , e₂) = and-elim (eval (proj₁ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c))) a)
                             (eval (proj₁ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c))) s) h
    in proj₁ (proj₂ (cyl→tree c) (mergeC a s))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (Cyl-rect c))))) a s
            (proj₂ (proj₂ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c)) a) e₁)
            (proj₂ (proj₂ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c)) s) e₂))

  -- the clopen tree of a cylinder is the interleaving of the trees of its two factors
  tree-split : ∀ {U} (c : Cyl U) (x : Cantor) →
    eval (proj₁ (cyl→tree c)) x ≡
    eval (interleave (proj₁ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c)))
                     (proj₁ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c)))) x
  tree-split {U} c x =
    ≡.trans (shift (proj₁ (cyl→tree c)))
      (≡.trans (bool-ext (tree-fw c a s) (tree-bw c a s))
        (≡.trans (≡.sym (eval-interleave t₁ t₂ a s)) (≡.sym (shift (interleave t₁ t₂)))))
    where
      t₁ = proj₁ (cyl→tree (P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c))
      t₂ = proj₁ (cyl→tree (P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c))
      a = evens x
      s = odds x
      shift : ∀ T → eval T x ≡ eval T (mergeC a s)
      shift T = eval-ext T (λ n → ≡.sym (merge-split x n))

  -- the two factors agree with the coin on every finite cylinder ...
  indep-cyl : ∀ {U} (c : Cyl U) →
    I (tensor₁ fairCoin fairCoin) (χ U) (Fun-χ (Cyl-borel c)) ≈ I fairCoin (χ U) (Fun-χ (Cyl-borel c))
  indep-cyl {U} c =
    trans (lhs-cyl fairCoin fairCoin c)
      (trans (*-cong (fairCoin-cyl c₂) (fairCoin-cyl c₁))
        (trans (*-comm _ _)
          (trans (sym (μ0-interleave t₁ t₂))
            (trans (μ0-ext (interleave t₁ t₂) tU (λ x → ≡.sym (tree-split c x)))
                   (sym (fairCoin-cyl c))))))
    where
      c₁ = P₁.rc₁ (λ _ → fairCoin) (constK fairCoin) c
      c₂ = P₁.rc₂ (λ _ → fairCoin) (constK fairCoin) c
      tU = proj₁ (cyl→tree c)
      t₁ = proj₁ (cyl→tree c₁)
      t₂ = proj₁ (cyl→tree c₂)

  -- the coin is a probability measure
  fairCoin-prob : IsProb fairCoin
  fairCoin-prob = L-one

  -- ... hence on every measurable function: ∫∫ h (merge a s) dμ(a) dμ(s) = ∫ h dμ
  fairCoin-indep : ∀ {h} (f : Fun h) → I (tensor₁ fairCoin fairCoin) h f ≈ I fairCoin h f
  fairCoin-indep = agree-fun (tensor₁ fairCoin fairCoin) fairCoin
    (trans (mass-tensor₁ fairCoin fairCoin)
      (trans (*-cong fairCoin-prob fairCoin-prob) (trans (*-identityˡ 1#) (sym fairCoin-prob))))
    indep-cyl
