{-# OPTIONS --safe --without-K #-}

-- First-bit decomposition of the fair coin: for every measurable function h,
--   ∫ h dμ = ½ ∫ h(true :: s) dμ(s) + ½ ∫ h(false :: s) dμ(s),
-- by uniqueness of measures (both sides are probability measures with the same values on
-- finite cylinders: the preimage of a cylinder under `cons b` is a cylinder, and the dyadic
-- measure of a tree is the average of the measures of its two children).
module QBS.Continuous.FirstBit where

open import Level using (lift; lower)
open import Function.Base using (const)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Borel.PiLambda using (Cyl; cylTop; cylAnd; cylResp)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Mixture using (module Mixture)
open import QBS.Analysis.Uniqueness using (module Uniqueness)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Clopen using (Cl; leaf; split; eval; eval-ext; cons; tl)
open import QBS.Analysis.ClopenMeasure using (module Premeasure)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.CoinSets using (module CoinSets)
open import QBS.Continuous.FairCoin
open import QBS.Classical using (LEM₁)

----------------------------------------------------------------------------
-- prepending a bit pulls cylinders back to cylinders

private
  ⊥-cyl : Cyl (λ _ → ⊥)
  ⊥-cyl = cylResp (λ x → (λ ((_ , e₁) , e₂) → bad e₁ e₂) , (λ ()))
                  (cylAnd (cylAnd cylTop 0 true) 0 false)
    where bad : ∀ {b : Bool} → b ≡ true → b ≡ false → ⊥
          bad ≡.refl ()

pullCyl : ∀ b {U} → Cyl U → Cyl (λ x → U (cons b x))
pullCyl b cylTop = cylTop
pullCyl b (cylAnd {U} c zero b′) = go b b′ (pullCyl b c)
  where
    go : ∀ b b′ → Cyl (λ x → U (cons b x)) → Cyl (λ x → U (cons b x) × (b ≡ b′))
    go true true c′ = cylResp (λ x → (λ u → u , ≡.refl) , proj₁) c′
    go false false c′ = cylResp (λ x → (λ u → u , ≡.refl) , proj₁) c′
    go true false c′ = cylResp (λ x → (λ ()) , (λ ())) ⊥-cyl
    go false true c′ = cylResp (λ x → (λ ()) , (λ ())) ⊥-cyl
pullCyl b (cylAnd c (suc n) b′) = cylAnd (pullCyl b c) n b′
pullCyl b (cylResp e c) = cylResp (λ x → e (cons b x)) (pullCyl b c)

private
  bool-ext : ∀ {x y : Bool} → (x ≡ true → y ≡ true) → (y ≡ true → x ≡ true) → x ≡ y
  bool-ext {true} {true} f g = ≡.refl
  bool-ext {true} {false} f g with f ≡.refl
  ... | ()
  bool-ext {false} {true} f g with g ≡.refl
  ... | ()
  bool-ext {false} {false} f g = ≡.refl

-- a tree whose children are `t₂` (first bit false) and `t₁` (first bit true) is `split t₂ t₁`
split-eval : ∀ t t₁ t₂ → (∀ s → eval t₁ s ≡ eval t (cons true s)) → (∀ s → eval t₂ s ≡ eval t (cons false s)) →
  ∀ x → eval t x ≡ eval (split t₂ t₁) x
split-eval t t₁ t₂ h₁ h₂ x with x 0 in e
... | true = ≡.trans (eval-ext t go) (≡.sym (h₁ (tl x)))
  where go : ∀ n → x n ≡ cons true (tl x) n
        go zero = e
        go (suc n) = ≡.refl
... | false = ≡.trans (eval-ext t go) (≡.sym (h₂ (tl x)))
  where go : ∀ n → x n ≡ cons false (tl x) n
        go zero = e
        go (suc n) = ≡.refl

module FirstBit (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open Integration A
  open Measurable A using (Fun; Fun-const; Fun-pre)
  open FairCoin lem₁ using (fairCoin; fairCoin-cyl)
  open Mixture A half hh
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-in; χ-out; case)
  open Premeasure R using (μ0; μ0-ext)
  open CoinSets (lemOf lem₁) using (cyl→tree)
  open Uniqueness A (lemOf lem₁) using (agree-fun)
  open SetoidReasoning setoid

  pushT pushF : Measure
  pushT = push {consR true} (measurable-cons true) fairCoin
  pushF = push {consR false} (measurable-cons false) fairCoin

  -- ½ μ(true :: ·) + ½ μ(false :: ·)
  firstBit : Measure
  firstBit = mix pushT pushF

  masses : mass fairCoin ≈ mass firstBit
  masses = sym (trans
    (mix-one {a = I pushT (const 1#) (Fun-const 1# ≤-refl)} {b = I pushF (const 1#) (Fun-const 1# ≤-refl)}
      (IsProb-push {consR true} (measurable-cons true) {fairCoin} L-one)
      (IsProb-push {consR false} (measurable-cons false) {fairCoin} L-one))
    (sym L-one))

  χ-pre : ∀ b C x → χ C (consR b x) ≈ χ (λ y → C (cons b y)) x
  χ-pre b C x = case {C (cons b (lower x))}
    (λ v → trans (χ-in C (consR b x) v) (sym (χ-in (λ y → C (cons b y)) x v)))
    (λ nv → trans (χ-out C (consR b x) nv) (sym (χ-out (λ y → C (cons b y)) x nv)))

  -- the measure of the preimage of a cylinder under `cons b`
  term : ∀ b {C} (c : Cyl C) →
    I fairCoin (λ x → χ C (consR b x)) (Fun-pre {h = χ C} {f = consR b} (Fun-χ (Cyl-borel c)) (measurable-cons b))
      ≈ μ0 (proj₁ (cyl→tree (pullCyl b c)))
  term b {C} c = trans
    (I-cong fairCoin {h = λ x → χ C (consR b x)} {h′ = χ (λ x → C (cons b x))} (χ-pre b C)
       (Fun-pre {h = χ C} {f = consR b} (Fun-χ (Cyl-borel c)) (measurable-cons b))
       (Fun-χ (Cyl-borel (pullCyl b c))))
    (fairCoin-cyl (pullCyl b c))

  -- the children of the tree of a cylinder are the trees of its preimages
  child-eval : ∀ b {C} (c : Cyl C) s →
    eval (proj₁ (cyl→tree (pullCyl b c))) s ≡ eval (proj₁ (cyl→tree c)) (cons b s)
  child-eval b {C} c s = bool-ext
    (λ p → proj₁ (proj₂ (cyl→tree c) (cons b s)) (proj₂ (proj₂ (cyl→tree (pullCyl b c)) s) p))
    (λ p → proj₁ (proj₂ (cyl→tree (pullCyl b c)) s) (proj₂ (proj₂ (cyl→tree c) (cons b s)) p))

  agree : ∀ {C} (c : Cyl C) →
    I fairCoin (χ C) (Fun-χ (Cyl-borel c)) ≈ I firstBit (χ C) (Fun-χ (Cyl-borel c))
  agree {C} c = mixcomb {m = I fairCoin (χ C) (Fun-χ (Cyl-borel c))} {m₁ = μ0 t₁} {m₂ = μ0 t₂}
    (trans (fairCoin-cyl c) (μ0-ext t (split t₂ t₁) (split-eval t t₁ t₂ (child-eval true c) (child-eval false c))))
    (sym (term true c)) (sym (term false c))
    where
      t = proj₁ (cyl→tree c)
      t₁ = proj₁ (cyl→tree (pullCyl true c))
      t₂ = proj₁ (cyl→tree (pullCyl false c))

  -- ∫ h dμ = ½ ∫ h(true :: ·) dμ + ½ ∫ h(false :: ·) dμ
  firstBit-fun : ∀ {h} (f : Fun h) →
    I fairCoin h f ≈
      half * I fairCoin (λ x → h (consR true x)) (Fun-pre {f = consR true} f (measurable-cons true))
      + half * I fairCoin (λ x → h (consR false x)) (Fun-pre {f = consR false} f (measurable-cons false))
  firstBit-fun f = agree-fun fairCoin firstBit masses agree f
