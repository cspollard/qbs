{-# OPTIONS --safe --without-K #-}

-- The cumulative distribution function of the uniform distribution on [0,1]: `P(u ≤ t) = t`,
-- the integral of the indicator of `[0,t]`, for every t ≤ 1.
--
-- Let F t = μ{expansion ≤ t} (μ the fair coin).  Splitting off the first bit (`FirstBit`) and the
-- self-similarity `expansion (b :: r) = b/2 + expansion r / 2` (`ExpansionCons`) give
--   F(t/2) = ½ Z(t) + ½ F(t)  with Z(t) ≤ F(0),   F(½ + t/2) = ½ F(t) + ½,
-- and `Analysis/SelfSimilar` shows these laws force F t = t.  The measurability of the test function
-- `cdfTest t` uses that {x | β x ≤ t} is Borel for a measurable β (`Analysis/Threshold`).
module QBS.Continuous.UniformCDF where

import Level as L
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Bool.Base using (true; false)
open import Data.Product.Base using (_,_; proj₁; proj₂; _×_)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (lift; lower)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core using (Hom)
open Hom using ()
open import QBS.Borel.Core using (Pred; _≐_)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Clopen using (cons)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.LowerReals using (LowerRealsOmega; _⊑_; mk⊑; zeroC; oneC)
open _⊑_
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch; halfC)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.SelfSimilar using (module SelfSimilar)
open import QBS.Analysis.Threshold using (module Threshold)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Continuous.Sample using (module UnitInterval; S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.SubProb
open import QBS.Continuous.SubModel using (module SubModel)

module UniformCDF (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open UnitInterval A lem using (AQ)
  open ContinuousSub A (lemOf lem₁) funext
  open SubModel lem₁ funext using (uniformSub)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half) renaming (half+half to hh)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion)
  open ExpansionCons A half hh using (expansion-cons)
  open HalfOrder A R
  open Integration A
  open Measurable A using (Fun; Fun-pre; Fun-ext)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun; χ-pre)
  open Threshold (lemOf lem₁)
  open Indicators A (lemOf lem₁) using (χ; Fun-χ; χ-in; χ-out; χ-cong; χ-≤1; case; I-const)

  ----------------------------------------------------------------------------
  -- the test function

  z₀ : R₁
  z₀ = lift (λ _ → false)

  -- the value of a proposition: 1 if it holds, else 0
  ι : Set → ∣A∣
  ι P = χ (λ _ → P) z₀

  ι-cong : ∀ {P Q : Set} → (P → Q) → (Q → P) → ι P ≈ ι Q
  ι-cong f g = χ-cong (λ _ → f , g) z₀

  -- the indicator of a threshold set, pointwise
  ι-χ : ∀ (h : R₁ → ∣A∣) t r → ι (Le (h r) t) ≈ χ (Below h t) r
  ι-χ h t r = case {Le (h r) t}
    (λ y → trans (χ-in (λ _ → Le (h r) t) z₀ y) (sym (χ-in (Below h t) r y)))
    (λ n → trans (χ-out (λ _ → Le (h r) t) z₀ n) (sym (χ-out (Below h t) r n)))

  -- the indicator of [0,t] as a test function on the unit interval
  cdfTest : ∣A∣ → Hom S AQ AQ
  cdfTest t = record
    { map = record
        { to = λ a → ι (Le (proj₁ a) t) , χ-≤1 (λ _ → Le (proj₁ a) t) z₀
        ; cong = λ {a} {b} e → ι-cong
            (λ l q m → l q (ap (proj₂ e) q m))
            (λ l q m → l q (ap (proj₁ e) q m))
        }
    ; map-random = λ {α} mα → Fun-ext (λ r → sym (ι-χ (λ r′ → proj₁ (α r′)) t r)) (Fun-χ (Below-borel mα t))
    }

  ----------------------------------------------------------------------------
  -- the distribution function F t = μ{expansion ≤ t}

  Fb : ∀ t → Fun (χ (Below expansion t))
  Fb t = Fun-χ (Below-borel Fun-expansion t)

  F : ∣A∣ → ∣A∣
  F t = I fairCoin (χ (Below expansion t)) (Fb t)

  χ-sub : ∀ {V W : Pred} → (∀ c → V c → W c) → ∀ x → χ V x ≤ χ W x
  χ-sub {V} {W} f x = case {V (lower x)}
    (λ v → ≤-trans (≤-reflexive (χ-in V x v)) (≤-reflexive (sym (χ-in W x (f _ v)))))
    (λ nv → ≤-trans (≤-reflexive (χ-out V x nv)) 0-least)

  F-mono : ∀ {s t} → s ≤ t → F s ≤ F t
  F-mono {s} {t} s≤t = I-mono fairCoin (Fb s) (Fb t) (χ-sub (λ c l q m → ap s≤t q (l q m)))

  F-cong : ∀ {s t} → s ≈ t → F s ≈ F t
  F-cong e = ≤-antisym (F-mono (proj₁ e)) (F-mono (proj₂ e))

  F-1 : F 1# ≈ 1#
  F-1 = trans (I-cong fairCoin {h′ = λ _ → 1#} (λ x → χ-in (Below expansion 1#) x (λ q m → ap (expansion≤1 x) q m))
                (Fb 1#) (Fun-const 1# ≤-refl)) L-one
    where open Measurable A using (Fun-const)

  -- the two halves of the fair coin
  Z : ∣A∣ → ∣A∣
  Z s = I fairCoin (λ x → χ (Below expansion (half * s)) (consR true x))
          (Fun-pre {h = χ (Below expansion (half * s))} {f = consR true} (Fb (half * s)) (measurable-cons true))

  -- expansion of a prepended bit, as an inequality-friendly equation
  exp-false : ∀ r → expansion (consR false r) ≈ half * expansion r
  exp-false r = trans (expansion-cons false r) (+-identityˡ _)

  exp-true : ∀ r → expansion (consR true r) ≈ half + half * expansion r
  exp-true r = expansion-cons true r

  -- the set equivalences, for the thresholds t = ½s and t = ½ + ½s
  false-set : ∀ s c → Below expansion (half * s) (cons false c) → Below expansion s c
  false-set s c l = ⊑→Le (proj₁ (false-iff {x = expansion (lift c)} {y = s} (exp-false (lift c))) (Le→⊑ l))

  false-set′ : ∀ s c → Below expansion s c → Below expansion (half * s) (cons false c)
  false-set′ s c l = ⊑→Le (proj₂ (false-iff {x = expansion (lift c)} {y = s} (exp-false (lift c))) (Le→⊑ l))

  true-set : ∀ s c → Below expansion (half + half * s) (cons true c) → Below expansion s c
  true-set s c l = ⊑→Le (proj₁ (true-iff {x = expansion (lift c)} {y = s} (exp-true (lift c))) (Le→⊑ l))

  true-set′ : ∀ s c → Below expansion s c → Below expansion (half + half * s) (cons true c)
  true-set′ s c l = ⊑→Le (proj₂ (true-iff {x = expansion (lift c)} {y = s} (exp-true (lift c))) (Le→⊑ l))

  FL : ∀ s → s ≤ 1# → F (half * s) ≈ half * Z s + half * F s
  FL s s≤1 = mix2 (firstBit-fun (Fb (half * s))) refl
    (I-cong fairCoin
      (λ x → trans (χ-pre false (Below expansion (half * s)) x)
                   (χ-cong (λ c → false-set s c , false-set′ s c) x))
      (Fun-pre {h = χ (Below expansion (half * s))} {f = consR false} (Fb (half * s)) (measurable-cons false)) (Fb s))

  Zb : ∀ s → Fun (λ x → χ (Below expansion (half * s)) (consR true x))
  Zb s = Fun-pre {h = χ (Below expansion (half * s))} {f = consR true} (Fb (half * s)) (measurable-cons true)

  ZL : ∀ s → s ≤ 1# → Z s ≤ F 0#
  ZL s s≤1 = I-mono fairCoin (Zb s) (Fb 0#) (λ x →
    ≤-trans (≤-reflexive (χ-pre true (Below expansion (half * s)) x))
      (χ-sub (λ c l → ⊑→Le (true-null {x = expansion (lift c)} {s = s} (exp-true (lift c)) s≤1 (Le→⊑ l))) x))

  Z0 : Z 0# ≤ 0#
  Z0 = ≤-trans (I-mono fairCoin (Zb 0#) (Fun-const 0# 0-least) (λ x →
         ≤-trans (≤-reflexive (χ-pre true (Below expansion (half * 0#)) x))
           (≤-reflexive (χ-out (λ y → Below expansion (half * 0#) (cons true y)) x
             (λ l → half≰0 (true-pos {x = expansion (lift (lower x))} (exp-true (lift (lower x))) (Le→⊑ l)))))))
       (≤-reflexive (I-const fairCoin L-one 0# 0-least))
    where open Measurable A using (Fun-const)

  FR : ∀ s → s ≤ 1# → F (half + half * s) ≈ half * F s + half * 1#
  FR s s≤1 = mix2 (firstBit-fun (Fb (half + half * s)))
    (I-cong fairCoin
      (λ x → trans (χ-pre true (Below expansion (half + half * s)) x)
                   (χ-cong (λ c → true-set s c , true-set′ s c) x))
      (Fun-pre {h = χ (Below expansion (half + half * s))} {f = consR true} (Fb (half + half * s)) (measurable-cons true)) (Fb s))
    (trans (I-cong fairCoin {h′ = λ _ → 1#}
      (λ x → trans (χ-pre false (Below expansion (half + half * s)) x)
                   (χ-in (λ y → Below expansion (half + half * s) (cons false y)) x
                     (λ q m → ap (false-top {x = expansion x} {s = s} (exp-false x) (expansion≤1 x)) q m)))
      (Fun-pre {h = χ (Below expansion (half + half * s))} {f = consR false} (Fb (half + half * s)) (measurable-cons false))
      (Fun-const 1# ≤-refl))
      (I-const fairCoin L-one 1# ≤-refl))
    where open Measurable A using (Fun-const)

  open SelfSimilar A R tot-half F Z using (selfSimilar)

  cdf : ∀ (t : ∣A∣) → t ≤ OmegaSemiring.1# A → ∫ uniformSub (cdfTest t) ≈ t
  cdf t t≤1 = trans (I-cong fairCoin (λ r → ι-χ expansion t r)
                      (Hom.map-random (cdfTest t) {λ r → expansion r , expansion≤1 r} Fun-expansion) (Fb t))
                    (selfSimilar F-cong F-mono F-1 FL ZL Z0 FR t t≤1)
