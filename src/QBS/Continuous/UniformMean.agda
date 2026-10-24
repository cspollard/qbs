{-# OPTIONS --safe --without-K #-}

-- The mean of the uniform distribution on [0,1] is ½: ∫ expansion dμ = ½, by monotone convergence
-- over the partial sums Σ_{k<n} rₖ 2^{-(k+1)} and the bit probability P(rₖ = true) = ½.
-- Consequently the soft-conditioned uniform draw (weight u) has total mass ½.
module QBS.Continuous.UniformMean where

import Level as L
open import Data.Empty using (⊥)
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_; proj₁)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.PiLambda using (Cyl; cylTop; cylAnd; cylResp)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Clopen using (Cl; leaf; split)
open import QBS.Analysis.ClopenMeasure using (module Premeasure)
open import QBS.Analysis.Regular using (module Regularity)
open import QBS.Analysis.Interleave using (module Product)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion
open import QBS.Continuous.FairCoin

module UniformMean (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero; hp-double; arch) renaming (half+half to hh)
  open Integration A
  open Measurable A using (Fun)
  open FairCoin lem₁ using (fairCoin; fairCoin-cyl)
  open Expansion A half hh
  open Series A
  open Indicators A (lemOf lem₁) using (χ; χ-in; χ-out; Fun-χ; I-const-mass)
  open Premeasure R using (μ0)
  open Product R using (half-double)
  open Regularity R (lemOf lem₁) using (bitT)
  open SetoidReasoning setoid

  ----------------------------------------------------------------------------
  -- the tolerances are the powers of a half

  hp≈hpow : ∀ n → hp n ≈ hpow n
  hp≈hpow zero = hp-zero
  hp≈hpow (suc n) = begin
    hp (suc n)                               ≈⟨ sym (*-identityˡ (hp (suc n))) ⟩
    1# * hp (suc n)                          ≈⟨ *-cong (sym hh) refl ⟩
    (half + half) * hp (suc n)               ≈⟨ distribʳ (hp (suc n)) half half ⟩
    half * hp (suc n) + half * hp (suc n)    ≈⟨ sym (distribˡ half (hp (suc n)) (hp (suc n))) ⟩
    half * (hp (suc n) + hp (suc n))         ≈⟨ *-cong refl (hp-double n) ⟩
    half * hp n                              ≈⟨ *-cong refl (hp≈hpow n) ⟩
    half * hpow n                            ∎

  -- Σ_k 2^{-(k+1)} = 1
  geom-sum : ∑ᶠ (λ n → half * hpow n) ≈ 1#
  geom-sum = ≤-antisym
    (⨆-lub (psum a) (psum-inc a) psum-≤1)
    (arch (λ n → ≤-trans (≤-reflexive (sym (geom n)))
      (+-mono (⨆-ub (psum a) (psum-inc a) n) (≤-reflexive (sym (hp≈hpow n))))))
    where a = λ n → half * hpow n

  ----------------------------------------------------------------------------
  -- the probability of a single bit is ½

  μ0-bitT : ∀ n b → μ0 (bitT n b) ≈ half
  μ0-bitT zero true = trans (*-cong refl (+-identityˡ 1#)) (*-identityʳ half)
  μ0-bitT zero false = trans (*-cong refl (+-identityʳ 1#)) (*-identityʳ half)
  μ0-bitT (suc n) b = trans (half-double (μ0 (bitT n b))) (μ0-bitT n b)

  bitU : ℕ → Pred
  bitU n x = x n ≡ true

  bitCyl : ∀ n → Cyl (bitU n)
  bitCyl n = cylResp (λ x → (λ (_ , p) → p) , (λ p → _ , p)) (cylAnd cylTop n true)

  ----------------------------------------------------------------------------
  -- the expectation of the binary expansion

  sel-scale : ∀ b w c → (b ≡ true → c ≈ 1#) → (b ≡ false → c ≈ 0#) → sel b w ≈ w * c
  sel-scale true w c t f = trans (sym (*-identityʳ w)) (*-cong refl (sym (t ≡.refl)))
  sel-scale false w c t f = sym (trans (*-cong refl (f ≡.refl)) (zeroʳ w))

  -- the weighted bit is the scaled indicator of the cylinder {rₙ = true}
  bit-scale : ∀ n r → bitW n r ≈ (half * hpow n) * χ (bitU n) r
  bit-scale n r = sel-scale (lower′ r n) (half * hpow n) (χ (bitU n) r)
    (λ e → χ-in (bitU n) r e)
    (λ e → χ-out (bitU n) r (λ p → absurd (≡.trans (≡.sym e) p)))
    where
      lower′ = λ r n → L.lower r n
      absurd : ∀ {B : Set} → false ≡ true → B
      absurd ()

  I-bit : ∀ n → I fairCoin (bitW n) (Fun-bitW n) ≈ (half * hpow n) * half
  I-bit n = trans (I-scale fairCoin (half * hpow n) (Fun-χ (Cyl-borel (bitCyl n))) (Fun-bitW n) (bit-scale n))
                  (*-cong refl (trans (fairCoin-cyl (bitCyl n)) (μ0-bitT n true)))

  I-part : ∀ N → I fairCoin (part N) (Fun-part N) ≈ psum (λ n → (half * hpow n) * half) N
  I-part zero = trans (I-const-mass fairCoin 0# 0-least) (zeroˡ (mass fairCoin))
  I-part (suc N) = trans (I-add fairCoin (Fun-part (suc N)) (Fun-part N) (Fun-bitW N) (λ r → refl))
                         (+-cong (I-part N) (I-bit N))

  -- E[U] = ½
  mean : I fairCoin expansion Fun-expansion ≈ half
  mean = begin
    I fairCoin expansion Fun-expansion
      ≈⟨ I-sup fairCoin part Fun-part part-inc Fun-expansion (λ r → refl) ⟩
    ⨆ (λ N → I fairCoin (part N) (Fun-part N)) incI
      ≈⟨ ⨆-cong incI (psum-inc b) I-part ⟩
    ∑ᶠ b
      ≈⟨ ∑ᶠ-cong (λ n → *-comm (half * hpow n) half) ⟩
    ∑ᶠ (λ n → half * (half * hpow n))
      ≈⟨ sym (∑ᶠ-scale half (λ n → half * hpow n)) ⟩
    half * ∑ᶠ (λ n → half * hpow n)
      ≈⟨ *-cong refl geom-sum ⟩
    half * 1#
      ≈⟨ *-identityʳ half ⟩
    half ∎
    where b = λ n → (half * hpow n) * half
          incI = λ n → I-mono fairCoin (Fun-part n) (Fun-part (suc n)) (λ x → part-inc x n)
