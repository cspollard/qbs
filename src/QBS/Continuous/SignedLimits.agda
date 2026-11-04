{-# OPTIONS --safe --without-K #-}

-- Limits of signed expectations (plan 03, "Signed layer").
--   * `SgConv a l`: signed values a n → l, as `ConvEps.SConv` on representatives (tolerance ½ᵏ, cross-added);
--     it respects `≃` (`SgConv-cong`), adds (`SgConv-+`) and scales (`SgConv-scale`);
--   * `dct-Ex`: dominated convergence in the vocabulary of `SignedExpect` (`DominatedSigned.dct-signed`);
--   * `deriv-Ex`: differentiation under the integral along steps ½ⁿ, without division: if the difference quotients
--     2ⁿ (f n − f₀) converge pointwise (where g is finite) to f′ and are dominated by g, then
--     2ⁿ (Ex f n − Ex f₀) → Ex f′.
-- Route: `SgConv-cong` from the witnesses of `≃` (finite, absorbed into the tolerance by `cancel-bnd`); `dct-Ex` is
-- `dct-signed` with the integrability proofs of `Int-dom`; `deriv-Ex` is `dct-Ex` for
-- dₙ = scaleT 2ⁿ (f n +T -T f₀), then `Ex-scale`, `Ex-+`, `Ex-neg` and `SgConv-cong`.
--   Skeleton: holes first.
module QBS.Continuous.SignedLimits where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; _^_)
open import Data.Product.Base using (_,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.ConvEps using (module ConvEps)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)

module SignedLimits (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; ≤-refl) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; Sg; _≃_; _+S_; _*S_; -S_; ι)
  open Sg
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open ConvEps lem₁ using (SConv)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _+T_; -T_; scaleT)
  open SignedExpect lem₁ using (Int; Ex; Int-dom)
  open QBS
  open Hom

  SgConv : (ℕ → Sg) → Sg → Set₁
  SgConv a l = SConv (λ n → pos (a n)) (λ n → neg (a n)) (pos l) (neg l)

  SgConv-cong : ∀ {a b l l′} → (∀ n → a n ≃ b n) → l ≃ l′ → SgConv a l → SgConv b l′
  SgConv-cong = ?

  SgConv-+ : ∀ {a b l m} → SgConv a l → SgConv b m → SgConv (λ n → a n +S b n) (l +S m)
  SgConv-+ = ?

  SgConv-neg : ∀ {a l} → SgConv a l → SgConv (λ n → -S a n) (-S l)
  SgConv-neg = ?

  SgConv-scale : ∀ c {a l} → SgConv a l → SgConv (λ n → c *S a n) (c *S l)
  SgConv-scale = ?

  -- 2ⁿ as a signed value
  two^ : ℕ → Sg
  two^ n = ι {nat (2 ^ n)} (2 ^ n , ≤-refl)

  -- pointwise signed convergence of tests wherever g is finite
  PtConv : ∀ {X : QBS S} → (ℕ → SgT X) → SgT X → Hom S X WQ → Set₁
  PtConv {X} f f∞ g = ∀ x → BndQ (map g ⟨$⟩ x) → SConv (λ n → at⁺ (f n) x) (λ n → at⁻ (f n) x) (at⁺ f∞ x) (at⁻ f∞ x)

  Dom : ∀ {X : QBS S} → SgT X → Hom S X WQ → Set₁
  Dom f g = ∀ x → at⁺ f x + at⁻ f x ≤ map g ⟨$⟩ x

  module _ {X : QBS S} (p : C.Pre (XW X)) (g : Hom S X WQ) (gB : Bnd (∫ᴹ {X} p g)) where

    dct-Ex : ∀ (f : ℕ → SgT X) (f∞ : SgT X) → PtConv f f∞ g → (dn : ∀ n → Dom (f n) g) → (d∞ : Dom f∞ g) →
      SgConv (λ n → Ex {X} p (f n) (Int-dom p (f n) g gB (dn n))) (Ex {X} p f∞ (Int-dom p f∞ g gB d∞))
    dct-Ex = ?

    -- derivative along ½ⁿ: f₀ at θ, f n at θ + ½ⁿ, f′ the pointwise derivative
    deriv-Ex : ∀ (f₀ f′ : SgT X) (f : ℕ → SgT X) (i₀ : Int {X} p f₀) (i : ∀ n → Int {X} p (f n)) →
      PtConv (λ n → scaleT (two^ n) (f n +T -T f₀)) f′ g →
      (∀ n → Dom (scaleT (two^ n) (f n +T -T f₀)) g) → (d′ : Dom f′ g) →
      SgConv (λ n → two^ n *S (Ex {X} p (f n) (i n) +S -S Ex {X} p f₀ i₀)) (Ex {X} p f′ (Int-dom p f′ g gB d′))
    deriv-Ex = ?
