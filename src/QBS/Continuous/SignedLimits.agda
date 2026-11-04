{-# OPTIONS --safe --without-K #-}

-- Limits of signed expectations (plan 03, "Signed layer").
--   * `SgConv a l`: signed values a n → l, as `ConvEps.SConv` on representatives (tolerance ½ᵏ, cross-added);
--     it respects `≃` (`SgConv-cong`), adds (`SgConv-+`) and scales (`SgConv-scale`);
--   * `dct-Ex`: dominated convergence in the vocabulary of `SignedExpect` (`DominatedSigned.dct-signed`);
--   * `deriv-Ex`: differentiation under the integral along steps ½ⁿ, without division: if the difference quotients
--     2ⁿ (f n − f₀) converge pointwise (where g is finite) to f′ and are dominated by g, then
--     2ⁿ (Ex f n − Ex f₀) → Ex f′.
-- Route: `SgConv-cong` from the witnesses of `≃` (finite, added to both sides and cancelled, `SignedLimitsAlg.cong-le`);
-- `SgConv-scale` takes a smaller tolerance ½ᵐ⁺ᵏ (`SignedLimitsAlg.small-scale`, `scale-ineq`); `dct-Ex` is
-- `dct-signed` with the integrability proofs of `Int-dom`; `deriv-Ex` is `dct-Ex` for
-- dₙ = scaleT 2ⁿ (f n +T -T f₀), then `Ex-scale`, `Ex-+`, `Ex-neg` and `SgConv-cong`.
module QBS.Continuous.SignedLimits where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc; _^_) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)

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
open import QBS.Continuous.DominatedSigned using (module DominatedSigned)
open import QBS.Continuous.SignedLimitsAlg using (module SignedLimitsAlg)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.Signed using (SubSemiring)

module SignedLimits (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; ≤-refl; ≤-trans; ≤-reflexive; +-comm; +-cong; refl; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; Sg; _≃_; _+S_; _*S_; -S_; ι; finite; ≃-refl; ≃-trans; +S-cong; *S-congʳ)
  open Sg
  open _≃_
  open SubSemiring finite using (Is-+)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open SignedLimitsAlg lem₁ using (cong-le; small-scale; scale-ineq)
  open DominatedSigned lem₁ using (dct-signed)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open ConvEps lem₁ using (SConv; add-tol)
  open SignedTest lem₁ using (SgT; posT; negT; at⁺; at⁻; _+T_; -T_; scaleT)
  open SignedExpect lem₁ using (Int; Ex; Int-dom; Int-+; Int-neg; Int-scale; Ex-irr; Ex-+; Ex-neg; Ex-scale)
  open QBS
  open Hom

  SgConv : (ℕ → Sg) → Sg → Set₁
  SgConv a l = SConv (λ n → pos (a n)) (λ n → neg (a n)) (pos l) (neg l)

  SgConv-cong : ∀ {a b l l′} → (∀ n → a n ≃ b n) → l ≃ l′ → SgConv a l → SgConv b l′
  SgConv-cong {a} {b} {l} {l′} e el sc k = proj₁ (sc k) , λ n le →
    cong-le (pos (a n)) (neg (a n)) (pos (b n)) (neg (b n)) (pos l) (neg l) (pos l′) (neg l′) (_≃_.k (e n)) (_≃_.k el) _
      (neg-fin (a n)) (neg-fin l) (k-fin (e n)) (k-fin el) (proj₁ (proj₂ (sc k) n le)) (eq (e n)) (eq el) ,
    cong-le (pos l) (neg l) (pos l′) (neg l′) (pos (a n)) (neg (a n)) (pos (b n)) (neg (b n)) (_≃_.k el) (_≃_.k (e n)) _
      (neg-fin l) (neg-fin (a n)) (k-fin el) (k-fin (e n)) (proj₂ (proj₂ (sc k) n le)) (eq el) (eq (e n))

  -- adding two tolerance bounds, on rearranged terms
  plus-tol : ∀ k A B A₂ B₂ L M L₂ M₂ → A + M ≤ L + B + hp (suc k) → A₂ + M₂ ≤ L₂ + B₂ + hp (suc k) →
    (A + A₂) + (M + M₂) ≤ (L + L₂) + (B + B₂) + hp k
  plus-tol k A B A₂ B₂ L M L₂ M₂ p q = ≤-trans (≤-reflexive (solve 4
    (λ A M A₂ M₂ → (A :+ A₂) :+ (M :+ M₂) := (A :+ M) :+ (A₂ :+ M₂)) refl A M A₂ M₂))
    (≤-trans (add-tol k p q) (≤-reflexive (+-cong (solve 4 (λ L B L₂ B₂ → (L :+ B) :+ (L₂ :+ B₂) := (L :+ L₂) :+ (B :+ B₂)) refl L B L₂ B₂) refl)))

  -- swapping the two terms on each side
  swap-tol : ∀ a b c d h → a + b ≤ c + d + h → b + a ≤ d + c + h
  swap-tol a b c d h le = ≤-trans (≤-reflexive (+-comm b a))
    (≤-trans le (≤-reflexive (solve 3 (λ c d h → c :+ d :+ h := d :+ c :+ h) refl c d h)))

  SgConv-+ : ∀ {a b l m} → SgConv a l → SgConv b m → SgConv (λ n → a n +S b n) (l +S m)
  SgConv-+ {a} {b} {l} {m} sa sb k = proj₁ (sa (suc k)) +ℕ proj₁ (sb (suc k)) , λ n le →
    plus-tol k _ _ _ _ _ _ _ _ (proj₁ (proj₂ (sa (suc k)) n (ℕP.≤-trans (ℕP.m≤m+n _ _) le)))
      (proj₁ (proj₂ (sb (suc k)) n (ℕP.≤-trans (ℕP.m≤n+m _ _) le))) ,
    plus-tol k _ _ _ _ _ _ _ _ (proj₂ (proj₂ (sa (suc k)) n (ℕP.≤-trans (ℕP.m≤m+n _ _) le)))
      (proj₂ (proj₂ (sb (suc k)) n (ℕP.≤-trans (ℕP.m≤n+m _ _) le)))

  SgConv-neg : ∀ {a l} → SgConv a l → SgConv (λ n → -S a n) (-S l)
  SgConv-neg sc k = proj₁ (sc k) , λ n le →
    swap-tol _ _ _ _ _ (proj₂ (proj₂ (sc k) n le)) , swap-tol _ _ _ _ _ (proj₁ (proj₂ (sc k) n le))

  SgConv-scale : ∀ c {a l} → SgConv a l → SgConv (λ n → c *S a n) (c *S l)
  SgConv-scale c {a} {l} sc k = proj₁ (sc (proj₁ m +ℕ k)) , λ n le →
    scale-ineq (pos c) (neg c) (pos (a n)) (neg (a n)) (pos l) (neg l) _ _ (small-scale k (proj₁ m) (proj₂ m))
      (proj₁ (proj₂ (sc (proj₁ m +ℕ k)) n le)) (proj₂ (proj₂ (sc (proj₁ m +ℕ k)) n le)) ,
    scale-ineq (pos c) (neg c) (pos l) (neg l) (pos (a n)) (neg (a n)) _ _ (small-scale k (proj₁ m) (proj₂ m))
      (proj₂ (proj₂ (sc (proj₁ m +ℕ k)) n le)) (proj₁ (proj₂ (sc (proj₁ m +ℕ k)) n le))
    where m = Is-+ {_} {_} (pos-fin c) (neg-fin c)

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
    dct-Ex f f∞ pc dn d∞ = dct-signed {X} p (λ n → posT (f n)) (λ n → negT (f n)) (posT f∞) (negT f∞) g pc dn d∞ gB

    -- the difference-quotient expectations, by linearity
    deriv-eq : ∀ (f₀ : SgT X) (f : ℕ → SgT X) (i₀ : Int {X} p f₀) (i : ∀ n → Int {X} p (f n)) →
      (dn : ∀ n → Dom (scaleT (two^ n) (f n +T -T f₀)) g) → ∀ n →
      Ex {X} p (scaleT (two^ n) (f n +T -T f₀)) (Int-dom p _ g gB (dn n)) ≃ two^ n *S (Ex {X} p (f n) (i n) +S -S Ex {X} p f₀ i₀)
    deriv-eq f₀ f i₀ i dn n = ≃-trans (Ex-irr {X} p _ _ (Int-scale {X} p (two^ n) (Int-+ {X} p (i n) (Int-neg {X} p i₀))))
      (≃-trans (Ex-scale {X} p (two^ n) _ (Int-+ {X} p (i n) (Int-neg {X} p i₀)))
        (*S-congʳ (two^ n) (≃-trans (Ex-+ {X} p (f n) (-T f₀) (i n) (Int-neg {X} p i₀)) (+S-cong ≃-refl (Ex-neg {X} p f₀ i₀)))))

    -- derivative along ½ⁿ: f₀ at θ, f n at θ + ½ⁿ, f′ the pointwise derivative
    deriv-Ex : ∀ (f₀ f′ : SgT X) (f : ℕ → SgT X) (i₀ : Int {X} p f₀) (i : ∀ n → Int {X} p (f n)) →
      PtConv (λ n → scaleT (two^ n) (f n +T -T f₀)) f′ g →
      (∀ n → Dom (scaleT (two^ n) (f n +T -T f₀)) g) → (d′ : Dom f′ g) →
      SgConv (λ n → two^ n *S (Ex {X} p (f n) (i n) +S -S Ex {X} p f₀ i₀)) (Ex {X} p f′ (Int-dom p f′ g gB d′))
    deriv-Ex f₀ f′ f i₀ i pc dn d′ = SgConv-cong (deriv-eq f₀ f i₀ i dn) (≃-refl {Ex {X} p f′ (Int-dom p f′ g gB d′)})
      (dct-Ex (λ n → scaleT (two^ n) (f n +T -T f₀)) f′ pc dn d′)
