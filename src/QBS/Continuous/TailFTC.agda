{-# OPTIONS --safe --without-K #-}

-- A derivative-free fundamental theorem of calculus in tail form, on the unit interval (part 2: the measure side).
--
-- Take h : [0,1] → [0,1] measurable and decreasing and G : [0,1] → ℝ₊ bounded, with the certificate on every dyadic
-- interval [a, b] = [a, a + ½ⁿ]:
--     G b + (b − a) h(b) ≤ G a ≤ G b + (b − a) h(a)         (the additive form of (b−a) h(b) ≤ G a − G b ≤ (b−a) h(a)).
-- Then `∫₀¹ h + G 1 ≈ G 0` (against the fair-coin/uniform measure, with the point u of [0,1] the binary expansion).
-- No derivative, no subtraction and no division.
--
-- The proof is by induction on the depth d over all dyadic pieces at once (`Claim d`): the piece integral of h over
-- [a, b] is `½ⁿ ∫ g` with g r = h (a + ½ⁿ e(r)), and the first-bit splitting g = (g ∘ cons false, g ∘ cons true) gives the
-- left and right halves; the algebra (`Analysis/TailFTC`) glues the halves, with error ½ⁿ ½ᵈ (h a − h b).  The
-- errors vanish archimedeanly (`squeeze`).
module QBS.Continuous.TailFTC where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import Data.Bool.Base using (true; false)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Classical using (LEM₁)

module TailFTC (lem₁ : LEM₁) where
  open Daniell lem₁ using (L-one)
  A = LowerRealsOmega (lemOf lem₁)
  R = lowerRealsArch (lemOf lem₁)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open Integration A
  open Measurable A using (Fun; Fun-const; Fun-pre)
  open Expansion A half hh
  open ExpansionCons A half hh using (expansion-cons)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Indicators A (lemOf lem₁) using (I-const)
  open AlgT A R

  -- the hypotheses: h decreasing on [0,1] with values in [0,1], G bounded by 2ᴷ at the left ends of dyadic pieces,
  -- and the certificate on every dyadic piece
  module Unit (h G : ∣A∣ → ∣A∣) (K : ℕ)
    (h-cong : ∀ {x y} → x ≈ y → h x ≈ h y) (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y)
    (h≤1 : ∀ x → x ≤ 1# → h x ≤ 1#) (h-mono : ∀ {x y} → x ≤ y → y ≤ 1# → h y ≤ h x)
    (Fh : Fun (λ r → h (expansion r)))
    (G-bnd : ∀ {n a} → Dy n a → G a ≤ P K)
    (cert-lo : ∀ {n a} → Dy n a → G (a + hp n) + hp n * h (a + hp n) ≤ G a)
    (cert-hi : ∀ {n a} → Dy n a → G a ≤ G (a + hp n) + hp n * h a) where

    -- the claim for a piece [a, b] of width ½ⁿ with the sample function g r = h (a + ½ⁿ e r) and error ½ⁿ ½ᵈ
    Pc : ∀ {g} → Fun g → ℕ → ∣A∣ → ∣A∣ → ℕ → Set₁
    Pc {g} Fg n a b d = Up (hp n * I fairCoin g Fg) (G a) (G b) (h a) (h b) (hp n * hp d)
                      × Lo (hp n * I fairCoin g Fg) (G a) (G b) (h a) (h b) (hp n * hp d)

    ----------------------------------------------------------------------------
    -- the base case: a single piece, D = ½ⁿ ∫ g is between ½ⁿ h b and ½ⁿ h a

    module Base {n a b g} (Fg : Fun g) (dy : Dy n a) (bb : b ≈ a + hp n)
      (gh : ∀ r → g r ≈ h (a + hp n * expansion r)) where
      a≤1 : a ≤ 1#
      a≤1 = ≤-trans ≤-+ʳ (dy-bound dy)

      b≤1 : b ≤ 1#
      b≤1 = ≤-trans (≤-reflexive bb) (dy-bound dy)

      lo-pt : ∀ r → a ≤ a + hp n * expansion r
      lo-pt r = ≤-+ʳ

      hi-pt : ∀ r → a + hp n * expansion r ≤ a + hp n
      hi-pt r = +-mono ≤-refl (≤-trans (*-mono (hp n) (expansion≤1 r)) (≤-reflexive (*-identityʳ (hp n))))

      g≤ha : ∀ r → g r ≤ h a
      g≤ha r = ≤-trans (≤-reflexive (gh r)) (h-mono (lo-pt r) (≤-trans (hi-pt r) (dy-bound dy)))

      hb≤g : ∀ r → h b ≤ g r
      hb≤g r = ≤-trans (≤-reflexive (h-cong bb)) (≤-trans (h-mono (hi-pt r) (dy-bound dy)) (≤-reflexive (sym (gh r))))

      Ig≤ : I fairCoin g Fg ≤ h a
      Ig≤ = ≤-trans (I-mono fairCoin Fg (Fun-const (h a) (h≤1 a a≤1)) g≤ha)
                    (≤-reflexive (I-const fairCoin L-one (h a) (h≤1 a a≤1)))

      Ig≥ : h b ≤ I fairCoin g Fg
      Ig≥ = ≤-trans (≤-reflexive (sym (I-const fairCoin L-one (h b) (h≤1 b b≤1))))
                    (I-mono fairCoin (Fun-const (h b) (h≤1 b b≤1)) Fg hb≤g)

      cl : G b + hp n * h b ≤ G a
      cl = ≤-resp (+-cong (G-cong (sym bb)) (*-cong refl (h-cong (sym bb)))) refl (cert-lo dy)

      ch : G a ≤ G b + hp n * h a
      ch = ≤-resp refl (+-cong (G-cong (sym bb)) refl) (cert-hi dy)

      base : Pc Fg n a b 0
      base = Up-cong refl (sym (*-identityʳ (hp n))) (base-up (*-mono (hp n) Ig≤) cl)
           , Lo-cong refl (sym (*-identityʳ (hp n))) (base-lo (*-mono (hp n) Ig≥) ch)

    ----------------------------------------------------------------------------
    -- the step: split off the first bit

    Claim : ℕ → Set₁
    Claim d = ∀ {n a b g} (Fg : Fun g) → Dy n a → b ≈ a + hp n → (∀ r → g r ≈ h (a + hp n * expansion r)) → Pc Fg n a b d

    FF : ∀ {g} → Fun g → Fun (λ x → g (consR false x))
    FF Fg = Fun-pre {f = consR false} Fg (measurable-cons false)

    FT : ∀ {g} → Fun g → Fun (λ x → g (consR true x))
    FT Fg = Fun-pre {f = consR true} Fg (measurable-cons true)

    gh-F : ∀ {n a} {g : R₁ → ∣A∣} → (∀ r → g r ≈ h (a + hp n * expansion r)) →
      ∀ r → g (consR false r) ≈ h (a + hp (suc n) * expansion r)
    gh-F {n} {a} gh r = trans (gh (consR false r))
      (h-cong (ptL n a (expansion r) _ (trans (expansion-cons false r) (+-identityˡ _))))

    gh-T : ∀ {n a} {g : R₁ → ∣A∣} → (∀ r → g r ≈ h (a + hp n * expansion r)) →
      ∀ r → g (consR true r) ≈ h ((a + hp (suc n)) + hp (suc n) * expansion r)
    gh-T {n} {a} gh r = trans (gh (consR true r)) (h-cong (ptR n a (expansion r) _ (expansion-cons true r)))

    module Step {d} (ih : Claim d) {n a b g} (Fg : Fun g) (dy : Dy n a) (bb : b ≈ a + hp n)
      (gh : ∀ r → g r ≈ h (a + hp n * expansion r)) where
      m : ∣A∣
      m = a + hp (suc n)

      dyM : Dy (suc n) m
      dyM = dyR dy

      m≤1 : m ≤ 1#
      m≤1 = ≤-trans ≤-+ʳ (dy-bound dyM)

      left : Pc (FF Fg) (suc n) a m d
      left = ih (FF Fg) (dyL dy) refl (gh-F gh)

      right : Pc (FT Fg) (suc n) m b d
      right = ih (FT Fg) dyM (dy-end n a b bb) (gh-T gh)

      bx : G m + (hp (suc n) * hp d) * h m ≤ P (suc K)
      bx = bndX (G-bnd dyM) (hpp≤1 (suc n) d) (h≤1 m m≤1)

      split : hp n * I fairCoin g Fg ≈ hp (suc n) * I fairCoin _ (FF Fg) + hp (suc n) * I fairCoin _ (FT Fg)
      split = Dsplit n (I fairCoin g Fg) (I fairCoin _ (FT Fg)) (I fairCoin _ (FF Fg)) (firstBit-fun Fg)

      step : Pc Fg n a b (suc d)
      step = Up-cong (sym split) (sym (eps n d)) (up-step {k = suc K} bx (proj₁ left) (proj₁ right))
           , Lo-cong (sym split) (sym (eps n d)) (lo-step {k = suc K} bx (proj₂ left) (proj₂ right))

    claim : ∀ d → Claim d
    claim zero Fg dy bb gh = Base.base Fg dy bb gh
    claim (suc d) Fg dy bb gh = Step.step (claim d) Fg dy bb gh

    ----------------------------------------------------------------------------
    -- the theorem

    root : ∀ d → Pc Fh 0 0# 1# d
    root d = claim d Fh dy0 (sym (+-identityˡ 1#)) (λ r → h-cong (sym (trans (+-identityˡ _) (*-identityˡ _))))

    -- ∫₀¹ h + G 1 = G 0
    ftc-unit : I fairCoin (λ r → h (expansion r)) Fh + G 1# ≈ G 0#
    ftc-unit = squeeze (h≤1 0# 0-least)
      (λ d → Up-cong (*-identityˡ _) (*-identityˡ _) (proj₁ (root d)))
      (λ d → Lo-cong (*-identityˡ _) (*-identityˡ _) (proj₂ (root d)))
