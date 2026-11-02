{-# OPTIONS --safe --without-K #-}

-- The tail-form fundamental theorem of calculus with Lipschitz errors and integration by parts, on the unit interval
-- (part 2: the measure side; the algebra is `Analysis/TailFTCLip`).
--
-- Take h, k : [0,1] → [0,1] and G : [0,1] → ℝ₊ with, on every dyadic piece [a, b] = [a, a + w], w = ½ⁿ, and constant c:
--   * h and k are Lipschitz: `|u (a + w x) − u a| ≤ w c` for x ∈ [0,1] (stated additively, both ways);
--   * the certificate holds up to `w² c`:  `G b + w h(a) ≤ G a + w k(a) + w² c` and `G a + w k(a) ≤ G b + w h(a) + w² c`
--     (the additive form of `G b − G a = w (h a − k a) + O(w²)`, i.e. `G′ = k − h`).
-- Then `∫₀¹ h + G 1 ≈ G 0 + ∫₀¹ k`, against the fair-coin/uniform measure (the point u is the binary expansion).
-- No derivative, no subtraction, no division, and no monotonicity (so no case split at the extremum of h).
-- As in `Continuous/TailFTC` the proof is an induction on the depth over all pieces at once (split off the first bit),
-- with the error budget `w² ½ᵈ 3c` of `Analysis/TailFTCLip`; the budget vanishes archimedeanly.
module QBS.Continuous.TailFTCLip where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import Data.Bool.Base using (true; false)
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.TailFTCLip using (module AlgL)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Classical using (LEM₁)

module TailFTCLip (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open Daniell lem₁ using (L-one)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero) renaming (half+half to hh)
  open Integration A
  open Measurable A using (Fun; Fun-const; Fun-pre; sumF)
  open Expansion A half hh
  open ExpansionCons A half hh using (expansion-cons)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Indicators A (lemOf lem₁) using (I-const)
  open AlgT A R
  open AlgL A R
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  module Lip (h k G : ∣A∣ → ∣A∣) (K : ℕ) (c : ∣A∣)
    (h-cong : ∀ {x y} → x ≈ y → h x ≈ h y) (k-cong : ∀ {x y} → x ≈ y → k x ≈ k y) (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y)
    (c3 : c + (c + c) ≤ 1#)
    (hb : ∀ x → x ≤ 1# → h x + c ≤ 1#) (kb : ∀ x → x ≤ 1# → k x + c ≤ 1#)
    (hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → h (a + hp n * x) ≤ h a + hp n * c)
    (hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → h a ≤ h (a + hp n * x) + hp n * c)
    (kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → k (a + hp n * x) ≤ k a + hp n * c)
    (kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → k a ≤ k (a + hp n * x) + hp n * c)
    (Fh : Fun (λ r → h (expansion r))) (Fk : Fun (λ r → k (expansion r)))
    (G-bnd : ∀ {n a} → Dy n a → G a ≤ P K)
    (cert1 : ∀ {n a} → Dy n a → G (a + hp n) + hp n * h a ≤ (G a + hp n * k a) + (hp n * hp n) * c)
    (cert2 : ∀ {n a} → Dy n a → G a + hp n * k a ≤ (G (a + hp n) + hp n * h a) + (hp n * hp n) * c) where

    c≤1 : c ≤ 1#
    c≤1 = ≤-trans ≤-+ʳ c3

    hn≤c : ∀ n → hp n * c ≤ c
    hn≤c n = ≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (*-mono c (hp≤1 n)) (≤-reflexive (*-identityʳ c)))

    c3′ : ∣A∣
    c3′ = c + (c + c)

    ----------------------------------------------------------------------------
    -- the sampled integral of u ∈ {h, k} over a piece is between w u(a) − w² c and w u(a) + w² c

    module Samp (u : ∣A∣ → ∣A∣) (ub : ∀ x → x ≤ 1# → u x + c ≤ 1#)
      (uU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (a + hp n * x) ≤ u a + hp n * c)
      (uD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u a ≤ u (a + hp n * x) + hp n * c) where
      module S {n a g} (Fg : Fun g) (dy : Dy n a) (gu : ∀ r → g r ≈ u (a + hp n * expansion r)) where
        a≤1 : a ≤ 1#
        a≤1 = ≤-trans ≤-+ʳ (dy-bound dy)

        pt≤1 : ∀ r → a + hp n * expansion r ≤ 1#
        pt≤1 r = ≤-trans (+-mono ≤-refl (≤-trans (*-mono (hp n) (expansion≤1 r)) (≤-reflexive (*-identityʳ (hp n))))) (dy-bound dy)

        ec1 : hp n * c ≤ 1#
        ec1 = ≤-trans (hn≤c n) c≤1

        ua : u a + hp n * c ≤ 1#
        ua = ≤-trans (+-mono ≤-refl (hn≤c n)) (ub a a≤1)

        ua1 : u a ≤ 1#
        ua1 = ≤-trans ≤-+ʳ ua

        g≤ : ∀ r → g r ≤ u a + hp n * c
        g≤ r = ≤-trans (≤-reflexive (gu r)) (uU dy (expansion r) (expansion≤1 r))

        ≥g : ∀ r → u a ≤ g r + hp n * c
        ≥g r = ≤-trans (uD dy (expansion r) (expansion≤1 r)) (+-mono (≤-reflexive (sym (gu r))) ≤-refl)

        gc≤1 : ∀ r → g r + hp n * c ≤ 1#
        gc≤1 r = ≤-trans (+-mono (≤-reflexive (gu r)) (hn≤c n)) (ub (a + hp n * expansion r) (pt≤1 r))

        Fgc : Fun (λ r → g r + hp n * c)
        Fgc = sumF {h₁ = g} {h₂ = λ _ → hp n * c} Fg (Fun-const (hp n * c) ec1) (λ r → refl) gc≤1

        I≤ : I fairCoin g Fg ≤ u a + hp n * c
        I≤ = ≤-trans (I-mono fairCoin Fg (Fun-const (u a + hp n * c) ua) g≤)
                     (≤-reflexive (I-const fairCoin L-one (u a + hp n * c) ua))

        I≥ : u a ≤ I fairCoin g Fg + hp n * c
        I≥ = ≤-trans (≤-reflexive (sym (I-const fairCoin L-one (u a) ua1)))
          (≤-trans (I-mono fairCoin (Fun-const (u a) ua1) Fgc ≥g)
            (≤-reflexive (trans (I-add fairCoin Fgc Fg (Fun-const (hp n * c) ec1) (λ r → refl))
              (+-cong refl (I-const fairCoin L-one (hp n * c) ec1)))))

        D≤ : hp n * I fairCoin g Fg ≤ hp n * u a + (hp n * hp n) * c
        D≤ = ≤-trans (*-mono (hp n) I≤)
          (≤-reflexive (solve 3 (λ p x t → p :* (x :+ p :* t) := p :* x :+ (p :* p) :* t) refl (hp n) (u a) c))

        D≥ : hp n * u a ≤ hp n * I fairCoin g Fg + (hp n * hp n) * c
        D≥ = ≤-trans (*-mono (hp n) I≥)
          (≤-reflexive (solve 3 (λ p x t → p :* (x :+ p :* t) := p :* x :+ (p :* p) :* t) refl (hp n) (I fairCoin g Fg) c))

    module SH = Samp h hb hU hD
    module SK = Samp k kb kU kD

    -- the claim for a piece [a, b] with the sample functions g (of h) and f (of k) and error budget ½ⁿ·½ⁿ·½ᵈ·3c
    Pc : ∀ {g f} → Fun g → Fun f → ℕ → ∣A∣ → ∣A∣ → ℕ → Set₁
    Pc {g} {f} Fg Ff n a b d =
      UpL (hp n * I fairCoin g Fg) (hp n * I fairCoin f Ff) (G a) (G b) (err n d c3′)
      × LoL (hp n * I fairCoin g Fg) (hp n * I fairCoin f Ff) (G a) (G b) (err n d c3′)

    ----------------------------------------------------------------------------
    -- the base case

    module Base {n a b g f} (Fg : Fun g) (Ff : Fun f) (dy : Dy n a) (bb : b ≈ a + hp n)
      (gh : ∀ r → g r ≈ h (a + hp n * expansion r)) (fk : ∀ r → f r ≈ k (a + hp n * expansion r)) where
      module Sg = SH.S Fg dy gh
      module Sf = SK.S Ff dy fk

      cl : G b + hp n * h a ≤ (G a + hp n * k a) + (hp n * hp n) * c
      cl = ≤-resp (+-cong (G-cong (sym bb)) refl) refl (cert1 dy)

      ch : G a + hp n * k a ≤ (G b + hp n * h a) + (hp n * hp n) * c
      ch = ≤-resp refl (+-cong (+-cong (G-cong (sym bb)) refl) refl) (cert2 dy)

      ee : (hp n * hp n) * c + ((hp n * hp n) * c + (hp n * hp n) * c) ≈ err n 0 c3′
      ee = trans (solve 2 (λ p t → p :* t :+ (p :* t :+ p :* t) := ((p :* con 1) :* (t :+ (t :+ t)))) refl (hp n * hp n) c)
        (*-cong (*-cong refl (sym hp-zero)) refl)

      base : Pc Fg Ff n a b 0
      base = UpL-cong refl refl ee (base-upL Sg.D≤ cl Sf.D≥)
           , LoL-cong refl refl ee (base-loL Sg.D≥ ch Sf.D≤)

    ----------------------------------------------------------------------------
    -- the step: split off the first bit

    Claim : ℕ → Set₁
    Claim d = ∀ {n a b g f} (Fg : Fun g) (Ff : Fun f) → Dy n a → b ≈ a + hp n →
      (∀ r → g r ≈ h (a + hp n * expansion r)) → (∀ r → f r ≈ k (a + hp n * expansion r)) → Pc Fg Ff n a b d

    FF : ∀ {g} → Fun g → Fun (λ x → g (consR false x))
    FF Fg = Fun-pre {f = consR false} Fg (measurable-cons false)

    FT : ∀ {g} → Fun g → Fun (λ x → g (consR true x))
    FT Fg = Fun-pre {f = consR true} Fg (measurable-cons true)

    gu-F : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) → ∀ {n a} {g : R₁ → ∣A∣} →
      (∀ r → g r ≈ u (a + hp n * expansion r)) → ∀ r → g (consR false r) ≈ u (a + hp (suc n) * expansion r)
    gu-F u uc {n} {a} gu r = trans (gu (consR false r))
      (uc (ptL n a (expansion r) _ (trans (expansion-cons false r) (+-identityˡ _))))

    gu-T : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) → ∀ {n a} {g : R₁ → ∣A∣} →
      (∀ r → g r ≈ u (a + hp n * expansion r)) → ∀ r → g (consR true r) ≈ u ((a + hp (suc n)) + hp (suc n) * expansion r)
    gu-T u uc {n} {a} gu r = trans (gu (consR true r)) (uc (ptR n a (expansion r) _ (expansion-cons true r)))

    module Step {d} (ih : Claim d) {n a b g f} (Fg : Fun g) (Ff : Fun f) (dy : Dy n a) (bb : b ≈ a + hp n)
      (gh : ∀ r → g r ≈ h (a + hp n * expansion r)) (fk : ∀ r → f r ≈ k (a + hp n * expansion r)) where
      m : ∣A∣
      m = a + hp (suc n)

      dyM : Dy (suc n) m
      dyM = dyR dy

      left : Pc (FF Fg) (FF Ff) (suc n) a m d
      left = ih (FF Fg) (FF Ff) (dyL dy) refl (gu-F h h-cong gh) (gu-F k k-cong fk)

      right : Pc (FT Fg) (FT Ff) (suc n) m b d
      right = ih (FT Fg) (FT Ff) dyM (dy-end n a b bb) (gu-T h h-cong gh) (gu-T k k-cong fk)

      splitG : hp n * I fairCoin g Fg ≈ hp (suc n) * I fairCoin _ (FF Fg) + hp (suc n) * I fairCoin _ (FT Fg)
      splitG = Dsplit n (I fairCoin g Fg) (I fairCoin _ (FT Fg)) (I fairCoin _ (FF Fg)) (firstBit-fun Fg)

      splitF : hp n * I fairCoin f Ff ≈ hp (suc n) * I fairCoin _ (FF Ff) + hp (suc n) * I fairCoin _ (FT Ff)
      splitF = Dsplit n (I fairCoin f Ff) (I fairCoin _ (FT Ff)) (I fairCoin _ (FF Ff)) (firstBit-fun Ff)

      step : Pc Fg Ff n a b (suc d)
      step = UpL-cong (sym splitG) (sym splitF) (err-split n d c3′)
               (up-stepL {k = K} (G-bnd dyM) (proj₁ left) (proj₁ right))
           , LoL-cong (sym splitG) (sym splitF) (err-split n d c3′)
               (lo-stepL {k = K} (G-bnd dyM) (proj₂ left) (proj₂ right))

    claim : ∀ d → Claim d
    claim zero Fg Ff dy bb gh fk = Base.base Fg Ff dy bb gh fk
    claim (suc d) Fg Ff dy bb gh fk = Step.step (claim d) Fg Ff dy bb gh fk

    ----------------------------------------------------------------------------
    -- the theorem

    root : ∀ d → Pc Fh Fk 0 0# 1# d
    root d = claim d Fh Fk dy0 (sym (+-identityˡ 1#))
      (λ r → h-cong (sym (trans (+-identityˡ _) (*-identityˡ _)))) (λ r → k-cong (sym (trans (+-identityˡ _) (*-identityˡ _))))

    -- ∫₀¹ h + G 1 = G 0 + ∫₀¹ k
    ftc-lip : I fairCoin (λ r → h (expansion r)) Fh + G 1# ≈ G 0# + I fairCoin (λ r → k (expansion r)) Fk
    ftc-lip = ≤-antisym
      (close (λ d → err-root d c3) (λ d → UpL-cong (*-identityˡ _) (*-identityˡ _) refl (proj₁ (root d))))
      (close (λ d → err-root d c3) (λ d → LoL-cong (*-identityˡ _) (*-identityˡ _) refl (proj₂ (root d))))
