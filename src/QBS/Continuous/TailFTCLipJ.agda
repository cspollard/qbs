{-# OPTIONS --safe --without-K #-}

-- The Lipschitz tail-form fundamental theorem (`Continuous/TailFTCLip`) for integrands of any size, in the unbounded
-- integral `J`.  The theorem there needs h, k : [0,1] → [0,1] (`Fun`); here h, k, G, c are only bounded by 2ˢ:
--   `h x + c ≤ P s`,  `k x + c ≤ P s`,  `c + (c + c) ≤ P s`   (P s = 2ˢ),
-- and the scaled data `½ˢ h`, `½ˢ k`, `½ˢ G`, `½ˢ c` satisfy the hypotheses of `Lip` (every hypothesis is additive,
-- so it scales).  Since `J` scales (`J-scale`) and extends the bounded integral (`J-fun`), the conclusion is
--   `J h + G 1 ≈ G 0 + J k`   (all integrals over the unit interval, the point being the binary expansion),
-- after unscaling by `P s · ½ˢ = 1` (`AlgL.unscale`).
module QBS.Continuous.TailFTCLipJ where

open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.TailFTCLip using (module AlgL)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLip using (module TailFTCLip)

module TailFTCLipJ (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R
  open AlgL A R
  open Lebesgue (lemOf lem₁) using (J; J-irrel; J-fun; J-scale)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open Expansion A half hh using (expansion; expansion≤1)
  open Measurable A using (Fun)
  open Integration A using (I)
  open FairCoin lem₁ using (fairCoin)
  open TailFTCLip lem₁ using (module Lip)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- 1 = ½ˢ · 2ˢ
  hP : ∀ s → hp s * P s ≈ 1#
  hP s = trans (*-comm _ _) (P*hp s)

  -- `x ≤ 2ˢ` scales to `½ˢ x ≤ 1`
  sc≤1 : ∀ s {x} → x ≤ P s → hp s * x ≤ 1#
  sc≤1 s le = ≤-trans (*-mono (hp s) le) (≤-reflexive (hP s))

  module LipJ (h k G : ∣A∣ → ∣A∣) (s K : ℕ) (c : ∣A∣)
    (h-cong : ∀ {x y} → x ≈ y → h x ≈ h y) (k-cong : ∀ {x y} → x ≈ y → k x ≈ k y) (G-cong : ∀ {x y} → x ≈ y → G x ≈ G y)
    (c3 : c + (c + c) ≤ P s)
    (hb : ∀ x → x ≤ 1# → h x + c ≤ P s) (kb : ∀ x → x ≤ 1# → k x + c ≤ P s)
    (hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → h (a + hp n * x) ≤ h a + hp n * c)
    (hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → h a ≤ h (a + hp n * x) + hp n * c)
    (kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → k (a + hp n * x) ≤ k a + hp n * c)
    (kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → k a ≤ k (a + hp n * x) + hp n * c)
    (Mh : Meas (λ r → h (expansion r))) (Mk : Meas (λ r → k (expansion r)))
    (G-bnd : ∀ {n a} → Dy n a → G a ≤ P K)
    (cert1 : ∀ {n a} → Dy n a → G (a + hp n) + hp n * h a ≤ (G a + hp n * k a) + (hp n * hp n) * c)
    (cert2 : ∀ {n a} → Dy n a → G a + hp n * k a ≤ (G (a + hp n) + hp n * h a) + (hp n * hp n) * c) where

    -- the scaled data
    hs ks Gs : ∣A∣ → ∣A∣
    hs x = hp s * h x
    ks x = hp s * k x
    Gs x = hp s * G x

    cs : ∣A∣
    cs = hp s * c

    sh-cong : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) → ∀ {x y} → x ≈ y → hp s * u x ≈ hp s * u y
    sh-cong u uc e = *-cong refl (uc e)

    c3s : cs + (cs + cs) ≤ 1#
    c3s = ≤-trans (≤-reflexive (solve 2 (λ p t → p :* t :+ (p :* t :+ p :* t) := p :* (t :+ (t :+ t))) refl (hp s) c))
      (sc≤1 s c3)

    -- `u x + c ≤ 2ˢ` scales to `½ˢ u x + ½ˢ c ≤ 1`
    sb : ∀ (u : ∣A∣ → ∣A∣) → (∀ x → x ≤ 1# → u x + c ≤ P s) → ∀ x → x ≤ 1# → hp s * u x + cs ≤ 1#
    sb u ub x x1 = ≤-trans (≤-reflexive (sym (distribˡ (hp s) (u x) c))) (sc≤1 s (ub x x1))

    alg3 : ∀ p x w t → p * (x + w * t) ≈ p * x + w * (p * t)
    alg3 p x w t = solve 4 (λ p′ x′ w′ t′ → p′ :* (x′ :+ w′ :* t′) := p′ :* x′ :+ w′ :* (p′ :* t′)) refl p x w t

    sLU : ∀ (u : ∣A∣ → ∣A∣) {n a x} → u x ≤ u a + hp n * c → hp s * u x ≤ hp s * u a + hp n * cs
    sLU u {n} {a} le = ≤-trans (*-mono (hp s) le) (≤-reflexive (alg3 (hp s) (u a) (hp n) c))

    sG : ∀ {n a} → Dy n a → hp s * G a ≤ P K
    sG {n} {a} dy = ≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (*-mono (G a) (hp≤1 s)) (≤-trans (≤-reflexive (*-identityʳ _)) (G-bnd dy)))

    alg1 : ∀ p g w x → p * g + w * (p * x) ≈ p * (g + w * x)
    alg1 p g w x = solve 4 (λ p′ g′ w′ x′ → p′ :* g′ :+ w′ :* (p′ :* x′) := p′ :* (g′ :+ w′ :* x′)) refl p g w x

    alg2 : ∀ p g w x t → p * ((g + w * x) + (w * w) * t) ≈ (p * g + w * (p * x)) + (w * w) * (p * t)
    alg2 p g w x t = solve 5 (λ p′ g′ w′ x′ t′ → p′ :* ((g′ :+ w′ :* x′) :+ (w′ :* w′) :* t′)
      := (p′ :* g′ :+ w′ :* (p′ :* x′)) :+ (w′ :* w′) :* (p′ :* t′)) refl p g w x t

    sc1 : ∀ {n a} → Dy n a → Gs (a + hp n) + hp n * hs a ≤ (Gs a + hp n * ks a) + (hp n * hp n) * cs
    sc1 {n} {a} dy = ≤-trans (≤-reflexive (alg1 (hp s) (G (a + hp n)) (hp n) (h a)))
      (≤-trans (*-mono (hp s) (cert1 dy)) (≤-reflexive (alg2 (hp s) (G a) (hp n) (k a) c)))

    sc2 : ∀ {n a} → Dy n a → Gs a + hp n * ks a ≤ (Gs (a + hp n) + hp n * hs a) + (hp n * hp n) * cs
    sc2 {n} {a} dy = ≤-trans (≤-reflexive (alg1 (hp s) (G a) (hp n) (k a)))
      (≤-trans (*-mono (hp s) (cert2 dy)) (≤-reflexive (alg2 (hp s) (G (a + hp n)) (hp n) (h a) c)))

    -- the scaled integrands are measurable and bounded by 1
    Meas-sc : ∀ (u : ∣A∣ → ∣A∣) → Meas (λ r → u (expansion r)) → Meas (λ r → hp s * u (expansion r))
    Meas-sc u M = Meas-⊗ {λ _ → hp s} {λ r → u (expansion r)} (Meas-const (hp s)) M

    Fs : ∀ (u : ∣A∣ → ∣A∣) → (∀ x → x ≤ 1# → u x + c ≤ P s) → Meas (λ r → u (expansion r)) →
      Fun (λ r → hp s * u (expansion r))
    Fs u ub M = Meas→Fun {λ r → hp s * u (expansion r)} (λ r → ≤-trans ≤-+ʳ (sb u ub (expansion r) (expansion≤1 r))) (Meas-sc u M)

    module L = Lip hs ks Gs K cs (sh-cong h h-cong) (sh-cong k k-cong) (sh-cong G G-cong) c3s (sb h hb) (sb k kb)
      (λ dy x x1 → sLU h (hU dy x x1)) (λ dy x x1 → sLU h (hD dy x x1))
      (λ dy x x1 → sLU k (kU dy x x1)) (λ dy x x1 → sLU k (kD dy x x1))
      (Fs h hb Mh) (Fs k kb Mk) sG sc1 sc2

    -- the scaled integral is ½ˢ times the integral
    sI : ∀ (u : ∣A∣ → ∣A∣) (ub : ∀ x → x ≤ 1# → u x + c ≤ P s) (M : Meas (λ r → u (expansion r))) →
      hp s * J fairCoin (λ r → u (expansion r)) M ≈ I fairCoin (λ r → hp s * u (expansion r)) (Fs u ub M)
    sI u ub M = trans (sym (J-scale fairCoin (hp s) {λ r → u (expansion r)} M))
      (trans (J-irrel fairCoin (Meas-sc u M) (LS (Fs u ub M))) (J-fun fairCoin (Fs u ub M)))

    -- ∫₀¹ h + G 1 = G 0 + ∫₀¹ k
    ftc-J : J fairCoin (λ r → h (expansion r)) Mh + G 1# ≈ G 0# + J fairCoin (λ r → k (expansion r)) Mk
    ftc-J = unscale s (trans (distribˡ (hp s) _ _) (trans (+-cong (sI h hb Mh) refl)
      (trans L.ftc-lip (trans (+-cong refl (sym (sI k kb Mk))) (sym (distribˡ (hp s) _ _))))))
