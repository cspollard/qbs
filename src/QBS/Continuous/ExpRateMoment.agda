{-# OPTIONS --safe --without-K #-}

-- All polynomial moments of the exponential with a rate λ (any rate with a reciprocal): `∫₀^∞ xⁿ e^{−λx} dx = cⁿ⁺¹ n!`, where `c` is the
-- reciprocal of the rate (`l c ≈ 1`, `l ≤ natE (suc μ)`, `c ≤ natE (suc ν)`).  So `λⁿ⁺¹ ∫ xⁿ e^{−λx} = n!`: the cases n = 0, 1, 2 are
-- `λ ∫ e^{−λx} = 1` (`Continuous/ExpRateInt`), `λ² ∫ x e^{−λx} = 1` and `λ³ ∫ x² e^{−λx} = 2`.
-- The step `∫ xʲ⁺¹ e^{−λx} = c (j+1) ∫ xʲ e^{−λx}` is `TailFTCLipHalf.glue` (integration by parts) with
--   h = cʲ⁺¹ H(λx),  k = cʲ⁺¹ (j+1) K(λx),  G = cʲ⁺² H(λx),   H = (λx)ʲ⁺¹ e^{−λx}, K = (λx)ʲ e^{−λx},
-- so that `G′ = k − h` (`cλ = 1`).  The unit-interval identities come from the rate-1 data of `Analysis/PolyExpCert` at the
-- point λx and width λw (`AlgRate.Rate`), moved to the dyadic pieces as in `HalfLineMomentN`; the tail is `AlgRate.Tl`.
-- Any positive rational (a+1)/(b+1) is `Rat`: l = (a+1) · (1/(b+1)), c = (b+1) · (1/(a+1)) with the reciprocals of `Analysis/ExpLower`.
module QBS.Continuous.ExpRateMoment where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
import Data.Nat.Properties as ℕ

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad; qinvC; inv-ok)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.ExpRate using (module AlgRate)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpRateInt using (module ExpRateInt)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipJ using (module TailFTCLipJ)
open import QBS.Continuous.TailFTCLipHalf using (module TailFTCLipHalf)

module ExpRateMoment (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgT A R using (P; Dy; dy-bound; hp≤1)
  open AlgP A R using (pw; natE≤P; *-monoʳ; *-mono₂; natE-*; P-*; pwB)
  open AlgRate A R using (module Fn; module Rate; module Tl; module Sc; fact-step; rat-lc)
  open Exp A using (natE)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-zero)
  open Lebesgue (lemOf lem₁) using (J)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift)
  open HalfLineMomentN lem₁ using (negExp-cong; pw-cong; facts; eadd)
  open HalfLineMomentFact lem₁ using (fact; module T)
  open HalfLineRate lem₁ using (negExpRH; pwRH; qH; scaleH; ∫-scaleH)
  open ExpRateInt lem₁ using (module Int)
  open TailFTCLipJ lem₁ using (module LipJ)
  open TailFTCLipHalf lem₁ using (module Glue)
  open QBS
  open Hom

  module Mom (l c : ∣A∣) (μ ν : ℕ) (lc : l * c ≈ 1#) (lμ : l ≤ natE (suc μ)) (cν : c ≤ natE (suc ν)) where
    open Sc l c lc

    cγ : c ≤ P (suc ν)
    cγ = ≤-trans cν (natE≤P (suc ν))

    lμ′ : l ≤ P (suc μ)
    lμ′ = ≤-trans lμ (natE≤P (suc μ))

    -- the constant `s = cʲ⁺¹ ≤ 2^σ`
    σ : ℕ → ℕ
    σ j = proj₁ (pwB {c} (suc ν) cγ (suc j))

    sσ : ∀ j → pw (suc j) c ≤ P (σ j)
    sσ j = proj₂ (pwB {c} (suc ν) cγ (suc j)) ≤-refl

    -- the scaled tests: h = cʲ⁺¹ H(λx), k = cʲ⁺¹ (j+1) K(λx), G = cʲ⁺² H(λx)  (`AlgRate.Fn`)
    module F (j : ℕ) = Fn negExp l c (pw (suc j) c) j

    hRH kRH : ℕ → Hom S WQ WQ
    hRH j = record
      { map = record { to = F.hR j
                     ; cong = λ e → *-cong refl (*-cong (pw-cong (suc j) (*-cong refl e)) (negExp-cong (*-cong refl e))) }
      ; map-random = λ {γ} m → map-random (scaleH (pw (suc j) c) (qH l (suc j))) {γ} m }
    kRH j = record
      { map = record { to = F.kR j
                     ; cong = λ e → *-cong refl (*-cong refl (*-cong (pw-cong j (*-cong refl e)) (negExp-cong (*-cong refl e)))) }
      ; map-random = λ {γ} m → map-random (scaleH (pw (suc j) c) (scaleH (natE (suc j)) (qH l j))) {γ} m }

    Gf : ℕ → ∣A∣ → ∣A∣
    Gf j = F.GR j

    Gf-cong : ∀ j {x y} → x ≈ y → Gf j x ≈ Gf j y
    Gf-cong j e = *-cong refl (*-cong (pw-cong (suc j) (*-cong refl e)) (negExp-cong (*-cong refl e)))

    ----------------------------------------------------------------------------
    -- the unit-interval identity on [n₀, n₀ + 1]

    module AtInterval (n₀ j : ℕ) where
      -- the points `x ≤ Mo = n₀ + 1` are sent by the rate to `λ x ≤ M = (μ+1)(n₀+1)`, the range of the rate-1 data
      Mo M : ∣A∣
      Mo = natE (suc n₀)
      M = natE (suc μ ℕ.* suc n₀)

      lM : ∀ {x} → x ≤ Mo → l * x ≤ M
      lM xM = ≤-trans (*-mono₂ lμ xM) (≤-reflexive (sym (natE-* (suc μ) (suc n₀))))

      module X = Rate negExp M (suc μ ℕ.* suc n₀) (natE≤P (suc μ ℕ.* suc n₀)) negExp≤1 negExp-anti (eadd (suc μ ℕ.* suc n₀))
        (λ t1 → proj₁ (facts t1)) (λ t1 → proj₂ (facts t1)) negExp-cong l c (pw (suc j) c) lc Mo lM (suc μ) lμ′ (σ j) (suc ν) (sσ j) cγ j

      W Z : ℕ
      W = X.W
      Z = X.Z

      -- the point `a + w x` of a dyadic piece, shifted to n₀
      hle : ∀ {n} x → x ≤ 1# → hp n * x ≤ hp n
      hle {n} x x1 = ≤-trans (*-mono (hp n) x1) (≤-reflexive (*-identityʳ _))

      pt : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → (natE n₀ + a) + hp n * x ≤ Mo
      pt {n} {a} dy x x1 = ≤-trans (≤-reflexive (+-assoc (natE n₀) a (hp n * x)))
        (+-mono ≤-refl (≤-trans (+-mono ≤-refl (hle x x1)) (dy-bound dy)))

      pt1 : ∀ {n a} → Dy n a → (natE n₀ + a) + hp n ≤ Mo
      pt1 {n} {a} dy = ≤-trans (≤-reflexive (+-assoc (natE n₀) a (hp n))) (+-mono ≤-refl (dy-bound dy))

      shU : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) →
        (∀ {a t} → a + t ≤ Mo → t ≤ 1# → u (a + t) ≤ u a + t * P W) →
        ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (natE n₀ + (a + hp n * x)) ≤ u (natE n₀ + a) + hp n * P W
      shU u uc up {n} {a} dy x x1 =
        ≤-trans (≤-resp (uc (+-assoc (natE n₀) a (hp n * x))) refl (up (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n))))
          (+-mono ≤-refl (*-monoʳ (P W) (hle x x1)))

      shD : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) →
        (∀ {a t} → a + t ≤ Mo → t ≤ 1# → u a ≤ u (a + t) + t * P W) →
        ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (natE n₀ + a) ≤ u (natE n₀ + (a + hp n * x)) + hp n * P W
      shD u uc down {n} {a} dy x x1 =
        ≤-trans (down (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n)))
          (+-mono (≤-reflexive (uc (+-assoc (natE n₀) a (hp n * x)))) (*-monoʳ (P W) (hle x x1)))

      -- the data of the interval
      hF kF GF : ∣A∣ → ∣A∣
      hF u = X.hR (natE n₀ + u)
      kF u = X.kR (natE n₀ + u)
      GF u = X.GR (natE n₀ + u)

      hF-cong : ∀ {x y} → x ≈ y → hF x ≈ hF y
      hF-cong e = X.hR-cong (+-cong refl e)

      kF-cong : ∀ {x y} → x ≈ y → kF x ≈ kF y
      kF-cong e = X.kR-cong (+-cong refl e)

      GF-cong : ∀ {x y} → x ≈ y → GF x ≈ GF y
      GF-cong e = X.GR-cong (+-cong refl e)

      hbF : ∀ x → x ≤ 1# → hF x + P W ≤ P Z
      hbF x x1 = X.hbR {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

      kbF : ∀ x → x ≤ 1# → kF x + P W ≤ P Z
      kbF x x1 = X.kbR {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

      hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF (a + hp n * x) ≤ hF a + hp n * P W
      hU dy x x1 = shU X.hR X.hR-cong X.hR-up dy x x1

      hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF a ≤ hF (a + hp n * x) + hp n * P W
      hD dy x x1 = shD X.hR X.hR-cong X.hR-dn dy x x1

      kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF (a + hp n * x) ≤ kF a + hp n * P W
      kU dy x x1 = shU X.kR X.kR-cong X.kR-up dy x x1

      kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF a ≤ kF (a + hp n * x) + hp n * P W
      kD dy x x1 = shD X.kR X.kR-cong X.kR-dn dy x x1

      GB : ∀ {n a} → Dy n a → GF a ≤ P W
      GB {n} {a} dy = X.GRb {natE n₀ + a} (+-mono (≤-refl {natE n₀}) (≤-trans ≤-+ʳ (dy-bound dy)))

      C1 : ∀ {n a} → Dy n a → GF (a + hp n) + hp n * hF a ≤ (GF a + hp n * kF a) + (hp n * hp n) * P W
      C1 {n} {a} dy = ≤-resp (+-cong (X.GR-cong (+-assoc (natE n₀) a (hp n))) refl) refl
        (X.cert1R {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

      C2 : ∀ {n a} → Dy n a → GF a + hp n * kF a ≤ (GF (a + hp n) + hp n * hF a) + (hp n * hp n) * P W
      C2 {n} {a} dy = ≤-resp refl (+-cong (+-cong (X.GR-cong (+-assoc (natE n₀) a (hp n))) refl) refl)
        (X.cert2R {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

      module L = LipJ hF kF GF Z W (P W) hF-cong kF-cong GF-cong X.c3R hbF kbF hU hD kU kD
        (Meas-hshift n₀ (hRH j)) (Meas-hshift n₀ (kRH j)) GB C1 C2

      -- ∫₀¹ h(n₀+u) du + G(n₀+1) = G(n₀) + ∫₀¹ k(n₀+u) du
      ibp-unit : J fairCoin (λ r → map (hRH j) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (hRH j)) + Gf j (natE (suc n₀))
        ≈ Gf j (natE n₀) + J fairCoin (λ r → map (kRH j) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (kRH j))
      ibp-unit = trans L.ftc-J (+-cong (Gf-cong j (+-identityʳ (natE n₀))) refl)

    ----------------------------------------------------------------------------
    -- the moments

    G0 : ∀ j → Gf j 0# ≈ 0#
    G0 j = trans (*-cong refl (trans (*-cong (trans (*-cong (zeroʳ l) refl) (zeroˡ _)) refl) (zeroˡ _))) (zeroʳ _)

    module TL (j : ℕ) = Tl negExp negExp-anti T.tail l c (pw (suc j) c * c) lc (suc μ) lμ′ ν (σ j ℕ.+ suc ν) cν
      (P-* {pw (suc j) c} {c} {σ j} {suc ν} (sσ j) cγ) (suc j)

    module I = Int l c μ ν lc lμ cν

    -- ∫ xʲ⁺¹ e^{−λx} = c (j+1) ∫ xʲ e^{−λx}
    moment-succ : ∀ j → ∫ᴹ {WQ} lebPre (pwRH l (suc j)) ≈ (c * natE (suc j)) * ∫ᴹ {WQ} lebPre (pwRH l j)
    moment-succ j = trans (∫ᴹ-cong {WQ} lebPre {pwRH l (suc j)} {hRH j} (λ x → sym (hq≈ j x (negExp (l * x)))))
      (trans (Glue.glue (hRH j) (kRH j) (Gf j) (λ n → AtInterval.ibp-unit n j) (G0 j) (λ m N₀ → TL.tailR j m N₀))
        (trans (∫ᴹ-cong {WQ} lebPre {kRH j} {scaleH (c * natE (suc j)) (pwRH l j)} (λ x → kq≈ j x (negExp (l * x))))
          (∫-scaleH (c * natE (suc j)) (pwRH l j))))

    -- ∫ e^{−λx} = c
    mom0 : ∫ᴹ {WQ} lebPre (pwRH l 0) ≈ c
    mom0 = trans (∫ᴹ-cong {WQ} lebPre {pwRH l 0} {negExpRH l} (λ x → *-identityˡ _)) I.∫-negExpR

    -- ∫ xⁿ e^{−λx} = cⁿ⁺¹ n!
    moment : ∀ n → ∫ᴹ {WQ} lebPre (pwRH l n) ≈ pw (suc n) c * fact n
    moment zero = trans mom0 (sym (trans (*-identityʳ _) (*-identityʳ c)))
    moment (suc n) = trans (moment-succ n) (trans (*-cong refl (moment n)) fact-step)

  ----------------------------------------------------------------------------
  -- the positive rationals (a+1)/(b+1)

  module Rat (a b : ℕ) where
    qi : ℕ → ∣A∣
    qi n = qinvC (lemOf lem₁) n

    -- the rate and its reciprocal
    ratL ratC : ∣A∣
    ratL = natE (suc a) * qi b
    ratC = natE (suc b) * qi a

    qi-ok : ∀ n → qi n * natE (suc n) ≈ 1#
    qi-ok n = inv-ok (lemOf lem₁) n

    one≤ : ∀ n → 1# ≤ natE (suc n)
    one≤ n = ≤-trans ≤-+ʳ (≤-reflexive (+-comm 1# (natE n)))

    ratLC : ratL * ratC ≈ 1#
    ratLC = rat-lc {natE (suc a)} {natE (suc b)} {qi a} {qi b} (qi-ok a) (qi-ok b)

    -- 1/(a+1) ≤ 1, so the reciprocal is at most b+1
    qi≤1 : qi a ≤ 1#
    qi≤1 = ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (qi a)))) (*-mono (qi a) (one≤ a))) (≤-reflexive (qi-ok a))

    -- 1/(b+1) ≤ 1, so the rate is at most a + 1
    qiB≤1 : qi b ≤ 1#
    qiB≤1 = ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (qi b)))) (*-mono (qi b) (one≤ b))) (≤-reflexive (qi-ok b))

    ratLμ : ratL ≤ natE (suc a)
    ratLμ = ≤-trans (*-mono (natE (suc a)) qiB≤1) (≤-reflexive (*-identityʳ _))

    ratCν : ratC ≤ natE (suc b)
    ratCν = ≤-trans (*-mono (natE (suc b)) qi≤1) (≤-reflexive (*-identityʳ _))
