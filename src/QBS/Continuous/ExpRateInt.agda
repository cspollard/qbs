{-# OPTIONS --safe --without-K #-}

-- `∫₀^∞ e^{−λx} dx = 1/λ` for every rate λ with a reciprocal, from the tail FTC (`Continuous/TailFTCHalfLine`) with `G = c e^{−λx}`.
-- The rate `l` comes with a reciprocal `c` (`l c ≈ 1`, no division on the cuts) and bounds `l ≤ natE (suc μ)`,
-- `c ≤ natE (suc ν)`; all positive rationals are covered by `Continuous/ExpRateMoment.Rat`.  With `y = e^{−λ w}` and
-- `u = λ w ≤ 1` (that is, `w ≤ ½ᴷ` for `K = μ + 1`) the certificate on a dyadic piece is the exp algebra
-- `y + u y ≤ 1 ≤ y + u` (as in `TailFTCExpHalf`) multiplied by `c` (`AlgRate.cert0`, using `c λ = 1`); the coarser
-- pieces follow by halving (`AlgExt.Plain`); the tail is `c e^{−λ ν N′} ≤ ½ᵐ` for a far-out N′ (`AlgRate.Tl`, from the rate-1
-- tail of `HalfLineMomentFact`).  Result: `∫ᴹ lebPre (negExpRH l) ≈ c`, hence `λ ∫ e^{−λx} ≈ 1`.
module QBS.Continuous.ExpRateInt where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.ExpRate using (module AlgRate)
open import QBS.Analysis.ExpRateExt using (module AlgExt)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCHalfLine using (module TailFTCHalfLine)

module ExpRateInt (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgT A R using (P; Dy; dy-bound; hp≤1)
  open AlgP A R using (natE≤P; *-monoʳ; *-mono₂; Phz; natE-*)
  open AlgRate A R using (cert0; module Tl)
  open AlgExt A R using (module Plain)
  open Exp A using (natE)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-zero)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExp-add)
  open HalfLineMomentN lem₁ using (negExp-cong; facts; bd1)
  open HalfLineMomentFact lem₁ using (module T)
  open HalfLineRate lem₁ using (negExpRH)
  open TailFTCHalfLine lem₁ using (module Leb)
  open QBS
  open Hom

  module Int (l c : ∣A∣) (μ ν : ℕ) (lc : l * c ≈ 1#) (lμ : l ≤ natE (suc μ)) (cν : c ≤ natE (suc ν)) where
    cγ : c ≤ P (suc ν)
    cγ = ≤-trans cν (natE≤P (suc ν))

    lμ′ : l ≤ P (suc μ)
    lμ′ = ≤-trans lμ (natE≤P (suc μ))

    -- the test and the antiderivative
    h G : ∣A∣ → ∣A∣
    h x = negExp (l * x)
    G x = c * negExp (l * x)

    h-cong : ∀ {x y} → x ≈ y → h x ≈ h y
    h-cong e = negExp-cong (*-cong refl e)

    G-cong : ∀ {x y} → x ≈ y → G x ≈ G y
    G-cong e = *-cong refl (negExp-cong (*-cong refl e))

    h≤1 : ∀ x → map (negExpRH l) ⟨$⟩ x ≤ 1#
    h≤1 x = negExp≤1 (l * x)

    h-anti : ∀ {x y} → x ≤ y → map (negExpRH l) ⟨$⟩ y ≤ map (negExpRH l) ⟨$⟩ x
    h-anti xy = negExp-anti (*-mono l xy)

    G-bnd : ∀ n {k a} → Dy k a → G (natE n + a) ≤ P (suc ν)
    G-bnd n _ = ≤-trans (≤-trans (*-mono c (negExp≤1 _)) (≤-reflexive (*-identityʳ c))) cγ

    -- the rate-1 facts are used at the width `λ t ≤ 1`, which holds for `t ≤ ½ᴷ` with `K = (μ+1) + 0`
    Kr : ℕ
    Kr = suc μ ℕ.+ 0

    Kr-ok : ∀ {t} → t ≤ hp Kr → l * t ≤ 1#
    Kr-ok {t} tK = ≤-trans (*-mono₂ lμ′ tK) (≤-reflexive (Phz (suc μ) 0))

    module Pl (N : ℕ) = Plain (natE N) h G (λ {x} {y} xy → h-anti {x} {y} xy) (λ {x} {y} e → h-cong {x} {y} e) (λ {x} {y} e → G-cong {x} {y} e)

    -- e^{−λ(a + t)} = e^{−λa} e^{−λt} for `a + t ≤ N`, `λ t ≤ 1`
    add-at : ∀ N {a t} → a + t ≤ natE N → l * t ≤ 1# → h (a + t) ≈ h a * h t
    add-at N {a} {t} at lt1 = trans (negExp-cong (distribˡ l a t))
      (negExp-add {l * a} {l * t} {suc μ ℕ.* N} {1} {suc μ ℕ.* N} hx hy hxy)
      where
      hxy : l * a + l * t ≤ natE (suc μ ℕ.* N)
      hxy = ≤-trans (≤-reflexive (sym (distribˡ l a t)))
        (≤-trans (*-mono₂ lμ at) (≤-reflexive (sym (natE-* (suc μ) N))))
      hx : l * a ≤ natE (suc μ ℕ.* N)
      hx = ≤-trans ≤-+ʳ hxy
      hy : l * t ≤ natE 1
      hy = bd1 lt1

    -- the certificate on a piece of width `t ≤ ½ᴷ`: the exp algebra `y + u y ≤ 1 ≤ y + u` at `u = λ t`, times `c`
    base : ∀ N {a t} → a + t ≤ natE N → t ≤ hp Kr → Pl.Cert N a t
    base N {a} {t} at tK = lo , hi
      where
      lt1 : l * t ≤ 1#
      lt1 = Kr-ok tK
      e : h (a + t) ≈ h a * h t
      e = add-at N at lt1
      fc : (negExp (l * t) + (l * t) * negExp (l * t) ≤ 1#) × (1# ≤ negExp (l * t) + l * t)
      fc = facts lt1
      ce : (c * (negExp (l * a) * negExp (l * t)) + t * (negExp (l * a) * negExp (l * t)) ≤ c * negExp (l * a))
        × (c * negExp (l * a) ≤ c * (negExp (l * a) * negExp (l * t)) + t * negExp (l * a))
      ce = cert0 {l} {c} {t} {negExp (l * a)} {negExp (l * t)} lc (proj₁ fc) (proj₂ fc)
      lo : G (a + t) + t * h (a + t) ≤ G a
      lo = ≤-resp (+-cong (*-cong refl (sym e)) (*-cong refl (sym e))) refl (proj₁ ce)
      hi : G a ≤ G (a + t) + t * h a
      hi = ≤-resp refl (+-cong (*-cong refl (sym e)) refl) (proj₂ ce)

    -- the dyadic pieces of [n, n+1]
    bd : ∀ n {k a} → Dy k a → (natE n + a) + hp k ≤ natE (suc n)
    bd n {k} {a} d = ≤-trans (≤-reflexive (+-assoc (natE n) a (hp k))) (+-mono ≤-refl (dy-bound d))

    cert-lo : ∀ n {k a} → Dy k a →
      G (natE n + (a + hp k)) + hp k * (map (negExpRH l) ⟨$⟩ (natE n + (a + hp k))) ≤ G (natE n + a)
    cert-lo n {k} {a} d = ≤-resp (+-cong (G-cong (+-assoc (natE n) a (hp k))) (*-cong refl (h-cong (+-assoc (natE n) a (hp k))))) refl
      (proj₁ (Pl.ext (suc n) Kr (base (suc n)) {natE n + a} {hp k} (bd n d) (hp≤1 k)))

    cert-hi : ∀ n {k a} → Dy k a →
      G (natE n + a) ≤ G (natE n + (a + hp k)) + hp k * (map (negExpRH l) ⟨$⟩ (natE n + a))
    cert-hi n {k} {a} d = ≤-resp refl (+-cong (G-cong (+-assoc (natE n) a (hp k))) refl)
      (proj₂ (Pl.ext (suc n) Kr (base (suc n)) {natE n + a} {hp k} (bd n d) (hp≤1 k)))

    module TL = Tl negExp negExp-anti T.tail l c c lc (suc μ) lμ′ ν (suc ν) cν cγ 0

    tl : ∀ m → Σ ℕ (λ N → G (natE N) ≤ hp m)
    tl m = proj₁ (TL.tailR m 0) , ≤-trans (≤-reflexive (*-cong refl (sym (*-identityˡ _)))) (proj₂ (proj₂ (TL.tailR m 0)))

    open Leb (negExpRH l) G (suc ν) G-cong h≤1 h-anti G-bnd cert-lo cert-hi using (leb-≈)

    -- ∫₀^∞ e^{−λx} dx = 1/λ
    ∫-negExpR : ∫ᴹ {WQ} lebPre (negExpRH l) ≈ c
    ∫-negExpR = trans (leb-≈ tl) (trans (*-cong refl (trans (negExp-cong (zeroʳ l)) negExp-zero)) (*-identityʳ c))

    -- λ ∫ e^{−λx} dx = 1
    ∫-negExpR-rate : l * ∫ᴹ {WQ} lebPre (negExpRH l) ≈ 1#
    ∫-negExpR-rate = trans (*-cong refl ∫-negExpR) lc
