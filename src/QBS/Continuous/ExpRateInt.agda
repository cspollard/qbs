{-# OPTIONS --safe --without-K #-}

-- `∫₀^∞ e^{−λx} dx = 1/λ` for a rate λ ≤ 1, from the tail FTC (`Continuous/TailFTCHalfLine`) with `G = c e^{−λx}`.
-- The rate `l` comes with a reciprocal `c` (`l c ≈ 1`, no division on the cuts) bounded by a natural (`c ≤ natE (suc ν)`);
-- positive rationals ≤ 1 are covered by `Continuous/ExpRateMoment.Rat`.  With `y = e^{−λ w}` and `u = λ w ≤ 1` the
-- certificate on a dyadic piece is the exp algebra `y + u y ≤ 1 ≤ y + u` (as in `TailFTCExpHalf`) multiplied by `c`
-- (`AlgRate.cert0`, using `c λ = 1`); the tail is `c e^{−λ ν N′} ≤ ½ᵐ` for a far-out N′ (`AlgRate.Tl`, from the rate-1
-- tail of `HalfLineMomentFact`).  Result: `∫ᴹ lebPre (negExpRH l) ≈ c`, hence `λ ∫ e^{−λx} ≈ 1`.
module QBS.Continuous.ExpRateInt where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
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
  open AlgP A R using (natE≤P; *-monoʳ)
  open AlgRate A R using (cert0; module Tl)
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

  module Int (l c : ∣A∣) (ν : ℕ) (lc : l * c ≈ 1#) (l1 : l ≤ 1#) (cν : c ≤ natE (suc ν)) where
    cγ : c ≤ P (suc ν)
    cγ = ≤-trans cν (natE≤P (suc ν))

    lxle : ∀ {x y} → x ≤ y → l * x ≤ y
    lxle {x} xy = ≤-trans (≤-trans (*-monoʳ x l1) (≤-reflexive (*-identityˡ x))) xy

    -- the test and the antiderivative
    G : ∣A∣ → ∣A∣
    G x = c * negExp (l * x)

    G-cong : ∀ {x y} → x ≈ y → G x ≈ G y
    G-cong e = *-cong refl (negExp-cong (*-cong refl e))

    h≤1 : ∀ x → map (negExpRH l) ⟨$⟩ x ≤ 1#
    h≤1 x = negExp≤1 (l * x)

    h-anti : ∀ {x y} → x ≤ y → map (negExpRH l) ⟨$⟩ y ≤ map (negExpRH l) ⟨$⟩ x
    h-anti xy = negExp-anti (*-mono l xy)

    G-bnd : ∀ n {k a} → Dy k a → G (natE n + a) ≤ P (suc ν)
    G-bnd n _ = ≤-trans (≤-trans (*-mono c (negExp≤1 _)) (≤-reflexive (*-identityʳ c))) cγ

    -- e^{−λ(n + (a + w))} = e^{−λ(n+a)} e^{−λ w} on the piece [a, a + w]
    add-at : ∀ n {k a} → Dy k a → negExp (l * (natE n + (a + hp k))) ≈ negExp (l * (natE n + a)) * negExp (l * hp k)
    add-at n {k} {a} d = trans (negExp-cong (trans (*-cong refl (sym (+-assoc (natE n) a (hp k)))) (distribˡ l (natE n + a) (hp k))))
      (negExp-add {l * (natE n + a)} {l * hp k} {suc n} {1} {suc n} hx hy hxy)
      where
      a≤1 : a ≤ 1#
      a≤1 = ≤-trans ≤-+ʳ (dy-bound d)
      hx : l * (natE n + a) ≤ natE (suc n)
      hx = lxle (+-mono ≤-refl a≤1)
      hy : l * hp k ≤ natE 1
      hy = bd1 (lxle (hp≤1 k))
      hxy : l * (natE n + a) + l * hp k ≤ natE (suc n)
      hxy = ≤-trans (≤-reflexive (sym (distribˡ l (natE n + a) (hp k))))
        (lxle (≤-trans (≤-reflexive (+-assoc (natE n) a (hp k))) (+-mono ≤-refl (dy-bound d))))

    -- the first-order exp facts at u = λ w
    fc : ∀ k → (negExp (l * hp k) + (l * hp k) * negExp (l * hp k) ≤ 1#) × (1# ≤ negExp (l * hp k) + l * hp k)
    fc k = facts (lxle (hp≤1 k))

    cert-lo : ∀ n {k a} → Dy k a →
      G (natE n + (a + hp k)) + hp k * (map (negExpRH l) ⟨$⟩ (natE n + (a + hp k))) ≤ G (natE n + a)
    cert-lo n {k} {a} d = ≤-resp (+-cong (*-cong refl (sym e)) (*-cong refl (sym e))) refl
      (proj₁ (cert0 {l} {c} {hp k} {negExp (l * (natE n + a))} {negExp (l * hp k)} lc (proj₁ (fc k)) (proj₂ (fc k))))
      where e = add-at n d

    cert-hi : ∀ n {k a} → Dy k a →
      G (natE n + a) ≤ G (natE n + (a + hp k)) + hp k * (map (negExpRH l) ⟨$⟩ (natE n + a))
    cert-hi n {k} {a} d = ≤-resp refl (+-cong (*-cong refl (sym e)) refl)
      (proj₂ (cert0 {l} {c} {hp k} {negExp (l * (natE n + a))} {negExp (l * hp k)} lc (proj₁ (fc k)) (proj₂ (fc k))))
      where e = add-at n d

    module TL = Tl negExp negExp-anti T.tail l c c lc l1 ν (suc ν) cν cγ 0

    tl : ∀ m → Σ ℕ (λ N → G (natE N) ≤ hp m)
    tl m = proj₁ (TL.tailR m 0) , ≤-trans (≤-reflexive (*-cong refl (sym (*-identityˡ _)))) (proj₂ (proj₂ (TL.tailR m 0)))

    open Leb (negExpRH l) G (suc ν) G-cong h≤1 h-anti G-bnd cert-lo cert-hi using (leb-≈)

    -- ∫₀^∞ e^{−λx} dx = 1/λ
    ∫-negExpR : ∫ᴹ {WQ} lebPre (negExpRH l) ≈ c
    ∫-negExpR = trans (leb-≈ tl) (trans (*-cong refl (trans (negExp-cong (zeroʳ l)) negExp-zero)) (*-identityʳ c))

    -- λ ∫ e^{−λx} dx = 1
    ∫-negExpR-rate : l * ∫ᴹ {WQ} lebPre (negExpRH l) ≈ 1#
    ∫-negExpR-rate = trans (*-cong refl ∫-negExpR) lc
