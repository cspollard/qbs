{-# OPTIONS --safe --without-K #-}

-- Validation of `Continuous/TailFTCHalfLine`: `∫₀^∞ e^{−x} dλ = 1` from the certificate for h = G = e^{−·} on each [n, n+1]
-- (the same pointwise exp algebra as `TailFTCExp`, at the shifted points) and the tail `e^{−N} ≤ ½ᴺ`
-- (from `e^{−1} + e^{−1} ≤ 1` and `e^{−(n+1)} = e^{−n} e^{−1}`).
module QBS.Continuous.TailFTCExpHalf where

open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCHalfLine using (module TailFTCHalfLine)

module TailFTCExpHalf (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; half-twice)
  open AlgT A R
  open Exp A using (natE; bd1)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-expC-nat; negExp-zero; negExp-cong)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExp-add; negExpH)
  open TailFTCHalfLine lem₁ using (module Leb)
  open import QBS.Continuous.SFinite using (module SFinite)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open import QBS.Continuous.Weights using (module Weights)
  open Weights (lemOf lem₁) using (WQ)

  facts : ∀ n → (negExp (hp n) + hp n * negExp (hp n) ≤ 1#) × (1# ≤ negExp (hp n) + hp n)
  facts n = exp-facts {negExp (hp n)} {hp n} {expC (lemOf lem₁) (hp n)} (negExp-expC-nat (hp n) 1 (bd1 (hp≤1 n)))
    (1+≤expC (lemOf lem₁) (hp n)) (expC≤quad (lemOf lem₁) (hp≤1 n))

  -- e^{−(n + (a + w))} = e^{−(n+a)} e^{−w} on the dyadic piece [a, a + w] of [0,1], shifted to n
  add-at : ∀ n {k a} → Dy k a → negExp (natE n + (a + hp k)) ≈ negExp (natE n + a) * negExp (hp k)
  add-at n {k} {a} d = trans (negExp-cong (sym (+-assoc (natE n) a (hp k))))
    (negExp-add {natE n + a} {hp k} {suc n} {1} {suc n} (+-mono ≤-refl a≤1) (bd1 (hp≤1 k))
      (≤-trans (≤-reflexive (+-assoc (natE n) a (hp k))) (+-mono ≤-refl (dy-bound d))))
    where a≤1 = ≤-trans ≤-+ʳ (dy-bound d)

  cert-lo : ∀ n {k a} → Dy k a →
    negExp (natE n + (a + hp k)) + hp k * negExp (natE n + (a + hp k)) ≤ negExp (natE n + a)
  cert-lo n {k} {a} d = ≤-resp (+-cong (sym e) (*-cong refl (sym e))) refl
    (proj₁ (exp-cert {negExp (natE n + a)} {negExp (hp k)} {hp k} (proj₁ (facts k)) (proj₂ (facts k))))
    where e = add-at n d

  cert-hi : ∀ n {k a} → Dy k a →
    negExp (natE n + a) ≤ negExp (natE n + (a + hp k)) + hp k * negExp (natE n + a)
  cert-hi n {k} {a} d = ≤-resp refl (+-cong (sym e) refl)
    (proj₂ (exp-cert {negExp (natE n + a)} {negExp (hp k)} {hp k} (proj₁ (facts k)) (proj₂ (facts k))))
    where e = add-at n d

  h≤1′ : ∀ x → negExp x ≤ 1#
  h≤1′ = negExp≤1

  G-bnd′ : ∀ n {k a} → Dy k a → negExp (natE n + a) ≤ P 0
  G-bnd′ n {k} {a} _ = negExp≤1 _

  -- the tail: e^{−N} ≤ ½ᴺ
  q≤half : negExp 1# ≤ half
  q≤half = ≤-trans (≤-reflexive (sym (half-twice (negExp 1#))))
    (≤-trans (≤-reflexive (*-cong refl (+-cong refl (sym (*-identityˡ _)))))
      (≤-trans (*-mono half (proj₁ (facts 0))) (≤-reflexive (*-identityʳ half))))

  tail : ∀ N → negExp (natE N) ≤ hp N
  tail zero = negExp≤1 _
  tail (suc N) = ≤-trans (≤-reflexive (negExp-add {natE N} {1#} {N} {1} {suc N} ≤-refl (bd1 ≤-refl) ≤-refl))
    (≤-trans (*-mono (negExp (natE N)) q≤half)
      (≤-trans (≤-reflexive (*-comm _ _)) (*-mono half (tail N))))

  open Leb negExpH negExp 0 negExp-cong h≤1′ (λ x≤y → negExp-anti x≤y) G-bnd′ cert-lo cert-hi using (leb-≈)

  -- ∫₀^∞ e^{−x} dλ = 1
  ∫-negExp : ∫ᴹ {WQ} lebPre negExpH ≈ 1#
  ∫-negExp = trans (leb-≈ (λ m → m , tail m)) negExp-zero
