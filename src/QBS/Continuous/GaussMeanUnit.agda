{-# OPTIONS --safe --without-K #-}

-- Gaussian first moment on the half-line (part 1): the unit-interval identity for `G = e^{−x²/2}`.
--   * `kzH : Hom S WQ WQ`, the zero test written as `x ↦ 0 · e^{−x²/2}` (so that its integral is `0 · ∫ e^{−x²/2}`);
--   * `AtInterval1.ibp-unit1 n₀`: with G = φ, h = x φ and k = 0 (so `G′ = −h`),
--       ∫₀¹ h(n₀+u) du + φ(n₀+1) = φ(n₀) + ∫₀¹ 0 du.
-- This is `TailFTCLipJ.ftc-J` on [n₀, n₀+1] with the pointwise facts of `Analysis/GaussCertM1` (the `j = −1` pack, which
-- `Continuous/GaussHalfLine.AtInterval` lacks), moved to the dyadic pieces of [0,1] exactly as there.
module QBS.Continuous.GaussMeanUnit where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussCertM1 using (module AlgGM)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipJ using (module TailFTCLipJ)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)

module GaussMeanUnit (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open import QBS.Analysis.Omega using (module OmegaSemiring)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open import QBS.Analysis.Archimedean using (Arch)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R using (P; Dy; dy-bound; hp≤1)
  open AlgP A R using (natE≤P)
  open AlgGM A R using (module Gauss1)
  open Exp A using (natE)
  open Expansion A half hh using (expansion)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1)
  open Lebesgue (lemOf lem₁) using (J)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open HalfLine lem₁ using (shiftPt; Meas-hshift)
  open TailFTCLipJ lem₁ using (module LipJ)
  open GaussHalfLine lem₁ using (Φ; Φ-cong; gh; gh-cong; gMomH; E-add; E-b; E-cb)
  open QBS
  open Hom

  -- the zero test
  kz : ∣A∣ → ∣A∣
  kz x = 0# * gh 0 x

  kz-cong : ∀ {x y} → x ≈ y → kz x ≈ kz y
  kz-cong e = *-cong refl (gh-cong 0 e)

  kzH : Hom S WQ WQ
  kzH = record
    { map = record { to = kz ; cong = kz-cong }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → 0#} {λ r → gh 0 (γ ⟨$⟩ r)} (Meas-const 0#)
        (map-random (gMomH 0) {γ} m) }

  ----------------------------------------------------------------------------
  -- the identity on [n₀, n₀ + 1]

  module AtInterval1 (n₀ : ℕ) where
    M : ∣A∣
    M = natE (suc n₀)

    module X = Gauss1 negExp M (suc n₀) (natE≤P (suc n₀)) negExp≤1 negExp-anti (E-add (suc n₀)) (E-b (suc n₀)) (E-cb (suc n₀))

    LipOK′ : (∣A∣ → ∣A∣) → ∣A∣ → Set₁
    LipOK′ u c = (∀ {a t} → a + t ≤ M → t ≤ 1# → u (a + t) ≤ u a + t * c)
               × (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * c)

    sI′ : ℕ → ℕ
    sI′ S = suc (S ℕ.+ suc (S ℕ.+ S))

    Pk : ℕ → Set₁
    Pk S = (P S + (P S + P S) ≤ P (sI′ S))
      × (∀ {x} → x ≤ M → gh 1 x + P S ≤ P (sI′ S))
      × (∀ {x} → x ≤ M → kz x + P S ≤ P (sI′ S))
      × LipOK′ (gh 1) (P S) × LipOK′ kz (P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          Φ (a + w) + w * gh 1 a ≤ (Φ a + w * kz a) + (w * w) * P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          Φ a + w * kz a ≤ (Φ (a + w) + w * gh 1 a) + (w * w) * P S)
      × (∀ {x} → x ≤ M → Φ x ≤ P (sI′ S))

    pk : Σ ℕ Pk
    pk = X.pack1

    Sx sI : ℕ
    Sx = proj₁ pk
    sI = sI′ Sx

    c3 = proj₁ (proj₂ pk)
    hb = proj₁ (proj₂ (proj₂ pk))
    kb = proj₁ (proj₂ (proj₂ (proj₂ pk)))
    hl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ pk))))
    kl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk)))))
    cr1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk))))))
    cr2 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk)))))))
    gb = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk)))))))

    hle : ∀ {n} x → x ≤ 1# → hp n * x ≤ hp n
    hle {n} x x1 = ≤-trans (*-mono (hp n) x1) (≤-reflexive (*-identityʳ _))

    pt : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → (natE n₀ + a) + hp n * x ≤ M
    pt {n} {a} dy x x1 = ≤-trans (≤-reflexive (+-assoc (natE n₀) a (hp n * x)))
      (+-mono ≤-refl (≤-trans (+-mono ≤-refl (hle x x1)) (dy-bound dy)))

    shU : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) →
      (∀ {a t} → a + t ≤ M → t ≤ 1# → u (a + t) ≤ u a + t * P Sx) →
      ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (natE n₀ + (a + hp n * x)) ≤ u (natE n₀ + a) + hp n * P Sx
    shU u uc up {n} {a} dy x x1 =
      ≤-trans (≤-resp (uc (+-assoc (natE n₀) a (hp n * x))) refl (up (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n))))
        (+-mono ≤-refl (AlgP.*-monoʳ A R (P Sx) (hle x x1)))

    shD : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) →
      (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * P Sx) →
      ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (natE n₀ + a) ≤ u (natE n₀ + (a + hp n * x)) + hp n * P Sx
    shD u uc down {n} {a} dy x x1 =
      ≤-trans (down (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n)))
        (+-mono (≤-reflexive (uc (+-assoc (natE n₀) a (hp n * x)))) (AlgP.*-monoʳ A R (P Sx) (hle x x1)))

    pt1 : ∀ {n a} → Dy n a → (natE n₀ + a) + hp n ≤ M
    pt1 {n} {a} dy = ≤-trans (≤-reflexive (+-assoc (natE n₀) a (hp n))) (+-mono ≤-refl (dy-bound dy))

    -- the data of the interval
    hF kF GF : ∣A∣ → ∣A∣
    hF u = gh 1 (natE n₀ + u)
    kF u = kz (natE n₀ + u)
    GF u = Φ (natE n₀ + u)

    hF-cong : ∀ {x y} → x ≈ y → hF x ≈ hF y
    hF-cong e = gh-cong 1 (+-cong refl e)

    kF-cong : ∀ {x y} → x ≈ y → kF x ≈ kF y
    kF-cong e = kz-cong (+-cong refl e)

    GF-cong : ∀ {x y} → x ≈ y → GF x ≈ GF y
    GF-cong e = Φ-cong (+-cong refl e)

    hbF : ∀ x → x ≤ 1# → hF x + P Sx ≤ P sI
    hbF x x1 = hb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    kbF : ∀ x → x ≤ 1# → kF x + P Sx ≤ P sI
    kbF x x1 = kb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF (a + hp n * x) ≤ hF a + hp n * P Sx
    hU dy x x1 = shU (gh 1) (gh-cong 1) (proj₁ hl) dy x x1

    hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF a ≤ hF (a + hp n * x) + hp n * P Sx
    hD dy x x1 = shD (gh 1) (gh-cong 1) (proj₂ hl) dy x x1

    kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF (a + hp n * x) ≤ kF a + hp n * P Sx
    kU dy x x1 = shU kz kz-cong (proj₁ kl) dy x x1

    kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF a ≤ kF (a + hp n * x) + hp n * P Sx
    kD dy x x1 = shD kz kz-cong (proj₂ kl) dy x x1

    GB : ∀ {n a} → Dy n a → GF a ≤ P sI
    GB {n} {a} dy = gb {natE n₀ + a} (+-mono (≤-refl {natE n₀}) (≤-trans ≤-+ʳ (dy-bound dy)))

    C1 : ∀ {n a} → Dy n a → GF (a + hp n) + hp n * hF a ≤ (GF a + hp n * kF a) + (hp n * hp n) * P Sx
    C1 {n} {a} dy = ≤-resp (+-cong (Φ-cong (+-assoc (natE n₀) a (hp n))) refl) refl
      (cr1 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    C2 : ∀ {n a} → Dy n a → GF a + hp n * kF a ≤ (GF (a + hp n) + hp n * hF a) + (hp n * hp n) * P Sx
    C2 {n} {a} dy = ≤-resp refl (+-cong (+-cong (Φ-cong (+-assoc (natE n₀) a (hp n))) refl) refl)
      (cr2 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    Mh : Meas (λ r → hF (expansion r))
    Mh = Meas-hshift n₀ (gMomH 1)

    Mk : Meas (λ r → kF (expansion r))
    Mk = Meas-hshift n₀ kzH

    module L = LipJ hF kF GF sI sI (P Sx) hF-cong kF-cong GF-cong c3 hbF kbF hU hD kU kD Mh Mk GB C1 C2

    -- ∫₀¹ h(n₀+u) du + φ(n₀+1) = φ(n₀) + ∫₀¹ 0 du
    ibp-unit1 : J fairCoin (λ r → map (gMomH 1) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (gMomH 1)) + Φ (natE (suc n₀))
      ≈ Φ (natE n₀) + J fairCoin (λ r → map kzH ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ kzH)
    ibp-unit1 = trans L.ftc-J (+-cong (Φ-cong (+-identityʳ (natE n₀))) refl)
