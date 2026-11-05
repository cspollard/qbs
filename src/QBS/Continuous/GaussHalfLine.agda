{-# OPTIONS --safe --without-K #-}

-- Gaussian moments on the half-line, without π (part 1): the tests and the unit-interval identities.
--   * `phiH : WQ ⇒ WQ`, the Gaussian `x ↦ e^{−x²/2}` (`negExp` of `½ x²`: `Meas-⊗`, `Meas-negExp`);
--     `gMomH i`, the test `x ↦ xⁱ e^{−x²/2}`, and `gKH j`, the test `x ↦ (j+1) xʲ e^{−x²/2}`;
--   * the first-order exponential facts `negExp u + u negExp u ≤ 1 ≤ negExp u + u` at every bounded u (the second by
--     `Analysis/CutSplit.split1`: for u ≥ 1 it is trivial);
--   * `ibp-unit j n`: with `G = xʲ⁺¹ e^{−x²/2}`, `h = xʲ⁺² e^{−x²/2}` and `k = (j+1) xʲ e^{−x²/2}` (so `G′ = k − h`),
--       ∫₀¹ h(n+u) du + G(n+1) = G(n) + ∫₀¹ k(n+u) du.
-- The identity is `TailFTCLipJ.ftc-J` on [n, n+1] with the pointwise facts of `Analysis/GaussCert` at M = n+1, moved
-- to the dyadic pieces of [0,1] exactly as in `HalfLineMomentN`.
module QBS.Continuous.GaussHalfLine where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; 1+≤expC; expC≤quad)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.CutSplit using (split1)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussExp using (bd; module AlgGE)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineMomentN using (module HalfLineMomentN)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipJ using (module TailFTCLipJ)

module GaussHalfLine (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R using (P; Dy; dy-bound; hp≤1; exp-facts)
  open AlgP A R using (pw; pnat; natE≤P; natE-pnat; *-monoʳ; module Ex)
  open AlgGE A R using (eb; ec-big; module Gauss)
  open Exp A using (natE)
  open Expansion A half hh using (expansion)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-expC-nat; Meas-negExp)
  open Lebesgue (lemOf lem₁) using (J)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open HalfLine lem₁ using (shiftPt; Meas-hshift)
  open HalfLineNegExp lem₁ using (negExp-add)
  open HalfLineMomentN lem₁ using (negExp-cong; pw-cong; Meas-pw; bd1)
  open TailFTCLipJ lem₁ using (module LipJ)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the exponential facts, at every bounded argument

  P≤natE : ∀ k → P k ≤ natE (pnat k)
  P≤natE k = ≤-reflexive (sym (natE-pnat k))

  E-add : ∀ m {x y} → x ≤ P (bd m) → y ≤ P (bd m) → x + y ≤ P (bd m) → negExp (x + y) ≈ negExp x * negExp y
  E-add m {x} {y} xb yb xyb = negExp-add {x} {y} {pnat (bd m)} {pnat (bd m)} {pnat (bd m)}
    (≤-trans xb (P≤natE _)) (≤-trans yb (P≤natE _)) (≤-trans xyb (P≤natE _))

  E-b : ∀ m {u} → u ≤ P (bd m) → negExp u + u * negExp u ≤ 1#
  E-b m {u} ub = eb {negExp u} {u} {expC (lemOf lem₁) u}
    (negExp-expC-nat u (pnat (bd m)) (≤-trans ub (P≤natE _))) (1+≤expC (lemOf lem₁) u)

  E-c : ∀ {u} → 1# ≤ negExp u + u
  E-c {u} with split1 (lemOf lem₁) u
  ... | inj₁ u1 = proj₂ (exp-facts {negExp u} {u} {expC (lemOf lem₁) u} (negExp-expC-nat u 1 (bd1 u1))
    (1+≤expC (lemOf lem₁) u) (expC≤quad (lemOf lem₁) u1))
  ... | inj₂ 1u = ec-big 1u

  E-cb : ∀ m {u} → u ≤ P (bd m) → 1# ≤ negExp u + u
  E-cb m _ = E-c

  ----------------------------------------------------------------------------
  -- the tests

  Φ : ∣A∣ → ∣A∣
  Φ x = negExp (half * (x * x))

  Φ-cong : ∀ {x y} → x ≈ y → Φ x ≈ Φ y
  Φ-cong e = negExp-cong (*-cong refl (*-cong e e))

  Meas-Φ : ∀ {f : R₁ → ∣A∣} → Meas f → Meas (λ r → Φ (f r))
  Meas-Φ {f} m = Meas-negExp {λ r → half * (f r * f r)}
    (Meas-⊗ {λ _ → half} {λ r → f r * f r} (Meas-const half) (Meas-⊗ {f} {f} m m))

  phiH : Hom S WQ WQ
  phiH = record
    { map = record { to = Φ ; cong = Φ-cong }
    ; map-random = λ {γ} m → Meas-Φ {γ ⟨$⟩_} m }

  gh : ℕ → ∣A∣ → ∣A∣
  gh i x = pw i x * Φ x

  gh-cong : ∀ i {x y} → x ≈ y → gh i x ≈ gh i y
  gh-cong i e = *-cong (pw-cong i e) (Φ-cong e)

  gMomH : ℕ → Hom S WQ WQ
  gMomH i = record
    { map = record { to = gh i ; cong = gh-cong i }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (γ ⟨$⟩ r)} {λ r → Φ (γ ⟨$⟩ r)}
        (Meas-pw i {γ ⟨$⟩_} m) (Meas-Φ {γ ⟨$⟩_} m) }

  kh : ℕ → ∣A∣ → ∣A∣
  kh j x = natE (suc j) * gh j x

  kh-cong : ∀ j {x y} → x ≈ y → kh j x ≈ kh j y
  kh-cong j e = *-cong refl (gh-cong j e)

  gKH : ℕ → Hom S WQ WQ
  gKH j = record
    { map = record { to = kh j ; cong = kh-cong j }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → natE (suc j)} {λ r → gh j (γ ⟨$⟩ r)} (Meas-const (natE (suc j)))
        (map-random (gMomH j) {γ} m) }

  ----------------------------------------------------------------------------
  -- the identity on [n₀, n₀ + 1]

  module AtInterval (n₀ j : ℕ) where
    M : ∣A∣
    M = natE (suc n₀)

    module X = Gauss negExp M (suc n₀) (natE≤P (suc n₀)) negExp≤1 negExp-anti (E-add (suc n₀)) (E-b (suc n₀)) (E-cb (suc n₀))

    -- the facts of the pack, restated with gh / kh (so that no later conversion has to unfold `gh`)
    LipOK′ : (∣A∣ → ∣A∣) → ∣A∣ → Set₁
    LipOK′ u c = (∀ {a t} → a + t ≤ M → t ≤ 1# → u (a + t) ≤ u a + t * c)
               × (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * c)

    sI′ : ℕ → ℕ
    sI′ S = suc (S ℕ.+ suc (S ℕ.+ S))

    Pk : ℕ → ℕ → Set₁
    Pk j S = (P S + (P S + P S) ≤ P (sI′ S))
      × (∀ {x} → x ≤ M → gh (suc (suc j)) x + P S ≤ P (sI′ S))
      × (∀ {x} → x ≤ M → kh j x + P S ≤ P (sI′ S))
      × LipOK′ (gh (suc (suc j))) (P S) × LipOK′ (kh j) (P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          gh (suc j) (a + w) + w * gh (suc (suc j)) a ≤ (gh (suc j) a + w * kh j a) + (w * w) * P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          gh (suc j) a + w * kh j a ≤ (gh (suc j) (a + w) + w * gh (suc (suc j)) a) + (w * w) * P S)
      × (∀ {x} → x ≤ M → gh (suc j) x ≤ P (sI′ S))

    pk : ∀ j → Σ ℕ (Pk j)
    pk j = X.pack j

    Sx sI : ℕ
    Sx = proj₁ (pk j)
    sI = sI′ Sx

    c3 = proj₁ (proj₂ (pk j))
    hb = proj₁ (proj₂ (proj₂ (pk j)))
    kb = proj₁ (proj₂ (proj₂ (proj₂ (pk j))))
    hl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (pk j)))))
    kl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (pk j))))))
    cr1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (pk j)))))))
    cr2 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (pk j))))))))
    gb = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (pk j))))))))

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
        (+-mono ≤-refl (*-monoʳ (P Sx) (hle x x1)))

    shD : ∀ (u : ∣A∣ → ∣A∣) → (∀ {x y} → x ≈ y → u x ≈ u y) →
      (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * P Sx) →
      ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (natE n₀ + a) ≤ u (natE n₀ + (a + hp n * x)) + hp n * P Sx
    shD u uc down {n} {a} dy x x1 =
      ≤-trans (down (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n)))
        (+-mono (≤-reflexive (uc (+-assoc (natE n₀) a (hp n * x)))) (*-monoʳ (P Sx) (hle x x1)))

    pt1 : ∀ {n a} → Dy n a → (natE n₀ + a) + hp n ≤ M
    pt1 {n} {a} dy = ≤-trans (≤-reflexive (+-assoc (natE n₀) a (hp n))) (+-mono ≤-refl (dy-bound dy))

    -- the data of the interval, named so that `LipJ` is applied to small terms
    hF kF GF : ∣A∣ → ∣A∣
    hF u = gh (suc (suc j)) (natE n₀ + u)
    kF u = kh j (natE n₀ + u)
    GF u = gh (suc j) (natE n₀ + u)

    hF-cong : ∀ {x y} → x ≈ y → hF x ≈ hF y
    hF-cong e = gh-cong (suc (suc j)) (+-cong refl e)

    kF-cong : ∀ {x y} → x ≈ y → kF x ≈ kF y
    kF-cong e = kh-cong j (+-cong refl e)

    GF-cong : ∀ {x y} → x ≈ y → GF x ≈ GF y
    GF-cong e = gh-cong (suc j) (+-cong refl e)

    hbF : ∀ x → x ≤ 1# → hF x + P Sx ≤ P sI
    hbF x x1 = hb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    kbF : ∀ x → x ≤ 1# → kF x + P Sx ≤ P sI
    kbF x x1 = kb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF (a + hp n * x) ≤ hF a + hp n * P Sx
    hU dy x x1 = shU (gh (suc (suc j))) (gh-cong (suc (suc j))) (proj₁ hl) dy x x1

    hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF a ≤ hF (a + hp n * x) + hp n * P Sx
    hD dy x x1 = shD (gh (suc (suc j))) (gh-cong (suc (suc j))) (proj₂ hl) dy x x1

    kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF (a + hp n * x) ≤ kF a + hp n * P Sx
    kU dy x x1 = shU (kh j) (kh-cong j) (proj₁ kl) dy x x1

    kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF a ≤ kF (a + hp n * x) + hp n * P Sx
    kD dy x x1 = shD (kh j) (kh-cong j) (proj₂ kl) dy x x1

    GB : ∀ {n a} → Dy n a → GF a ≤ P sI
    GB {n} {a} dy = gb {natE n₀ + a} (+-mono (≤-refl {natE n₀}) (≤-trans ≤-+ʳ (dy-bound dy)))

    C1 : ∀ {n a} → Dy n a → GF (a + hp n) + hp n * hF a ≤ (GF a + hp n * kF a) + (hp n * hp n) * P Sx
    C1 {n} {a} dy = ≤-resp (+-cong (gh-cong (suc j) (+-assoc (natE n₀) a (hp n))) refl) refl
      (cr1 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    C2 : ∀ {n a} → Dy n a → GF a + hp n * kF a ≤ (GF (a + hp n) + hp n * hF a) + (hp n * hp n) * P Sx
    C2 {n} {a} dy = ≤-resp refl (+-cong (+-cong (gh-cong (suc j) (+-assoc (natE n₀) a (hp n))) refl) refl)
      (cr2 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    Mh : Meas (λ r → hF (expansion r))
    Mh = Meas-hshift n₀ (gMomH (suc (suc j)))

    Mk : Meas (λ r → kF (expansion r))
    Mk = Meas-hshift n₀ (gKH j)

    module L = LipJ hF kF GF sI sI (P Sx) hF-cong kF-cong GF-cong c3 hbF kbF hU hD kU kD Mh Mk GB C1 C2

    -- ∫₀¹ h(n₀+u) du + G(n₀+1) = G(n₀) + ∫₀¹ k(n₀+u) du
    ibp-unit : J fairCoin (λ r → map (gMomH (suc (suc j))) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (gMomH (suc (suc j))))
        + gh (suc j) (natE (suc n₀))
      ≈ gh (suc j) (natE n₀) + J fairCoin (λ r → map (gKH j) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (gKH j))
    ibp-unit = trans L.ftc-J (+-cong (gh-cong (suc j) (+-identityʳ (natE n₀))) refl)
