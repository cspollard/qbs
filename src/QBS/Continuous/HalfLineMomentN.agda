{-# OPTIONS --safe --without-K #-}

-- All polynomial moments of the exponential: integration by parts on each unit interval (part 1).
--   * `pwNegExpH i : WQ ⇒ WQ`, the test `x ↦ xⁱ e^{−x}`, and `kH j`, the test `x ↦ (j+1) xʲ e^{−x}`;
--   * `ibp-unit j n`: with `G = h = xʲ⁺¹ e^{−x}` and `k = (j+1) xʲ e^{−x}` (so that `G′ = k − h`),
--       ∫₀¹ h(n+u) du + G(n+1) = G(n) + ∫₀¹ k(n+u) du.
-- The identity is `TailFTCLipJ.ftc-J` on the interval [n, n+1]: the Lipschitz and certificate hypotheses are the
-- pointwise facts of `Analysis/PolyExpCert` at M = n+1 (Bernoulli's inequality with remainder, and the first-order
-- exponential facts `y + w y ≤ 1 ≤ y + w` derived from `1 + w ≤ eʷ ≤ 1 + w + w²`), moved to the dyadic pieces of [0,1].
module QBS.Continuous.HalfLineMomentN where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

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
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipJ using (module TailFTCLipJ)

module HalfLineMomentN (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp) renaming (half+half to hh)
  open AlgT A R using (P; Dy; dy-bound; hp≤1; exp-facts)
  open AlgP A R using (pw; pw-mono; natE≤P; *-monoʳ; module Ex)
  open Exp A using (natE)
  open NegExp (lemOf lem₁) using (negExp; negExp-anti; negExp≤1; negExp-expC-nat; Meas-negExp)
  open Lebesgue (lemOf lem₁) using (J)
  open Meas (lemOf lem₁) using (Meas; Meas-⊗; Meas-const)
  open Weights (lemOf lem₁) using (WQ)
  open FairCoin lem₁ using (fairCoin)
  open HalfLine lem₁ using (shiftPt; Meas-hshift)
  open HalfLineNegExp lem₁ using (negExp-add)
  open TailFTCLipJ lem₁ using (module LipJ)
  open QBS
  open Hom

  negExp-cong : ∀ {x y} → x ≈ y → negExp x ≈ negExp y
  negExp-cong e = negExp-anti (proj₂ e) , negExp-anti (proj₁ e)

  bd1 : ∀ {x} → x ≤ 1# → x ≤ natE 1
  bd1 h = ≤-trans h (≤-reflexive (sym (+-identityˡ 1#)))

  -- the first-order exponential facts at any width t ≤ 1
  facts : ∀ {t} → t ≤ 1# → (negExp t + t * negExp t ≤ 1#) × (1# ≤ negExp t + t)
  facts {t} t1 = exp-facts {negExp t} {t} {expC (lemOf lem₁) t} (negExp-expC-nat t 1 (bd1 t1))
    (1+≤expC (lemOf lem₁) t) (expC≤quad (lemOf lem₁) t1)

  eadd : ∀ N {a t} → a + t ≤ natE N → t ≤ 1# → negExp (a + t) ≈ negExp a * negExp t
  eadd N {a} {t} at t1 = negExp-add {a} {t} {N} {1} {N} (≤-trans ≤-+ʳ at) (bd1 t1) at

  ----------------------------------------------------------------------------
  -- the tests `xⁱ e^{−x}` and `(j+1) xʲ e^{−x}`

  pw-cong : ∀ i {x y} → x ≈ y → pw i x ≈ pw i y
  pw-cong i e = ≤-antisym (pw-mono i (≤-reflexive e)) (pw-mono i (≤-reflexive (sym e)))

  hx : ℕ → ∣A∣ → ∣A∣
  hx i x = pw i x * negExp x

  hx-cong : ∀ i {x y} → x ≈ y → hx i x ≈ hx i y
  hx-cong i e = *-cong (pw-cong i e) (negExp-cong e)

  Meas-pw : ∀ i {f : R₁ → ∣A∣} → Meas f → Meas (λ r → pw i (f r))
  Meas-pw zero m = Meas-const 1#
  Meas-pw (suc i) {f} m = Meas-⊗ {f} {λ r → pw i (f r)} m (Meas-pw i m)

  pwNegExpH : ℕ → Hom S WQ WQ
  pwNegExpH i = record
    { map = record { to = hx i ; cong = hx-cong i }
    ; map-random = λ {γ} m → Meas-⊗ {λ r → pw i (γ ⟨$⟩ r)} {λ r → negExp (γ ⟨$⟩ r)}
        (Meas-pw i {γ ⟨$⟩_} m) (Meas-negExp {γ ⟨$⟩_} m) }

  kH : ℕ → Hom S WQ WQ
  kH j = record
    { map = record { to = λ x → natE (suc j) * hx j x ; cong = λ e → *-cong refl (hx-cong j e) }
    ; map-random = λ {γ} m → Meas-⊗ {λ _ → natE (suc j)} {λ r → hx j (γ ⟨$⟩ r)} (Meas-const (natE (suc j)))
        (map-random (pwNegExpH j) {γ} m) }

  ----------------------------------------------------------------------------
  -- the identity on [n₀, n₀ + 1]

  module AtInterval (n₀ j : ℕ) where
    M : ∣A∣
    M = natE (suc n₀)

    module X = Ex negExp M (suc n₀) (natE≤P (suc n₀)) negExp≤1 negExp-anti (eadd (suc n₀))
      (λ t1 → proj₁ (facts t1)) (λ t1 → proj₂ (facts t1))

    Sx sI : ℕ
    Sx = proj₁ (X.pack j)
    sI = X.sIdx Sx

    c3 = proj₁ (proj₂ (X.pack j))
    hb = proj₁ (proj₂ (proj₂ (X.pack j)))
    kb = proj₁ (proj₂ (proj₂ (proj₂ (X.pack j))))
    hl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (X.pack j)))))
    kl = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (X.pack j))))))
    cr1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (X.pack j)))))))
    cr2 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (X.pack j))))))))
    gb = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (X.pack j))))))))

    -- the point `a + w x` of a dyadic piece, shifted to n₀
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

    kcong : ∀ {x y} → x ≈ y → natE (suc j) * hx j x ≈ natE (suc j) * hx j y
    kcong e = *-cong refl (hx-cong j e)

    -- the data of the interval, named so that `LipJ` is applied to small terms
    hF kF : ∣A∣ → ∣A∣
    hF u = X.hh (suc j) (natE n₀ + u)
    kF u = natE (suc j) * X.hh j (natE n₀ + u)

    hF-cong : ∀ {x y} → x ≈ y → hF x ≈ hF y
    hF-cong e = hx-cong (suc j) (+-cong refl e)

    kF-cong : ∀ {x y} → x ≈ y → kF x ≈ kF y
    kF-cong e = kcong (+-cong refl e)

    hbF : ∀ x → x ≤ 1# → hF x + P Sx ≤ P sI
    hbF x x1 = hb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    kbF : ∀ x → x ≤ 1# → kF x + P Sx ≤ P sI
    kbF x x1 = kb {natE n₀ + x} (+-mono (≤-refl {natE n₀}) x1)

    hU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF (a + hp n * x) ≤ hF a + hp n * P Sx
    hU dy x x1 = shU (X.hh (suc j)) (hx-cong (suc j)) (proj₁ hl) dy x x1

    hD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → hF a ≤ hF (a + hp n * x) + hp n * P Sx
    hD dy x x1 = shD (X.hh (suc j)) (hx-cong (suc j)) (proj₂ hl) dy x x1

    kU : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF (a + hp n * x) ≤ kF a + hp n * P Sx
    kU dy x x1 = shU (λ y → natE (suc j) * X.hh j y) kcong (proj₁ kl) dy x x1

    kD : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → kF a ≤ kF (a + hp n * x) + hp n * P Sx
    kD dy x x1 = shD (λ y → natE (suc j) * X.hh j y) kcong (proj₂ kl) dy x x1

    GB : ∀ {n a} → Dy n a → hF a ≤ P sI
    GB {n} {a} dy = gb {natE n₀ + a} (+-mono (≤-refl {natE n₀}) (≤-trans ≤-+ʳ (dy-bound dy)))

    C1 : ∀ {n a} → Dy n a → hF (a + hp n) + hp n * hF a ≤ (hF a + hp n * kF a) + (hp n * hp n) * P Sx
    C1 {n} {a} dy = ≤-resp (+-cong (hx-cong (suc j) (+-assoc (natE n₀) a (hp n))) refl) refl
      (cr1 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    C2 : ∀ {n a} → Dy n a → hF a + hp n * kF a ≤ (hF (a + hp n) + hp n * hF a) + (hp n * hp n) * P Sx
    C2 {n} {a} dy = ≤-resp refl (+-cong (+-cong (hx-cong (suc j) (+-assoc (natE n₀) a (hp n))) refl) refl)
      (cr2 {natE n₀ + a} {hp n} (pt1 dy) (hp≤1 n))

    module L = LipJ hF kF hF sI sI (P Sx) hF-cong kF-cong hF-cong c3 hbF kbF hU hD kU kD
      (Meas-hshift n₀ (pwNegExpH (suc j))) (Meas-hshift n₀ (kH j)) GB C1 C2

    -- ∫₀¹ h(n₀+u) du + G(n₀+1) = G(n₀) + ∫₀¹ k(n₀+u) du
    ibp-unit : J fairCoin (λ r → map (pwNegExpH (suc j)) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (pwNegExpH (suc j)))
        + hx (suc j) (natE (suc n₀))
      ≈ hx (suc j) (natE n₀) + J fairCoin (λ r → map (kH j) ⟨$⟩ shiftPt n₀ r) (Meas-hshift n₀ (kH j))
    ibp-unit = trans L.ftc-J (+-cong (hx-cong (suc j) (+-identityʳ (natE n₀))) refl)
