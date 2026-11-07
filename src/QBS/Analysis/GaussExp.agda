{-# OPTIONS --safe --without-K #-}

-- The Gaussian `Φ x = E (½ x²)` from an exponential E (`Analysis/GaussCert`'s input), over an abstract Archimedean
-- ω-semiring A.  E is `e^{−x}`: `E ≤ 1`, antitone, and on arguments bounded by 2ᴮ (B = `bd m`, M ≤ 2ᵐ)
--   E (x + y) = E x · E y,     E u + u E u ≤ 1,     1 ≤ E u + u.
-- (The last two are `1 + u ≤ eᵘ` with `e^{−u} eᵘ = 1`, and `1 ≤ e^{−u} + u`, which for u > 1 is trivial.)  With
-- `Y a w = E (a w + ½ w²)` one has Φ (a + w) = Φ a · Y a w (since ½ (a + w)² = ½ a² + (a w + ½ w²)), and the first-order
-- facts at `u = a w + ½ w² = w (a + ½ w)` give `Y + a w ≤ 1 + w² 2ᶜ` (from `E u + u ≤ 1 + u²`, `Analysis/PolyExpCert.yt`)
-- and `1 ≤ (Y + a w) + w² 2ᶜ`.  These are the hypotheses of `AlgG.Gs`, whose `pack` is re-exported.
module QBS.Analysis.GaussExp where

import Level as L
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussCert using (module AlgG)

-- the bound on the arguments of E: 2ᵇ with b = 2m + 1
bd : ℕ → ℕ
bd m = suc (m ℕ.+ m)

-- the constant of the first-order bounds
cst : ℕ → ℕ
cst m = bd m ℕ.+ bd m

module AlgGE (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; half+half; half-twice)
  open AlgT A R using (P; P≥1)
  open HalfOrder A R using (half≤1)
  open AlgP A R using (*-monoʳ; *-mono₂; P-mono; P-+; P-*; yt)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  half≤ : ∀ z → half * z ≤ z
  half≤ z = ≤-trans (*-monoʳ z half≤1) (≤-reflexive (*-identityˡ z))

  -- `y e = 1` and `1 + u ≤ e` give `y + u y ≤ 1`; and `1 ≤ u` gives `1 ≤ y + u`
  eb : ∀ {y u e} → y * e ≈ 1# → 1# + u ≤ e → y + u * y ≤ 1#
  eb {y} {u} {e} ye lo = ≤-trans (≤-reflexive (solve 2 (λ y′ w′ → y′ :+ w′ :* y′ := y′ :* (con 1 :+ w′)) refl y u))
    (≤-trans (*-mono y lo) (≤-reflexive ye))

  ec-big : ∀ {y u} → 1# ≤ u → 1# ≤ y + u
  ec-big {y} {u} h = ≤-trans h (≤-trans ≤-+ʳ (≤-reflexive (+-comm u y)))

  module Gauss (E : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ {x y} → x ≤ P (bd m) → y ≤ P (bd m) → x + y ≤ P (bd m) → E (x + y) ≈ E x * E y)
    (E-b : ∀ {u} → u ≤ P (bd m) → E u + u * E u ≤ 1#)
    (E-c : ∀ {u} → u ≤ P (bd m) → 1# ≤ E u + u) where

    Φ : ∣A∣ → ∣A∣
    Φ x = E (half * (x * x))

    Y : ∣A∣ → ∣A∣ → ∣A∣
    Y a w = E (a * w + half * (w * w))

    E-cong : ∀ {x y} → x ≈ y → E x ≈ E y
    E-cong e = ≤-antisym (E-anti (≤-reflexive (sym e))) (E-anti (≤-reflexive e))

    Φ≤1 : ∀ x → Φ x ≤ 1#
    Φ≤1 x = E≤1 _

    Φ-anti : ∀ {x y} → x ≤ y → Φ y ≤ Φ x
    Φ-anti xy = E-anti (*-mono half (*-mono₂ xy xy))

    Y≤1 : ∀ a w → Y a w ≤ 1#
    Y≤1 a w = E≤1 _

    -- the sizes: a, a + w ≤ M ≤ 2ᵐ, w ≤ 1 ≤ 2ᵐ
    sq : ∀ {a} → a ≤ M → a * a ≤ P (m ℕ.+ m)
    sq aM = P-* (≤-trans aM Mm) (≤-trans aM Mm)

    w≤P : ∀ {w} → w ≤ 1# → w ≤ P m
    w≤P w1 = ≤-trans w1 (P≥1 m)

    PB : ∀ {x} → x ≤ P (m ℕ.+ m) → x ≤ P (bd m)
    PB le = ≤-trans le (P-mono (ℕ.n≤1+n (m ℕ.+ m)))

    sq-eq : ∀ a w → half * ((a + w) * (a + w)) ≈ half * (a * a) + (a * w + half * (w * w))
    sq-eq a w = trans (solve 3 (λ h a′ w′ → h :* ((a′ :+ w′) :* (a′ :+ w′))
        := h :* (a′ :* a′) :+ (h :* ((a′ :* w′) :+ (a′ :* w′)) :+ h :* (w′ :* w′))) refl half a w)
      (+-cong refl (+-cong (half-twice (a * w)) refl))

    -- u = a w + ½ w² = w v with v = a + ½ w ≤ 2^(bd m)
    vB : ∀ {a w} → a ≤ M → w ≤ 1# → a + half * w ≤ P (bd m)
    vB {a} {w} aM w1 = P-+ {i = m} {j = m} (≤-trans aM Mm) (≤-trans (half≤ w) (w≤P w1))

    u-eq : ∀ a w → a * w + half * (w * w) ≈ w * (a + half * w)
    u-eq a w = solve 3 (λ a′ w′ h → a′ :* w′ :+ h :* (w′ :* w′) := w′ :* (a′ :+ h :* w′)) refl a w half

    uB : ∀ {a w} → a ≤ M → w ≤ 1# → a * w + half * (w * w) ≤ P (bd m)
    uB {a} {w} aM w1 = ≤-trans (≤-reflexive (u-eq a w)) (≤-trans (≤-trans (*-monoʳ _ w1) (≤-reflexive (*-identityˡ _)))
      (vB aM w1))

    Y-mul : ∀ {a w} → a + w ≤ M → w ≤ 1# → Φ (a + w) ≈ Φ a * Y a w
    Y-mul {a} {w} aw w1 = trans (E-cong (sq-eq a w)) (E-add xb yb (PB (≤-trans (≤-reflexive (sym (sq-eq a w)))
      (≤-trans (half≤ _) (sq aw)))))
      where
      aM : a ≤ M
      aM = ≤-trans ≤-+ʳ aw
      xb : half * (a * a) ≤ P (bd m)
      xb = PB (≤-trans (half≤ _) (sq aM))
      yb : a * w + half * (w * w) ≤ P (bd m)
      yb = uB aM w1

    Y-up : ∀ {a w} → a + w ≤ M → w ≤ 1# → Y a w + a * w ≤ 1# + (w * w) * P (cst m)
    Y-up {a} {w} aw w1 = ≤-trans (+-mono ≤-refl (≤-trans ≤-+ʳ (≤-refl {a * w + half * (w * w)})))
      (≤-trans (yt {Y a w} {u} (E-b ub) (E-c ub))
        (+-mono ≤-refl (≤-trans (≤-reflexive (trans (*-cong (u-eq a w) (u-eq a w))
          (solve 3 (λ w′ a′ h → (w′ :* (a′ :+ h :* w′)) :* (w′ :* (a′ :+ h :* w′)) := (w′ :* w′) :* ((a′ :+ h :* w′) :* (a′ :+ h :* w′)))
            refl w a half)))
          (*-mono (w * w) (P-* {i = bd m} {j = bd m} vb vb)))))
      where
      u = a * w + half * (w * w)
      aM = ≤-trans ≤-+ʳ aw
      ub = uB aM w1
      vb = vB aM w1

    Y-lo : ∀ {a w} → a + w ≤ M → w ≤ 1# → 1# ≤ (Y a w + a * w) + (w * w) * P (cst m)
    Y-lo {a} {w} aw w1 = ≤-trans (E-c ub) (≤-trans (≤-reflexive split) (+-mono ≤-refl small))
      where
      ub = uB (≤-trans ≤-+ʳ aw) w1
      split : Y a w + (a * w + half * (w * w)) ≈ (Y a w + a * w) + half * (w * w)
      split = solve 3 (λ y a′ h → y :+ (a′ :+ h) := (y :+ a′) :+ h) refl (Y a w) (a * w) (half * (w * w))
      small : half * (w * w) ≤ (w * w) * P (cst m)
      small = ≤-trans (half≤ (w * w)) (≤-trans (≤-reflexive (sym (*-identityʳ (w * w)))) (*-mono (w * w) (P≥1 (cst m))))

    open AlgG A R using (module Gs)

    open Gs Φ M m Mm Φ≤1 Φ-anti Y (cst m) Y≤1 Y-mul Y-up Y-lo public
