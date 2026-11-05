{-# OPTIONS --safe --without-K #-}

-- The Gaussian pack at `j = −1`: pointwise algebra for `∫₀^∞ x e^{−x²/2} dx = 1` through the Lipschitz tail FTC
-- (`Analysis/TailFTCLip`), over an abstract Archimedean ω-semiring A.
--
-- With `G = Φ` (the Gaussian), `h = x Φ` and `k = 0`, one has `G′ = −h`, so `∫ h + G b = G a + 0`.  `Analysis/GaussCert` covers
-- `G = x^{j+1} Φ` for j ≥ 0 only.  Here the certificate is first order and needs no Bernstein bounds: from the facts of
-- `Analysis/GaussExp` (`Φ (a + w) = Φ a · Y`, `Y + a w ≤ 1 + w² 2ᶜ`, `1 ≤ (Y + a w) + w² 2ᶜ`) and `Φ ≤ 1`,
--   Φ(a+w) + w (a Φ a) ≤ Φ a + w² 2ᶜ     and     Φ a ≤ (Φ(a+w) + w (a Φ a)) + w² 2ᶜ.
-- `kz x = 0 · hh 0 x` is the zero integrand written as `k-scale` writes `(j+1) hh j`, so that its integral is `0 · ∫ Φ`.
-- `pack1 : Σ S (Pack1 S)` collects all the hypotheses of `Continuous/TailFTCLipJ.LipJ` at one constant (as `Pack j S`).
module QBS.Analysis.GaussCertM1 where

import Level as L
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.GaussCert using (module AlgG)
open import QBS.Analysis.GaussExp using (cst; module AlgGE)

module AlgGM (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgT A R using (P; P≥1)
  open AlgP A R using (*-monoʳ; P-mono; P-+; pw)
  open AlgG A R using (Up; both; upI; module Gs)
  open AlgGE A R using (module Gauss)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- p Y + w (a p) ≤ p + w² c   when p ≤ 1 and Y + a w ≤ 1 + w² c
  lem1a : ∀ {p Y a w c} → p ≤ 1# → Y + a * w ≤ 1# + (w * w) * c → p * Y + w * (a * p) ≤ p + (w * w) * c
  lem1a {p} {Y} {a} {w} {c} p1 yw =
    ≤-trans (≤-reflexive (solve 4 (λ p′ y′ a′ w′ → p′ :* y′ :+ w′ :* (a′ :* p′) := p′ :* (y′ :+ a′ :* w′)) refl p Y a w))
    (≤-trans (*-mono p yw)
    (≤-trans (≤-reflexive (solve 3 (λ p′ w′ c′ → p′ :* (con 1 :+ (w′ :* w′) :* c′) := p′ :+ (w′ :* w′) :* (p′ :* c′)) refl p w c))
      (+-mono (≤-refl {p}) (*-mono (w * w) (≤-trans (*-monoʳ c p1) (≤-reflexive (*-identityˡ c)))))))

  -- the same with the zero term `w q` (q = 0) added
  lem1 : ∀ {p Y a w c q} → q ≈ 0# → p ≤ 1# → Y + a * w ≤ 1# + (w * w) * c → p * Y + w * (a * p) ≤ (p + w * q) + (w * w) * c
  lem1 {p} {w = w} {q = q} q0 p1 yw = ≤-trans (lem1a p1 yw)
    (≤-reflexive (sym (+-cong (trans (+-cong refl (trans (*-cong refl q0) (zeroʳ w))) (+-identityʳ p)) refl)))

  -- p ≤ (p Y + w (a p)) + w² c + w q   when q = 0, p ≤ 1 and 1 ≤ (Y + a w) + w² c
  lem2 : ∀ {p Y a w c q} → q ≈ 0# → p ≤ 1# → 1# ≤ (Y + a * w) + (w * w) * c → p + w * q ≤ (p * Y + w * (a * p)) + (w * w) * c
  lem2 {p} {Y} {a} {w} {c} {q} q0 p1 yw =
    ≤-trans (≤-reflexive (trans (+-cong refl (trans (*-cong refl q0) (zeroʳ w))) (trans (+-identityʳ p) (sym (*-identityʳ p)))))
    (≤-trans (*-mono p yw)
    (≤-trans (≤-reflexive (solve 5 (λ p′ y′ a′ w′ c′ → p′ :* ((y′ :+ a′ :* w′) :+ (w′ :* w′) :* c′)
        := (p′ :* y′ :+ w′ :* (a′ :* p′)) :+ (w′ :* w′) :* (p′ :* c′)) refl p Y a w c))
      (+-mono (≤-refl {p * Y + w * (a * p)}) (*-mono (w * w) pc))))
    where
    pc : p * c ≤ c
    pc = ≤-trans (*-monoʳ c p1) (≤-reflexive (*-identityˡ c))

  module Gauss1 (E : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ {x y} → x ≤ P (ℕ.suc (m ℕ.+ m)) → y ≤ P (ℕ.suc (m ℕ.+ m)) → x + y ≤ P (ℕ.suc (m ℕ.+ m)) → E (x + y) ≈ E x * E y)
    (E-b : ∀ {u} → u ≤ P (ℕ.suc (m ℕ.+ m)) → E u + u * E u ≤ 1#)
    (E-c : ∀ {u} → u ≤ P (ℕ.suc (m ℕ.+ m)) → 1# ≤ E u + u) where

    open Gauss E M m Mm E≤1 E-anti E-add E-b E-c

    kz : ∣A∣ → ∣A∣
    kz x = 0# * hh 0 x

    kz0 : ∀ x → kz x ≈ 0#
    kz0 x = zeroˡ (hh 0 x)

    h1 : ∀ a → hh 1 a ≈ a * Φ a
    h1 a = *-cong (*-identityʳ a) refl

    Cr1z Cr2z : ℕ → Set₁
    Cr1z K = ∀ {a w} → a + w ≤ M → w ≤ 1# →
      Φ (a + w) + w * hh 1 a ≤ (Φ a + w * kz a) + (w * w) * P K
    Cr2z K = ∀ {a w} → a + w ≤ M → w ≤ 1# →
      Φ a + w * kz a ≤ (Φ (a + w) + w * hh 1 a) + (w * w) * P K

    cert1z : Cr1z (cst m)
    cert1z {a} {w} aw w1 = ≤-trans (≤-reflexive (+-cong (Y-mul aw w1) (*-cong refl (h1 a))))
      (lem1 {Φ a} {Y a w} {a} {w} {P (cst m)} {kz a} (kz0 a) (Φ≤1 a) (Y-up aw w1))

    cert2z : Cr2z (cst m)
    cert2z {a} {w} aw w1 = ≤-trans (lem2 {Φ a} {Y a w} {a} {w} {P (cst m)} {kz a} (kz0 a) (Φ≤1 a) (Y-lo aw w1))
      (≤-reflexive (+-cong (+-cong (sym (Y-mul aw w1)) (*-cong refl (sym (h1 a)))) refl))

    cr1-mono : ∀ {K K′} → K ℕ.≤ K′ → Cr1z K → Cr1z K′
    cr1-mono le f aw w1 = ≤-trans (f aw w1) (+-mono ≤-refl (*-mono _ (P-mono le)))

    cr2-mono : ∀ {K K′} → K ℕ.≤ K′ → Cr2z K → Cr2z K′
    cr2-mono le f aw w1 = ≤-trans (f aw w1) (+-mono ≤-refl (*-mono _ (P-mono le)))

    kz-lip : ∀ K → LipOK kz (P K)
    kz-lip K = (λ {a} {t} _ _ → ≤-trans (≤-reflexive (kz0 (a + t))) 0-least)
      , (λ {a} {t} _ _ → ≤-trans (≤-reflexive (kz0 a)) 0-least)

    Pr1 : ℕ → Set₁
    Pr1 K = LipOK (hh 1) (P K) × Cr1z K × Cr2z K × Bd (hh 1) K

    prim1 : Up Pr1
    prim1 = both (upLip 1) (both (upI cr1-mono (cst m , λ {a} {w} → cert1z {a} {w}))
      (both (upI cr2-mono (cst m , λ {a} {w} → cert2z {a} {w})) (upI bd-mono (hhB 1))))

    Pack1 : ℕ → Set₁
    Pack1 S = (P S + (P S + P S) ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → hh 1 x + P S ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → kz x + P S ≤ P (sIdx S))
      × LipOK (hh 1) (P S) × LipOK kz (P S) × Cr1z S × Cr2z S
      × (∀ {x} → x ≤ M → Φ x ≤ P (sIdx S))

    pack1-at : ∀ S → Pr1 S → Pack1 S
    pack1-at S (hl , c1 , c2 , bh) =
      pC3 S , (λ xM → ≤-trans (P-+ {i = S} {j = S} (bh xM) ≤-refl) (P-mono (pSl S)))
      , (λ {x} xM → ≤-trans (P-+ {i = S} {j = S} (≤-trans (≤-reflexive (kz0 x)) 0-least) ≤-refl) (P-mono (pSl S)))
      , hl , kz-lip S , c1 , c2 , (λ {x} _ → ≤-trans (Φ≤1 x) (P≥1 _))

    abstract
      pack1 : Σ ℕ Pack1
      pack1 = proj₁ prim1 , pack1-at (proj₁ prim1) (proj₂ prim1 ℕ.≤-refl)
