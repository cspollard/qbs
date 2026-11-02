{-# OPTIONS --safe --without-K #-}

-- Pointwise algebra for the Gaussian moments `∫₀^∞ xʲ e^{−x²/2} dx` through the Lipschitz tail FTC
-- (`Analysis/TailFTCLip`), over an abstract Archimedean ω-semiring A.
--
-- Data: a function Φ (the Gaussian `e^{−x²/2}`) with `Φ ≤ 1`, antitone, and on [0, M] (M ≤ 2ᵐ) a factor `Y a w` with
--   Φ (a + w) = Φ a · Y a w,     Y ≤ 1,     Y a w + a w ≤ 1 + w² 2ᶜ,     1 ≤ (Y a w + a w) + w² 2ᶜ   (w ≤ 1).
-- (For the Gaussian `Y a w = e^{−(a w + ½ w²)}`, and the two bounds are the first-order facts `E u + u E u ≤ 1 ≤ E u + u`
-- at `u = a w + ½ w²`.)  Unlike `Analysis/PolyExpCert` the exponent has a first-order term `a w` with a large coefficient
-- a ≤ M, so the constants grow with M: the certificate is applied per unit interval.  This module proves, for
--   G = hh (j+1),   h = hh (j+2),   k = (j+1) hh j,    hh i x = xⁱ Φ x   (so `G′ = k − h`):
--   * `Φ-lipD`: Φ is Lipschitz (downwards) on [0, M];  `hh-lip`: `hh i` is Lipschitz on [0, M];
--   * `Cr1`/`Cr2`: the certificate up to `w² 2ᴷ` on every [a, a + w] ⊆ [0, M], from `lem-up`/`lem-lo` (the algebra);
--   * `pack`: all the hypotheses of `Continuous/TailFTCLipJ.LipJ` with a single constant, as `Pack j S`.
module QBS.Analysis.GaussCert where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)

module AlgG (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp)
  open AlgT A R using (P; P≥1)
  open AlgP A R using (*-monoʳ; *-mono₂; P-mono; P-+; P-*; natE≤P; t*t≤t; pw; dpw; pw-mono; dpw-eq; lo-bern;
    pwB; dpwB; up-bern)
  open Exp A using (natE)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the two algebraic lemmas behind the certificate
  --   Bv = (a + w)ʲ⁺¹ ≈ π + w D + O(w²),   π = aʲ⁺¹, D = (j+1) aʲ, p = Φ a, Y = Φ(a+w)/Φ a, s = a w

  lem-up1 : ∀ {Bv π D Cb p Y a w c₁} → Bv ≤ (π + w * D) + (w * w) * Cb → Y + a * w ≤ 1# + (w * w) * c₁ → Y ≤ 1# →
    Bv * (p * Y) + w * ((a * π) * p) ≤ p * (π + (w * D + (w * w) * (π * c₁ + Cb)))
  lem-up1 {Bv} {π} {D} {Cb} {p} {Y} {a} {w} {c₁} bv yw y1 =
    ≤-trans (+-mono (*-monoʳ (p * Y) bv) (≤-refl {w * ((a * π) * p)}))
    (≤-trans (≤-reflexive (solve 7 (λ π′ d cb p′ y′ a′ w′ →
        ((π′ :+ w′ :* d) :+ (w′ :* w′) :* cb) :* (p′ :* y′) :+ w′ :* ((a′ :* π′) :* p′)
        := p′ :* (π′ :* (y′ :+ a′ :* w′) :+ ((w′ :* d) :* y′ :+ ((w′ :* w′) :* cb) :* y′))) refl π D Cb p Y a w))
    (≤-trans (*-mono p (+-mono (*-mono π yw) (+-mono (*-mono (w * D) y1) (*-mono ((w * w) * Cb) y1))))
      (≤-reflexive (solve 6 (λ π′ d cb p′ w′ c₁′ →
        p′ :* (π′ :* (con 1 :+ (w′ :* w′) :* c₁′) :+ ((w′ :* d) :* con 1 :+ ((w′ :* w′) :* cb) :* con 1))
        := p′ :* (π′ :+ (w′ :* d :+ (w′ :* w′) :* (π′ :* c₁′ :+ cb)))) refl π D Cb p w c₁))))

  lem-up2 : ∀ {π D Cb p w c₁ c} → p ≤ 1# → π * c₁ + Cb ≤ c →
    p * (π + (w * D + (w * w) * (π * c₁ + Cb))) ≤ (π * p + w * (D * p)) + (w * w) * c
  lem-up2 {π} {D} {Cb} {p} {w} {c₁} {c} p1 cc =
    ≤-trans (*-mono p (+-mono ≤-refl (+-mono ≤-refl (*-mono (w * w) cc))))
    (≤-trans (≤-reflexive (solve 5 (λ π′ d c′ p′ w′ →
        p′ :* (π′ :+ (w′ :* d :+ (w′ :* w′) :* c′)) := (π′ :* p′ :+ w′ :* (d :* p′)) :+ (w′ :* w′) :* (c′ :* p′))
        refl π D c p w))
      (+-mono ≤-refl (*-mono (w * w) (≤-trans (*-mono c p1) (≤-reflexive (*-identityʳ c))))))

  lem-up : ∀ {Bv π D Cb p Y a w c₁ c} → Bv ≤ (π + w * D) + (w * w) * Cb → Y + a * w ≤ 1# + (w * w) * c₁ →
    Y ≤ 1# → p ≤ 1# → π * c₁ + Cb ≤ c →
    Bv * (p * Y) + w * ((a * π) * p) ≤ (π * p + w * (D * p)) + (w * w) * c
  lem-up bv yw y1 p1 cc = ≤-trans (lem-up1 bv yw y1) (lem-up2 p1 cc)

  lem-lo1 : ∀ {Bv π D p Y a w c₂} → 1# ≤ (Y + a * w) + (w * w) * c₂ → π + w * D ≤ Bv → w ≤ 1# →
    π * p + w * (D * p) ≤
      p * (((Bv * Y) + (w * (a * π) + (w * w) * (D * a + π * c₂))) + (w * w) * (D * c₂))
  lem-lo1 {Bv} {π} {D} {p} {Y} {a} {w} {c₂} one bv w1 =
    ≤-trans (≤-reflexive (solve 4 (λ π′ d p′ w′ → π′ :* p′ :+ w′ :* (d :* p′) := p′ :* ((π′ :+ w′ :* d) :* con 1))
      refl π D p w))
    (≤-trans (*-mono p (*-mono (π + w * D) one))
    (≤-trans (≤-reflexive (solve 7 (λ π′ d p′ y′ a′ w′ c₂′ →
        p′ :* ((π′ :+ w′ :* d) :* ((y′ :+ a′ :* w′) :+ (w′ :* w′) :* c₂′))
        := p′ :* ((((π′ :+ w′ :* d) :* y′) :+ (w′ :* (a′ :* π′) :+ (w′ :* w′) :* (d :* a′ :+ π′ :* c₂′)))
            :+ (w′ :* w′) :* (w′ :* (d :* c₂′)))) refl π D p Y a w c₂))
      (*-mono p (+-mono (+-mono (*-monoʳ Y bv) ≤-refl) (*-mono (w * w) wD)))))
    where
    wD : w * (D * c₂) ≤ D * c₂
    wD = ≤-trans (*-monoʳ (D * c₂) w1) (≤-reflexive (*-identityˡ _))

  lem-lo2 : ∀ {Bv π D p Y a w c₂ c} → p ≤ 1# → (D * a + π * c₂) + D * c₂ ≤ c →
    p * (((Bv * Y) + (w * (a * π) + (w * w) * (D * a + π * c₂))) + (w * w) * (D * c₂)) ≤
      (Bv * (p * Y) + w * ((a * π) * p)) + (w * w) * c
  lem-lo2 {Bv} {π} {D} {p} {Y} {a} {w} {c₂} {c} p1 cc =
    ≤-trans (≤-reflexive (solve 8 (λ bv′ y′ p′ a′ π′ w′ d c₂′ →
        p′ :* (((bv′ :* y′) :+ (w′ :* (a′ :* π′) :+ (w′ :* w′) :* (d :* a′ :+ π′ :* c₂′))) :+ (w′ :* w′) :* (d :* c₂′))
        := (bv′ :* (p′ :* y′) :+ w′ :* ((a′ :* π′) :* p′)) :+ (w′ :* w′) :* (p′ :* ((d :* a′ :+ π′ :* c₂′) :+ d :* c₂′)))
        refl Bv Y p a π w D c₂))
      (+-mono ≤-refl (*-mono (w * w) (≤-trans (*-mono₂ p1 cc) (≤-reflexive (*-identityˡ c)))))

  lem-lo : ∀ {Bv π D p Y a w c₂ c} → 1# ≤ (Y + a * w) + (w * w) * c₂ → π + w * D ≤ Bv → w ≤ 1# → p ≤ 1# →
    (D * a + π * c₂) + D * c₂ ≤ c →
    π * p + w * (D * p) ≤ (Bv * (p * Y) + w * ((a * π) * p)) + (w * w) * c
  lem-lo one bv w1 p1 cc = ≤-trans (lem-lo1 one bv w1) (lem-lo2 p1 cc)

  ----------------------------------------------------------------------------
  -- upward closure of constants: `Up F` is `∃K ∀K′ ≥ K. F K′`

  Up : (ℕ → Set₁) → Set₁
  Up F = Σ ℕ (λ K → ∀ {K′} → K ℕ.≤ K′ → F K′)

  both : ∀ {F F′ : ℕ → Set₁} → Up F → Up F′ → Up (λ K → F K × F′ K)
  both (K₁ , f) (K₂ , g) = (K₁ ℕ.+ K₂) , (λ le → f (ℕ.≤-trans (ℕ.m≤m+n K₁ K₂) le) , g (ℕ.≤-trans (ℕ.m≤n+m K₂ K₁) le))

  upI : ∀ {F : ℕ → Set₁} → (∀ {K K′} → K ℕ.≤ K′ → F K → F K′) → Σ ℕ F → Up F
  upI mono (K , f) = K , (λ le → mono le f)

  ----------------------------------------------------------------------------
  -- the Gaussian data

  module Gs (Φ : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (Φ≤1 : ∀ x → Φ x ≤ 1#) (Φ-anti : ∀ {x y} → x ≤ y → Φ y ≤ Φ x)
    (Y : ∣A∣ → ∣A∣ → ∣A∣) (C : ℕ) (Y≤1 : ∀ a w → Y a w ≤ 1#)
    (Y-mul : ∀ {a w} → a + w ≤ M → w ≤ 1# → Φ (a + w) ≈ Φ a * Y a w)
    (Y-up : ∀ {a w} → a + w ≤ M → w ≤ 1# → Y a w + a * w ≤ 1# + (w * w) * P C)
    (Y-lo : ∀ {a w} → a + w ≤ M → w ≤ 1# → 1# ≤ (Y a w + a * w) + (w * w) * P C) where

    hh : ℕ → ∣A∣ → ∣A∣
    hh i x = pw i x * Φ x

    kh : ℕ → ∣A∣ → ∣A∣
    kh j x = natE (suc j) * hh j x

    -- Φ a ≤ Φ (a + t) + t 2ᴸ
    Lg : ℕ
    Lg = suc (m ℕ.+ C)

    Φ-lipD : ∀ {a t} → a + t ≤ M → t ≤ 1# → Φ a ≤ Φ (a + t) + t * P Lg
    Φ-lipD {a} {t} at t1 =
      ≤-trans (≤-reflexive (sym (*-identityʳ (Φ a))))
      (≤-trans (*-mono (Φ a) (≤-trans (Y-lo at t1) (≤-refl {(Y a t + a * t) + (t * t) * P C})))
      (≤-trans (≤-reflexive (solve 5 (λ φ y a′ t′ c → φ :* ((y :+ a′ :* t′) :+ (t′ :* t′) :* c)
          := (φ :* y) :+ (t′ :* (φ :* a′) :+ (t′ :* t′) :* (φ :* c))) refl (Φ a) (Y a t) a t (P C)))
      (≤-trans (+-mono (≤-reflexive (sym (Y-mul at t1)))
          (+-mono (*-mono t φa) (≤-trans (*-monoʳ (Φ a * P C) (t*t≤t t1)) (*-mono t φc))))
        (≤-trans (+-mono ≤-refl (≤-reflexive (solve 3 (λ t′ x y → t′ :* x :+ t′ :* y := t′ :* (x :+ y)) refl t (P m) (P C))))
          (+-mono ≤-refl (*-mono t (P-+ {i = m} {j = C} ≤-refl ≤-refl)))))))
      where
      aM : a ≤ M
      aM = ≤-trans ≤-+ʳ at
      φa : Φ a * a ≤ P m
      φa = ≤-trans (*-monoʳ a (Φ≤1 a)) (≤-trans (≤-reflexive (*-identityˡ a)) (≤-trans aM Mm))
      φc : Φ a * P C ≤ P C
      φc = ≤-trans (*-monoʳ (P C) (Φ≤1 a)) (≤-reflexive (*-identityˡ _))

    LipOK : (∣A∣ → ∣A∣) → ∣A∣ → Set₁
    LipOK u c = (∀ {a t} → a + t ≤ M → t ≤ 1# → u (a + t) ≤ u a + t * c)
              × (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * c)

    pw-lip : ∀ i → Σ ℕ (λ K → ∀ {a t} → a + t ≤ M → t ≤ 1# → pw i (a + t) ≤ pw i a + t * P K)
    pw-lip i with up-bern m Mm i | dpwB m Mm i
    ... | C′ , f | D , g = suc (D ℕ.+ C′) , (λ {a} {t} at t1 →
      ≤-trans (f at)
        (≤-trans (+-mono (+-mono (≤-refl {pw i a}) (*-mono t (g (≤-trans ≤-+ʳ at)))) (*-monoʳ (P C′) (t*t≤t t1)))
          (≤-trans (≤-reflexive (solve 4 (λ q t′ d c → (q :+ t′ :* d) :+ t′ :* c := q :+ t′ :* (d :+ c)) refl (pw i a) t (P D) (P C′)))
            (+-mono (≤-refl {pw i a}) (*-mono t (P-+ (≤-refl {P D}) (≤-refl {P C′})))))))

    -- hh i is Lipschitz: up with 2^K₁ (Φ ≤ 1, antitone), down with 2^(K₂+Lg) (Φ-lipD)
    hh-lip : ∀ i → Σ ℕ (λ K → LipOK (hh i) (P K))
    hh-lip i with pw-lip i | pwB m Mm i
    ... | K₁ , f | K₂ , g = (K₁ ℕ.+ (K₂ ℕ.+ Lg)) , up , down
      where
      up : ∀ {a t} → a + t ≤ M → t ≤ 1# → hh i (a + t) ≤ hh i a + t * P (K₁ ℕ.+ (K₂ ℕ.+ Lg))
      up {a} {t} at t1 = ≤-trans (*-mono₂ (f at t1) (Φ-anti (≤-+ʳ {a} {t})))
        (≤-trans (≤-reflexive (solve 4 (λ q t′ c e → (q :+ t′ :* c) :* e := q :* e :+ t′ :* (c :* e)) refl (pw i a) t (P K₁) (Φ a)))
          (+-mono (≤-refl {pw i a * Φ a}) (*-mono t (≤-trans (*-mono (P K₁) (Φ≤1 a))
            (≤-trans (≤-reflexive (*-identityʳ _)) (P-mono (ℕ.m≤m+n K₁ (K₂ ℕ.+ Lg))))))))
      down : ∀ {a t} → a + t ≤ M → t ≤ 1# → hh i a ≤ hh i (a + t) + t * P (K₁ ℕ.+ (K₂ ℕ.+ Lg))
      down {a} {t} at t1 = ≤-trans (*-mono₂ (pw-mono i (≤-+ʳ {a} {t})) (Φ-lipD at t1))
        (≤-trans (≤-reflexive (solve 4 (λ q e t′ c → q :* (e :+ t′ :* c) := q :* e :+ t′ :* (q :* c)) refl
            (pw i (a + t)) (Φ (a + t)) t (P Lg)))
          (+-mono (≤-refl {pw i (a + t) * Φ (a + t)})
            (*-mono t (≤-trans (P-* (g at) (≤-refl {P Lg})) (P-mono (ℕ.m≤n+m (K₂ ℕ.+ Lg) K₁))))))

    lip-mono : ∀ {u K K′} → K ℕ.≤ K′ → LipOK u (P K) → LipOK u (P K′)
    lip-mono e (up , down) =
      (λ at t1 → ≤-trans (up at t1) (+-mono ≤-refl (*-mono _ (P-mono e))))
      , (λ at t1 → ≤-trans (down at t1) (+-mono ≤-refl (*-mono _ (P-mono e))))

    scale-step : ∀ {N x y t K L} → N ≤ P L → x ≤ y + t * P K → N * x ≤ N * y + t * P (L ℕ.+ K)
    scale-step {N} {x} {y} {t} {K} {L} NL h = ≤-trans (*-mono N h)
      (≤-trans (≤-reflexive (solve 4 (λ n y′ t′ c → n :* (y′ :+ t′ :* c) := n :* y′ :+ t′ :* (n :* c)) refl N y t (P K)))
        (+-mono ≤-refl (*-mono t (P-* NL (≤-refl {P K})))))

    lip-scale : ∀ {u K L N} → N ≤ P L → LipOK u (P K) → LipOK (λ x → N * u x) (P (L ℕ.+ K))
    lip-scale NL (up , down) = (λ at t1 → scale-step NL (up at t1)) , (λ at t1 → scale-step NL (down at t1))

    ----------------------------------------------------------------------------
    -- the certificate for G = hh (j+1), h = hh (j+2), k = kh j

    Cr1 Cr2 : ℕ → ℕ → Set₁
    Cr1 j K = ∀ {a w} → a + w ≤ M → w ≤ 1# →
      hh (suc j) (a + w) + w * hh (suc (suc j)) a ≤ (hh (suc j) a + w * kh j a) + (w * w) * P K
    Cr2 j K = ∀ {a w} → a + w ≤ M → w ≤ 1# →
      hh (suc j) a + w * kh j a ≤ (hh (suc j) (a + w) + w * hh (suc (suc j)) a) + (w * w) * P K

    kk : ∀ j a → kh j a ≈ dpw (suc j) a * Φ a
    kk j a = trans (sym (*-assoc _ _ _)) (*-cong (sym (dpw-eq j a)) refl)

    cC cB cD : ℕ → ℕ
    cC j = proj₁ (up-bern m Mm (suc j))
    cB j = proj₁ (pwB m Mm (suc j))
    cD j = proj₁ (dpwB m Mm (suc j))

    cub : ∀ j {a t} → a + t ≤ M → pw (suc j) (a + t) ≤ (pw (suc j) a + t * dpw (suc j) a) + (t * t) * P (cC j)
    cub j = proj₂ (up-bern m Mm (suc j))

    -- the constants
    k1 k2 : ℕ → ℕ
    k1 j = suc ((cB j ℕ.+ C) ℕ.+ cC j)
    k2 j = suc (suc ((cD j ℕ.+ m) ℕ.+ (cB j ℕ.+ C)) ℕ.+ (cD j ℕ.+ C))

    bd1 : ∀ j {a} → a ≤ M → pw (suc j) a * P C + P (cC j) ≤ P (k1 j)
    bd1 j aM = P-+ (P-* (proj₂ (pwB m Mm (suc j)) aM) (≤-refl {P C})) (≤-refl {P (cC j)})

    bd2 : ∀ j {a} → a ≤ M → (dpw (suc j) a * a + pw (suc j) a * P C) + dpw (suc j) a * P C ≤ P (k2 j)
    bd2 j aM = P-+ (P-+ (P-* (proj₂ (dpwB m Mm (suc j)) aM) (≤-trans aM Mm)) (P-* (proj₂ (pwB m Mm (suc j)) aM) (≤-refl {P C})))
      (P-* (proj₂ (dpwB m Mm (suc j)) aM) (≤-refl {P C}))

    cert1 : ∀ j → Cr1 j (k1 j)
    cert1 j {a} {w} aw w1 =
      ≤-trans (≤-reflexive (+-cong (*-cong refl (Y-mul aw w1)) refl))
      (≤-trans (lem-up {pw (suc j) (a + w)} {pw (suc j) a} {dpw (suc j) a} {P (cC j)} {Φ a} {Y a w} {a} {w} {P C} {P (k1 j)}
          (cub j aw) (Y-up aw w1) (Y≤1 a w) (Φ≤1 a) (bd1 j (≤-trans ≤-+ʳ aw)))
        (≤-reflexive (+-cong (+-cong refl (*-cong refl (sym (kk j a)))) refl)))

    cert2 : ∀ j → Cr2 j (k2 j)
    cert2 j {a} {w} aw w1 =
      ≤-trans (≤-reflexive (+-cong refl (*-cong refl (kk j a))))
      (≤-trans (lem-lo {pw (suc j) (a + w)} {pw (suc j) a} {dpw (suc j) a} {Φ a} {Y a w} {a} {w} {P C} {P (k2 j)}
          (Y-lo aw w1) (lo-bern (suc j)) w1 (Φ≤1 a) (bd2 j (≤-trans ≤-+ʳ aw)))
        (≤-reflexive (+-cong (+-cong (*-cong refl (sym (Y-mul aw w1))) refl) refl)))

    ----------------------------------------------------------------------------
    -- bounds on [0, M], and the pack

    Bd : (∣A∣ → ∣A∣) → ℕ → Set₁
    Bd u K = ∀ {x} → x ≤ M → u x ≤ P K

    hhB : ∀ i → Σ ℕ (Bd (hh i))
    hhB i = proj₁ (pwB m Mm i) , (λ {x} xM → ≤-trans (*-mono (pw i x) (Φ≤1 x))
      (≤-trans (≤-reflexive (*-identityʳ _)) (proj₂ (pwB m Mm i) xM)))

    khB : ∀ j → Σ ℕ (Bd (kh j))
    khB j = (suc j ℕ.+ proj₁ (hhB j)) , (λ xM → P-* (natE≤P (suc j)) (proj₂ (hhB j) xM))

    Pr : ℕ → ℕ → Set₁
    Pr j K = LipOK (hh (suc (suc j))) (P K) × LipOK (kh j) (P K) × Cr1 j K × Cr2 j K
      × Bd (hh (suc j)) K × Bd (hh (suc (suc j))) K × Bd (kh j) K

    cr-mono1 : ∀ {j K K′} → K ℕ.≤ K′ → Cr1 j K → Cr1 j K′
    cr-mono1 le f aw w1 = ≤-trans (f aw w1) (+-mono ≤-refl (*-mono _ (P-mono le)))

    cr-mono2 : ∀ {j K K′} → K ℕ.≤ K′ → Cr2 j K → Cr2 j K′
    cr-mono2 le f aw w1 = ≤-trans (f aw w1) (+-mono ≤-refl (*-mono _ (P-mono le)))

    bd-mono : ∀ {u K K′} → K ℕ.≤ K′ → Bd u K → Bd u K′
    bd-mono le f xM = ≤-trans (f xM) (P-mono le)

    upLip : ∀ i → Up (λ K → LipOK (hh i) (P K))
    upLip i = upI lip-mono (hh-lip i)

    upLipK : ∀ j → Up (λ K → LipOK (kh j) (P K))
    upLipK j = upI lip-mono (suc j ℕ.+ proj₁ (hh-lip j) , lip-scale {L = suc j} (natE≤P (suc j)) (proj₂ (hh-lip j)))

    prim : ∀ j → Up (Pr j)
    prim j = both (upLip (suc (suc j))) (both (upLipK j) (both (upI cr-mono1 (k1 j , λ {a} {w} → cert1 j {a} {w}))
      (both (upI cr-mono2 (k2 j , λ {a} {w} → cert2 j {a} {w}))
      (both (upI bd-mono (hhB (suc j))) (both (upI bd-mono (hhB (suc (suc j)))) (upI bd-mono (khB j)))))))

    sIdx : ℕ → ℕ
    sIdx S = suc (S ℕ.+ suc (S ℕ.+ S))

    pSl : ∀ S → suc (S ℕ.+ S) ℕ.≤ sIdx S
    pSl S = ℕ.s≤s (ℕ.+-monoʳ-≤ S (ℕ.≤-trans (ℕ.m≤m+n S S) (ℕ.n≤1+n (S ℕ.+ S))))

    pC3 : ∀ S → P S + (P S + P S) ≤ P (sIdx S)
    pC3 S = P-+ {i = S} {j = suc (S ℕ.+ S)} ≤-refl (P-+ {i = S} {j = S} ≤-refl ≤-refl)

    Pack : ℕ → ℕ → Set₁
    Pack j S = (P S + (P S + P S) ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → hh (suc (suc j)) x + P S ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → kh j x + P S ≤ P (sIdx S))
      × LipOK (hh (suc (suc j))) (P S) × LipOK (kh j) (P S) × Cr1 j S × Cr2 j S
      × (∀ {x} → x ≤ M → hh (suc j) x ≤ P (sIdx S))

    pack-at : ∀ j S → Pr j S → Pack j S
    pack-at j S (hl , kl , c1 , c2 , bG , bh , bk) =
      pC3 S , (λ xM → ≤-trans (P-+ {i = S} {j = S} (bh xM) ≤-refl) (P-mono (pSl S)))
      , (λ xM → ≤-trans (P-+ {i = S} {j = S} (bk xM) ≤-refl) (P-mono (pSl S)))
      , hl , kl , c1 , c2 , (λ xM → ≤-trans (bG xM) (P-mono (ℕ.≤-trans (ℕ.m≤m+n S (suc (S ℕ.+ S))) (ℕ.n≤1+n _))))

    -- abstract: the constant is only used through the bounds, never computed
    abstract
      pack : ∀ j → Σ ℕ (Pack j)
      pack j = proj₁ (prim j) , pack-at j (proj₁ (prim j)) (proj₂ (prim j) ℕ.≤-refl)
