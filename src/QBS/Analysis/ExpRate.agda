{-# OPTIONS --safe --without-K #-}

-- The exponential with a rate λ: the pointwise algebra, over an abstract Archimedean ω-semiring, that moves the rate-1
-- certificates of `Analysis/PolyExpCert` to `x ↦ e^{−λx}`.  There is no division, so the rate comes with a reciprocal
-- `c` (`λ c ≈ 1`), and every rescaling is exact algebra:
--   * `cert0`: for `h = e^{−λx}`, `G = c e^{−λx}` the plain certificate on a piece of width `w` (with `y = e^{−λw}`,
--     `y + λw y ≤ 1 ≤ y + λw`): `G(a+w) + w h(a+w) ≤ G a ≤ G(a+w) + w h(a)`, since `c λ w = w`;
--   * `Rate`: for `s` a bound `s ≤ 2^σ` and `λ ≤ 1`, the scaled data `h = s H(λx)`, `k = s K(λx)`, `G = s c H(λx)` (with `H`
--     the rate-1 function `xʲ⁺¹ e^{−x}` and `K = (j+1) xʲ e^{−x}`) satisfy the Lipschitz bounds and the certificate with
--     one constant `2^W`, from the rate-1 data at the point `λx` and width `λw` (`rs`: multiply by `s c` and use `cλ = 1`);
--     `hq≈`, `kq≈` identify them with `xʲ⁺¹ e^{−λx}` and `c (j+1) xʲ e^{−λx}` for `s = cʲ⁺¹`;
--   * `Tl`: the tail `κ xⁱ e^{−λN}`, at `N = ν N′` for a far-out `N′`, from the rate-1 tail of `Analysis/ExpTail`.
module QBS.Analysis.ExpRate where

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
open import QBS.Analysis.ExpRateExt using (module AlgExt)

module AlgRate (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (hp)
  open AlgT A R using (P; exp-cert)
  open AlgP A R using (P-mono; P-+; P-*; P-mul; Phz; *-mono₂; *-monoʳ; pw; pw-mono; pw-mul; pw-one; pwB; natE≤P; natE-*; module Ex)
  open Exp A using (natE)
  open AlgExt A R using (module Lip; module Cert2)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  pw-cong : ∀ i {x y} → x ≈ y → pw i x ≈ pw i y
  pw-cong i e = ≤-antisym (pw-mono i (≤-reflexive e)) (pw-mono i (≤-reflexive (sym e)))

  ----------------------------------------------------------------------------
  -- the plain certificate for `G = c e^{−λx}`

  u-eq : ∀ {l c w q} → l * c ≈ 1# → (l * w) * (c * q) ≈ w * q
  u-eq {l} {c} {w} {q} lc = trans
    (solve 4 (λ l′ c′ w′ q′ → (l′ :* w′) :* (c′ :* q′) := (l′ :* c′) :* (w′ :* q′)) refl l c w q)
    (trans (*-cong lc refl) (*-identityˡ _))

  -- with p = e^{−λa} and y = e^{−λw}, the certificate for G = c p y at a + w
  cert0 : ∀ {l c w p y} → l * c ≈ 1# → y + (l * w) * y ≤ 1# → 1# ≤ y + (l * w) →
    ((c * (p * y)) + w * (p * y) ≤ c * p) × (c * p ≤ (c * (p * y)) + w * p)
  cert0 {l} {c} {w} {p} {y} lc b c′ = lo , hi
    where
    e : (l * w) * ((c * p) * y) ≈ w * (p * y)
    e = trans (*-cong refl (*-assoc c p y)) (u-eq lc)
    lo : (c * (p * y)) + w * (p * y) ≤ c * p
    lo = ≤-trans (≤-reflexive (+-cong (sym (*-assoc c p y)) (sym e))) (proj₁ (exp-cert {c * p} {y} {l * w} b c′))
    hi : c * p ≤ (c * (p * y)) + w * p
    hi = ≤-trans (proj₂ (exp-cert {c * p} {y} {l * w} b c′)) (≤-reflexive (+-cong (*-assoc c p y) (u-eq lc)))

  ----------------------------------------------------------------------------
  -- scaling a rate-1 certificate at (λa, λw) by s c

  sc-lt : ∀ {l c s t Y} → l * c ≈ 1# → (s * c) * ((l * t) * Y) ≈ t * (s * Y)
  sc-lt {l} {c} {s} {t} {Y} lc = trans
    (solve 5 (λ s′ c′ l′ t′ y′ → (s′ :* c′) :* ((l′ :* t′) :* y′) := (l′ :* c′) :* (t′ :* (s′ :* y′))) refl s c l t Y)
    (trans (*-cong lc refl) (*-identityˡ _))

  sc-err : ∀ {l c s t U} → l * c ≈ 1# → (s * c) * (((l * t) * (l * t)) * U) ≈ (t * t) * ((s * l) * U)
  sc-err {l} {c} {s} {t} {U} lc = trans
    (solve 5 (λ s′ c′ l′ t′ u′ → (s′ :* c′) :* (((l′ :* t′) :* (l′ :* t′)) :* u′)
        := (l′ :* c′) :* ((t′ :* t′) :* ((s′ :* l′) :* u′))) refl s c l t U)
    (trans (*-cong lc refl) (*-identityˡ _))

  rs : ∀ {l c s t X1 Y1 X2 Y2 U} → l * c ≈ 1# →
    X1 + (l * t) * Y1 ≤ (X2 + (l * t) * Y2) + ((l * t) * (l * t)) * U →
    (s * c) * X1 + t * (s * Y1) ≤ ((s * c) * X2 + t * (s * Y2)) + (t * t) * ((s * l) * U)
  rs {l} {c} {s} {t} {X1} {Y1} {X2} {Y2} {U} lc h = ≤-trans (≤-reflexive e1) (≤-trans (*-mono (s * c) h) (≤-reflexive e2))
    where
    e1 : (s * c) * X1 + t * (s * Y1) ≈ (s * c) * (X1 + (l * t) * Y1)
    e1 = trans (+-cong refl (sym (sc-lt lc))) (sym (distribˡ (s * c) X1 ((l * t) * Y1)))
    e2 : (s * c) * ((X2 + (l * t) * Y2) + ((l * t) * (l * t)) * U)
      ≈ ((s * c) * X2 + t * (s * Y2)) + (t * t) * ((s * l) * U)
    e2 = trans (distribˡ (s * c) (X2 + (l * t) * Y2) (((l * t) * (l * t)) * U))
      (+-cong (trans (distribˡ (s * c) X2 ((l * t) * Y2)) (+-cong refl (sc-lt lc))) (sc-err lc))

  ----------------------------------------------------------------------------
  -- the moments: `xⁱ = cⁱ (λx)ⁱ`, so `cʲ⁺¹ (λx)ʲ⁺¹ e = xʲ⁺¹ e` and `cʲ⁺¹ (j+1) (λx)ʲ e = c (j+1) xʲ e`

  module Sc (l c : ∣A∣) (lc : l * c ≈ 1#) where
    cx : ∀ x → c * (l * x) ≈ x
    cx x = trans (solve 3 (λ c′ l′ x′ → c′ :* (l′ :* x′) := (l′ :* c′) :* x′) refl c l x)
      (trans (*-cong lc refl) (*-identityˡ x))

    pw-c : ∀ i x → pw i x ≈ pw i c * pw i (l * x)
    pw-c i x = trans (pw-cong i (sym (cx x))) (pw-mul i c (l * x))

    hq≈ : ∀ j x e → pw (suc j) c * (pw (suc j) (l * x) * e) ≈ pw (suc j) x * e
    hq≈ j x e = trans (sym (*-assoc (pw (suc j) c) (pw (suc j) (l * x)) e)) (*-cong (sym (pw-c (suc j) x)) refl)

    kq≈ : ∀ j x e → pw (suc j) c * (natE (suc j) * (pw j (l * x) * e)) ≈ (c * natE (suc j)) * (pw j x * e)
    kq≈ j x e = trans
      (solve 5 (λ c′ pc n py e′ → (c′ :* pc) :* (n :* (py :* e′)) := (c′ :* n) :* ((pc :* py) :* e′)) refl
        c (pw j c) (natE (suc j)) (pw j (l * x)) e)
      (*-cong refl (*-cong (sym (pw-c j x)) refl))

    -- `λ cⁱ⁺¹ f = cⁱ f`
    l-step : ∀ p f → l * ((c * p) * f) ≈ p * f
    l-step p f = trans (solve 4 (λ l′ c′ p′ f′ → l′ :* ((c′ :* p′) :* f′) := (l′ :* c′) :* (p′ :* f′)) refl l c p f)
      (trans (*-cong lc refl) (*-identityˡ _))

    -- `cⁿ λⁿ = 1`
    pw-lc : ∀ n → pw n c * pw n l ≈ 1#
    pw-lc n = trans (sym (pw-mul n c l)) (trans (pw-cong n (trans (*-comm c l) lc)) (pw-one n))

    -- the arithmetic of `λⁿ · (cⁿ f − 0) ≃ f`
    rate-eq : ∀ n f → (((pw n c * f) * pw n l + 0# * 0#) + 0#) + 0# ≈ (f + ((pw n c * f) * 0# + 0# * pw n l)) + 0#
    rate-eq n f = trans (solve 3 (λ pc pl f′ → (((pc :* f′) :* pl :+ con 0 :* con 0) :+ con 0) :+ con 0 := (pc :* pl) :* f′)
        refl (pw n c) (pw n l) f)
      (trans (*-cong (pw-lc n) refl) (trans (*-identityˡ f)
        (sym (solve 3 (λ pc pl f′ → (f′ :+ ((pc :* f′) :* con 0 :+ con 0 :* pl)) :+ con 0 := f′) refl (pw n c) (pw n l) f))))

    -- the arithmetic of the variance `λ² (2c² − c²) = 1`, with `f₁ = 1!` and `f₂ = 2!` given
    PV : ∣A∣ → ∣A∣ → ∣A∣
    PV f1 f2 = pw 2 c * f2 + ((pw 1 c * f1) * 0# + 0# * (pw 1 c * f1))

    NV : ∣A∣ → ∣A∣
    NV f1 = 0# + ((pw 1 c * f1) * (pw 1 c * f1) + 0# * 0#)

    uu : (c * c) * (l * l) ≈ 1#
    uu = trans (solve 2 (λ c′ l′ → (c′ :* c′) :* (l′ :* l′) := (c′ :* l′) :* (c′ :* l′)) refl c l)
      (trans (*-cong (trans (*-comm c l) lc) (trans (*-comm c l) lc)) (*-identityˡ 1#))

    var-e1 : ∀ f1 f2 → (((PV f1 f2 * pw 2 l + NV f1 * 0#) + 0#) + 0#) ≈ f2 * ((c * c) * (l * l))
    var-e1 f1 f2 = solve 4 (λ c′ l′ f1′ f2′ →
      let a1 = c′ :* con 1 :* f1′ ; pv = c′ :* (c′ :* con 1) :* f2′ :+ (a1 :* con 0 :+ con 0 :* a1)
          nv = con 0 :+ (a1 :* a1 :+ con 0 :* con 0)
      in ((pv :* (l′ :* (l′ :* con 1)) :+ nv :* con 0) :+ con 0) :+ con 0 := f2′ :* ((c′ :* c′) :* (l′ :* l′))) refl c l f1 f2

    var-e2 : ∀ f1 f2 → (1# + (PV f1 f2 * 0# + NV f1 * pw 2 l)) + 0# ≈ 1# + (f1 * f1) * ((c * c) * (l * l))
    var-e2 f1 f2 = solve 4 (λ c′ l′ f1′ f2′ →
      let a1 = c′ :* con 1 :* f1′ ; pv = c′ :* (c′ :* con 1) :* f2′ :+ (a1 :* con 0 :+ con 0 :* a1)
          nv = con 0 :+ (a1 :* a1 :+ con 0 :* con 0)
      in (con 1 :+ (pv :* con 0 :+ nv :* (l′ :* (l′ :* con 1)))) :+ con 0
        := con 1 :+ (f1′ :* f1′) :* ((c′ :* c′) :* (l′ :* l′))) refl c l f1 f2

    var-eq : ∀ f1 f2 → f1 ≈ 1# → f2 ≈ 1# + 1# →
      (((PV f1 f2 * pw 2 l + NV f1 * 0#) + 0#) + 0#) ≈ (1# + (PV f1 f2 * 0# + NV f1 * pw 2 l)) + 0#
    var-eq f1 f2 h1 h2 = trans (trans (var-e1 f1 f2) (trans (*-cong h2 uu) (*-identityʳ (1# + 1#))))
      (sym (trans (var-e2 f1 f2) (+-cong refl (trans (*-cong (*-cong h1 h1) uu) (trans (*-identityʳ (1# * 1#)) (*-identityʳ 1#))))))

  -- the product of the rate (a+1)/(b+1) and its reciprocal: `(p v) (q u) = (u p)(v q)`
  rat-lc : ∀ {p q u v} → u * p ≈ 1# → v * q ≈ 1# → (p * v) * (q * u) ≈ 1#
  rat-lc {p} {q} {u} {v} up vq = trans (solve 4 (λ p′ q′ u′ v′ → (p′ :* v′) :* (q′ :* u′) := (u′ :* p′) :* (v′ :* q′)) refl p q u v)
    (trans (*-cong up vq) (*-identityˡ 1#))

  -- the recursion of the moments: `c (j+1) · cʲ⁺¹ n! = cʲ⁺² (j+1)!`
  fact-step : ∀ {c n p f} → (c * n) * (p * f) ≈ (c * p) * (n * f)
  fact-step {c} {n} {p} {f} = solve 4 (λ c′ n′ p′ f′ → (c′ :* n′) :* (p′ :* f′) := (c′ :* p′) :* (n′ :* f′)) refl c n p f

  -- the scaled functions, as plain definitions (no proofs), so that the concrete tests unify syntactically:
  -- with `qq i x = (λx)ⁱ e^{−λx}`:  `hR = s qq(j+1)`, `kR = s (j+1) qq j`, `GR = s c qq(j+1)`
  module Fn (E : ∣A∣ → ∣A∣) (l c s : ∣A∣) (j : ℕ) where
    qq : ℕ → ∣A∣ → ∣A∣
    qq i x = pw i (l * x) * E (l * x)

    hR kR GR : ∣A∣ → ∣A∣
    hR x = s * qq (suc j) x
    kR x = s * (natE (suc j) * qq j x)
    GR x = (s * c) * qq (suc j) x

  ----------------------------------------------------------------------------
  -- the scaled data for `xʲ⁺¹ e^{−λx}` against `c (j+1) xʲ e^{−λx}`

  module Rate (E : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ {a t} → a + t ≤ M → t ≤ 1# → E (a + t) ≈ E a * E t)
    (E-b : ∀ {t} → t ≤ 1# → E t + t * E t ≤ 1#) (E-c : ∀ {t} → t ≤ 1# → 1# ≤ E t + t)
    (E-cong : ∀ {x y} → x ≈ y → E x ≈ E y)
    (l c s : ∣A∣) (lc : l * c ≈ 1#) (Mo : ∣A∣) (lM : ∀ {x} → x ≤ Mo → l * x ≤ M) (μ : ℕ) (lμ : l ≤ P μ)
    (σ₀ γ : ℕ) (sσ₀ : s ≤ P σ₀) (cγ : c ≤ P γ) (j : ℕ) where
    open Ex E M m Mm E≤1 E-anti E-add E-b E-c

    -- the rate enlarges the bound of `s`
    σ : ℕ
    σ = σ₀ ℕ.+ μ

    sσ : s ≤ P σ
    sσ = ≤-trans sσ₀ (P-mono (ℕ.m≤m+n σ₀ μ))

    S sI W Z : ℕ
    S = proj₁ (pack j)
    sI = sIdx S
    W = (σ ℕ.+ γ) ℕ.+ sI
    Z = sIdx W

    pk = proj₂ (pack j)

    hb₀ : ∀ {x} → x ≤ M → hh (suc j) x + P S ≤ P sI
    hb₀ = proj₁ (proj₂ pk)

    kb₀ : ∀ {x} → x ≤ M → kh j x + P S ≤ P sI
    kb₀ = proj₁ (proj₂ (proj₂ pk))

    hl₀ : LipOK (hh (suc j)) (P S)
    hl₀ = proj₁ (proj₂ (proj₂ (proj₂ pk)))

    kl₀ : LipOK (kh j) (P S)
    kl₀ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ pk))))

    cr1₀ : ∀ {a w} → a + w ≤ M → w ≤ 1# →
      hh (suc j) (a + w) + w * hh (suc j) a ≤ (hh (suc j) a + w * kh j a) + (w * w) * P S
    cr1₀ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk)))))

    cr2₀ : ∀ {a w} → a + w ≤ M → w ≤ 1# →
      hh (suc j) a + w * kh j a ≤ (hh (suc j) (a + w) + w * hh (suc j) a) + (w * w) * P S
    cr2₀ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk))))))

    gb₀ : ∀ {x} → x ≤ M → hh (suc j) x ≤ P sI
    gb₀ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ pk))))))

    hh-cong : ∀ i {x y} → x ≈ y → hh i x ≈ hh i y
    hh-cong i e = *-cong (pw-cong i e) (E-cong e)

    -- the scaled data (`Fn`)
    open Fn E l c s j public

    hR-cong : ∀ {x y} → x ≈ y → hR x ≈ hR y
    hR-cong e = *-cong refl (hh-cong (suc j) (*-cong refl e))

    kR-cong : ∀ {x y} → x ≈ y → kR x ≈ kR y
    kR-cong {x} {y} e = *-cong refl (*-cong refl (hh-cong j (*-cong refl e)))

    GR-cong : ∀ {x y} → x ≈ y → GR x ≈ GR y
    GR-cong e = *-cong refl (hh-cong (suc j) (*-cong refl e))

    ----------------------------------------------------------------------------
    -- indices

    S≤sI : S ℕ.≤ sI
    S≤sI = ℕ.≤-trans (ℕ.m≤m+n S _) (ℕ.n≤1+n _)

    σS≤W : (σ ℕ.+ S) ℕ.≤ W
    σS≤W = ℕ.≤-trans (ℕ.+-monoʳ-≤ σ S≤sI) (ℕ.+-monoˡ-≤ sI (ℕ.m≤m+n σ γ))

    σsI≤W : (σ ℕ.+ sI) ℕ.≤ W
    σsI≤W = ℕ.+-monoˡ-≤ sI (ℕ.m≤m+n σ γ)

    -- the bounds
    hRb : ∀ {x} → x ≤ Mo → hR x ≤ P W
    hRb xM = ≤-trans (P-* sσ (gb₀ (lM xM))) (P-mono σsI≤W)

    kRb : ∀ {x} → x ≤ Mo → kR x ≤ P W
    kRb xM = ≤-trans (P-* sσ (≤-trans ≤-+ʳ (kb₀ (lM xM)))) (P-mono σsI≤W)

    GRb : ∀ {x} → x ≤ Mo → GR x ≤ P W
    GRb xM = P-* (P-* sσ cγ) (gb₀ (lM xM))

    hbR : ∀ {x} → x ≤ Mo → hR x + P W ≤ P Z
    hbR xM = ≤-trans (P-+ {i = W} {j = W} (hRb xM) ≤-refl) (P-mono (pSl W))

    kbR : ∀ {x} → x ≤ Mo → kR x + P W ≤ P Z
    kbR xM = ≤-trans (P-+ {i = W} {j = W} (kRb xM) ≤-refl) (P-mono (pSl W))

    c3R : P W + (P W + P W) ≤ P Z
    c3R = pC3 W

    ----------------------------------------------------------------------------
    -- the Lipschitz bounds

    slσ : s * l ≤ P σ
    slσ = P-* sσ₀ lμ

    sl : ∀ {X Y t K} → X ≤ Y + (l * t) * P K → s * X ≤ s * Y + t * P (σ ℕ.+ K)
    sl {X} {Y} {t} {K} h = ≤-trans (*-mono s h)
      (≤-trans (≤-reflexive (solve 5 (λ s′ y t′ k l′ → s′ :* (y :+ (l′ :* t′) :* k) := s′ :* y :+ t′ :* ((s′ :* l′) :* k))
          refl s Y t (P K) l))
        (+-mono ≤-refl (*-mono t (P-* slσ (≤-refl {P K})))))

    dist : ∀ {a t} → l * (a + t) ≈ l * a + l * t
    dist {a} {t} = distribˡ l a t

    at′ : ∀ {a t} → a + t ≤ Mo → l * a + l * t ≤ M
    at′ at = ≤-trans (≤-reflexive (sym dist)) (lM at)

    -- the rate-1 data is used at the width `λ t ≤ 1`, which holds for `t ≤ ½ᴷ` with `K = μ + 0`
    Kr : ℕ
    Kr = μ ℕ.+ 0

    Kr-ok : ∀ {t} → t ≤ hp Kr → l * t ≤ 1#
    Kr-ok {t} tK = ≤-trans (*-mono₂ lμ tK) (≤-reflexive (Phz μ 0))

    hR-up0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# → hR (a + t) ≤ hR a + t * P W
    hR-up0 {a} {t} at lt1 = ≤-trans (≤-resp (sym (*-cong refl (hh-cong (suc j) dist))) refl
        (sl {hh (suc j) (l * a + l * t)} {hh (suc j) (l * a)} {t} {S} (proj₁ hl₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono t (P-mono σS≤W)))

    hR-dn0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# → hR a ≤ hR (a + t) + t * P W
    hR-dn0 {a} {t} at lt1 = ≤-trans (≤-resp refl (+-cong (*-cong refl (hh-cong (suc j) (sym dist))) refl)
        (sl {hh (suc j) (l * a)} {hh (suc j) (l * a + l * t)} {t} {S} (proj₂ hl₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono t (P-mono σS≤W)))

    kR-up0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# → kR (a + t) ≤ kR a + t * P W
    kR-up0 {a} {t} at lt1 = ≤-trans (≤-resp (sym (*-cong refl (*-cong refl (hh-cong j dist)))) refl
        (sl {kh j (l * a + l * t)} {kh j (l * a)} {t} {S} (proj₁ kl₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono t (P-mono σS≤W)))

    kR-dn0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# → kR a ≤ kR (a + t) + t * P W
    kR-dn0 {a} {t} at lt1 = ≤-trans (≤-resp refl (+-cong (*-cong refl (*-cong refl (hh-cong j (sym dist)))) refl)
        (sl {kh j (l * a)} {kh j (l * a + l * t)} {t} {S} (proj₂ kl₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono t (P-mono σS≤W)))

    ----------------------------------------------------------------------------
    -- the certificates

    err : (s * l) * P S ≤ P W
    err = ≤-trans (P-* slσ (≤-refl {P S})) (P-mono σS≤W)

    cert1R0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# →
      GR (a + t) + t * hR a ≤ (GR a + t * kR a) + (t * t) * P W
    cert1R0 {a} {t} at lt1 = ≤-trans
      (≤-resp (+-cong (*-cong refl (hh-cong (suc j) (sym dist))) refl) refl (rs {t = t} lc (cr1₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono (t * t) err))

    cert2R0 : ∀ {a t} → a + t ≤ Mo → l * t ≤ 1# →
      GR a + t * kR a ≤ (GR (a + t) + t * hR a) + (t * t) * P W
    cert2R0 {a} {t} at lt1 = ≤-trans
      (≤-resp refl (+-cong (+-cong (*-cong refl (hh-cong (suc j) (sym dist))) refl) refl) (rs {t = t} lc (cr2₀ (at′ at) lt1)))
      (+-mono ≤-refl (*-mono (t * t) err))

    -- G vanishes at 0
    GR0 : GR 0# ≈ 0#
    GR0 = trans (*-cong refl (trans (*-cong (trans (*-cong (zeroʳ l) refl) (zeroˡ _)) refl) (zeroˡ _))) (zeroʳ _)

    ----------------------------------------------------------------------------
    -- all widths `t ≤ 1` from the widths `t ≤ ½ᴷ` with `λ t ≤ 1` (`Analysis/ExpRateExt`)

    module Lh = Lip Mo hR (P W) hR-cong
    module LkU = Lip Mo kR (P W) kR-cong

    hR-up : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → hR (a + t) ≤ hR a + t * P W
    hR-up = Lh.up-ext Kr (λ at tK → hR-up0 at (Kr-ok tK))

    hR-dn : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → hR a ≤ hR (a + t) + t * P W
    hR-dn = Lh.dn-ext Kr (λ at tK → hR-dn0 at (Kr-ok tK))

    kR-up : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → kR (a + t) ≤ kR a + t * P W
    kR-up = LkU.up-ext Kr (λ at tK → kR-up0 at (Kr-ok tK))

    kR-dn : ∀ {a t} → a + t ≤ Mo → t ≤ 1# → kR a ≤ kR (a + t) + t * P W
    kR-dn = LkU.dn-ext Kr (λ at tK → kR-dn0 at (Kr-ok tK))

    module Cx = Cert2 Mo hR kR GR (P W) GR-cong hR-up hR-dn kR-up kR-dn

    cert1R : ∀ {a t} → a + t ≤ Mo → t ≤ 1# →
      GR (a + t) + t * hR a ≤ (GR a + t * kR a) + (t * t) * P W
    cert1R = Cx.ext1 Kr (λ at tK → cert1R0 at (Kr-ok tK))

    cert2R : ∀ {a t} → a + t ≤ Mo → t ≤ 1# →
      GR a + t * kR a ≤ (GR (a + t) + t * hR a) + (t * t) * P W
    cert2R = Cx.ext2 Kr (λ at tK → cert2R0 at (Kr-ok tK))

  ----------------------------------------------------------------------------
  -- the tail `κ xⁱ e^{−λN}` along a subsequence, from the rate-1 tail `xⁱ e^{−N} ≤ ½ᵐ`

  module Tl (E : ∣A∣ → ∣A∣) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (tl : ∀ e m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × pw e (natE N) * E (natE N) ≤ hp m))
    (l c κ : ∣A∣) (lc : l * c ≈ 1#) (μ : ℕ) (lμ : l ≤ P μ) (ν k : ℕ) (cν : c ≤ natE (suc ν)) (κk : κ ≤ P k) (i : ℕ) where
    n1 : ℕ
    n1 = suc ν

    -- the rate is at most 2ᵘ, so `λ n1 ≤ 2^(μ+n1)`
    lB : l * natE n1 ≤ P (μ ℕ.+ n1)
    lB = ≤-trans (*-mono₂ lμ (natE≤P n1)) (≤-reflexive (P-mul μ n1))

    B : ℕ
    B = proj₁ (pwB {l * natE n1} (μ ℕ.+ n1) lB i)

    pB : pw i (l * natE n1) ≤ P B
    pB = proj₂ (pwB {l * natE n1} (μ ℕ.+ n1) lB i) ≤-refl

    one≤ : 1# ≤ l * natE n1
    one≤ = ≤-trans (≤-reflexive (sym lc)) (*-mono l cν)

    -- N = n1 N′ is stretched by the rate to at least N′
    lN≥ : ∀ N′ → natE N′ ≤ l * natE (n1 ℕ.* N′)
    lN≥ N′ = ≤-trans (≤-reflexive (sym (*-identityˡ (natE N′)))) (≤-trans (*-monoʳ (natE N′) one≤)
      (≤-reflexive (trans (*-assoc l (natE n1) (natE N′)) (*-cong refl (sym (natE-* n1 N′))))))

    lN-eq : ∀ N′ → l * natE (n1 ℕ.* N′) ≈ (l * natE n1) * natE N′
    lN-eq N′ = trans (*-cong refl (natE-* n1 N′)) (sym (*-assoc l (natE n1) (natE N′)))

    pw-le : ∀ N′ → pw i (l * natE (n1 ℕ.* N′)) ≤ P B * pw i (natE N′)
    pw-le N′ = ≤-trans (≤-reflexive (trans (pw-cong i (lN-eq N′)) (pw-mul i (l * natE n1) (natE N′))))
      (*-monoʳ (pw i (natE N′)) pB)

    -- the bound at N = n1 N′ from the rate-1 bound at N′
    tail-bound : ∀ m N′ → pw i (natE N′) * E (natE N′) ≤ hp ((k ℕ.+ B) ℕ.+ m) →
      κ * (pw i (l * natE (n1 ℕ.* N′)) * E (l * natE (n1 ℕ.* N′))) ≤ hp m
    tail-bound m N′ bd = ≤-trans (*-mono κ (*-mono₂ (pw-le N′) (E-anti (lN≥ N′))))
      (≤-trans (*-mono κ (≤-reflexive (*-assoc (P B) (pw i (natE N′)) (E (natE N′)))))
      (≤-trans (*-mono κ (*-mono (P B) bd))
      (≤-trans (*-monoʳ (P B * hp ((k ℕ.+ B) ℕ.+ m)) κk)
      (≤-reflexive (trans (sym (*-assoc (P k) (P B) (hp ((k ℕ.+ B) ℕ.+ m))))
        (trans (*-cong (P-mul k B) refl) (Phz (k ℕ.+ B) m)))))))

    tailR : ∀ m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × κ * (pw i (l * natE N) * E (l * natE N)) ≤ hp m)
    tailR m N₀ = n1 ℕ.* N′ , ℕ.≤-trans (proj₁ (proj₂ r)) (ℕ.m≤m+n N′ (ν ℕ.* N′)) , tail-bound m N′ (proj₂ (proj₂ r))
      where
      r : Σ ℕ (λ N → N₀ ℕ.≤ N × pw i (natE N) * E (natE N) ≤ hp ((k ℕ.+ B) ℕ.+ m))
      r = tl i ((k ℕ.+ B) ℕ.+ m) N₀
      N′ : ℕ
      N′ = proj₁ r
