{-# OPTIONS --safe --without-K #-}

-- Pointwise algebra for the integrals `∫₀^∞ xʲ e^{−x} dx` through the Lipschitz tail FTC (`Analysis/TailFTCLip`).
--
-- Over an abstract Archimedean ω-semiring A with a function E (the exponential e^{−x}) satisfying
--   E x ≤ 1,  E antitone,  E (a + t) = E a · E t when a + t ≤ M and t ≤ 1,
--   E t + t E t ≤ 1 ≤ E t + t  for t ≤ 1   (the facts `AlgT.exp-facts` derives from 1 + t ≤ eᵗ ≤ 1 + t + t²),
-- and M ≤ 2ᵐ, this module proves for hh j x = xʲ E x (with the powers and their formal derivative `dpw`):
--   * `pw-lip`: Bernoulli's inequality with remainder, `xʲ` is Lipschitz on [0, M] (`LipOK`, with constants 2ᴷ);
--   * `hh-lip`: `hh j` is Lipschitz on [0, M];
--   * `cert`: with G = h = hh (j+1), k = (j+1)·hh j and `G′ = k − h`, the certificate up to w² c on every [a, a + w]:
--       G (a+w) + w h(a) ≤ G a + w k(a) + w² c    and    G a + w k(a) ≤ G (a+w) + w h(a) + w² c.
-- Everything is first order in w: the constants absorb the second-order terms, so the exponential needs only the
-- bounds `y + w y ≤ 1 ≤ y + w` (and `y + w ≤ 1 + w²`, derived).
module QBS.Analysis.PolyExpCert where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.TailFTC using (module AlgT)

module AlgP (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; cancel≤; half+half)
  open AlgT A R using (P; P≥1; cancel≤P)
  open Exp A using (natE)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- multiplicative monotonicity and the powers of two

  *-monoʳ : ∀ c {a b} → a ≤ b → a * c ≤ b * c
  *-monoʳ c ab = ≤-trans (≤-reflexive (*-comm _ c)) (≤-trans (*-mono c ab) (≤-reflexive (*-comm c _)))

  *-mono₂ : ∀ {x x′ y y′} → x ≤ x′ → y ≤ y′ → x * y ≤ x′ * y′
  *-mono₂ {x} {x′} {y} {y′} xx yy = ≤-trans (*-mono x yy) (*-monoʳ y′ xx)

  P-mono : ∀ {K K′} → K ℕ.≤ K′ → P K ≤ P K′
  P-mono {K′ = K′} ℕ.z≤n = P≥1 K′
  P-mono (ℕ.s≤s e) = +-mono (P-mono e) (P-mono e)

  P-+ : ∀ {x y i j} → x ≤ P i → y ≤ P j → x + y ≤ P (suc (i ℕ.+ j))
  P-+ {i = i} {j} xi yj = +-mono (≤-trans xi (P-mono (ℕ.m≤m+n i j))) (≤-trans yj (P-mono (ℕ.m≤n+m j i)))

  P-mul : ∀ i j → P i * P j ≈ P (i ℕ.+ j)
  P-mul zero j = *-identityˡ _
  P-mul (suc i) j = trans (distribʳ (P j) (P i) (P i)) (+-cong (P-mul i j) (P-mul i j))

  P-* : ∀ {x y i j} → x ≤ P i → y ≤ P j → x * y ≤ P (i ℕ.+ j)
  P-* {x} {y} {i} {j} xi yj = ≤-trans (*-mono₂ xi yj) (≤-reflexive (P-mul i j))

  natE≤P : ∀ i → natE i ≤ P i
  natE≤P zero = 0-least
  natE≤P (suc i) = +-mono (natE≤P i) (P≥1 i)

  t*t≤t : ∀ {t} → t ≤ 1# → t * t ≤ t
  t*t≤t {t} t1 = ≤-trans (*-mono t t1) (≤-reflexive (*-identityʳ t))

  ----------------------------------------------------------------------------
  -- powers, their formal derivative, and Bernoulli's inequality

  pw dpw : ℕ → ∣A∣ → ∣A∣
  pw zero x = 1#
  pw (suc i) x = x * pw i x
  dpw zero x = 0#
  dpw (suc i) x = pw i x + x * dpw i x

  pw-mono : ∀ i {x y} → x ≤ y → pw i x ≤ pw i y
  pw-mono zero xy = ≤-refl
  pw-mono (suc i) xy = *-mono₂ xy (pw-mono i xy)

  -- (n+1) · xⁿ
  dpw-eq : ∀ j x → dpw (suc j) x ≈ natE (suc j) * pw j x
  dpw-eq zero x = solve 1 (λ x′ → con 1 :+ x′ :* con 0 := (con 0 :+ con 1) :* con 1) refl x
  dpw-eq (suc j) x = trans (+-cong refl (*-cong refl (dpw-eq j x)))
    (solve 3 (λ n x′ q → x′ :* q :+ x′ :* (n :* q) := (n :+ con 1) :* (x′ :* q)) refl (natE (suc j)) x (pw j x))

  lo-bern : ∀ i {a t} → pw i a + t * dpw i a ≤ pw i (a + t)
  lo-bern zero {a} {t} = ≤-reflexive (solve 1 (λ t′ → con 1 :+ t′ :* con 0 := con 1) refl t)
  lo-bern (suc i) {a} {t} = ≤-trans (≤-trans ≤-+ʳ
      (≤-reflexive (solve 4 (λ a′ t′ q d → (a′ :* q :+ t′ :* (q :+ a′ :* d)) :+ (t′ :* t′) :* d := (a′ :+ t′) :* (q :+ t′ :* d))
        refl a t (pw i a) (dpw i a))))
    (*-mono (a + t) (lo-bern i))

  pwB : ∀ {M} m → M ≤ P m → ∀ i → Σ ℕ (λ K → ∀ {a} → a ≤ M → pw i a ≤ P K)
  pwB m Mm zero = 0 , (λ _ → ≤-refl)
  pwB m Mm (suc i) with pwB m Mm i
  ... | K , f = (m ℕ.+ K) , (λ aM → P-* (≤-trans aM Mm) (f aM))

  dpwB : ∀ {M} m → M ≤ P m → ∀ i → Σ ℕ (λ K → ∀ {a} → a ≤ M → dpw i a ≤ P K)
  dpwB m Mm zero = 0 , (λ _ → 0-least)
  dpwB m Mm (suc i) with pwB m Mm i | dpwB m Mm i
  ... | K₁ , f | K₂ , g = suc (K₁ ℕ.+ (m ℕ.+ K₂)) , (λ aM → P-+ (f aM) (P-* (≤-trans aM Mm) (g aM)))

  -- Bernoulli's inequality with remainder: (a+t)ⁱ ≤ aⁱ + t · dpw i a + t² 2ᶜ on [0, M]
  up-bern : ∀ {M} m → M ≤ P m → ∀ i →
    Σ ℕ (λ C → ∀ {a t} → a + t ≤ M → pw i (a + t) ≤ (pw i a + t * dpw i a) + (t * t) * P C)
  up-bern m Mm zero = 0 , (λ _ → ≤-trans ≤-+ʳ ≤-+ʳ)
  up-bern m Mm (suc i) with up-bern m Mm i | dpwB m Mm i
  ... | C , f | D , g = suc (D ℕ.+ (m ℕ.+ C)) , (λ {a} {t} at →
    ≤-trans (*-mono (a + t) (f at))
      (≤-trans (≤-reflexive (solve 5 (λ a′ t′ q d c →
          (a′ :+ t′) :* ((q :+ t′ :* d) :+ (t′ :* t′) :* c)
          := (a′ :* q :+ t′ :* (q :+ a′ :* d)) :+ (t′ :* t′) :* (d :+ (a′ :+ t′) :* c)) refl a t (pw i a) (dpw i a) (P C)))
        (+-mono ≤-refl (*-mono (t * t) (P-+ (g (≤-trans ≤-+ʳ at)) (P-* (≤-trans at Mm) (≤-refl {P C})))))))

  lem-lo : ∀ {A′ D C p y w c} → y + w ≤ 1# + w * w → y ≤ 1# → p ≤ 1# → A′ + C ≤ c →
    ((A′ + w * D) + (w * w) * C) * (p * y) + w * (A′ * p) ≤ (A′ * p + w * (D * p)) + (w * w) * c
  lem-lo {A′} {D} {C} {p} {y} {w} {c} yw y1 p1 AC =
    ≤-trans (≤-reflexive (solve 6 (λ a d c′ p′ y′ w′ → ((a :+ w′ :* d) :+ (w′ :* w′) :* c′) :* (p′ :* y′) :+ w′ :* (a :* p′)
        := p′ :* ((a :* (y′ :+ w′) :+ (w′ :* d) :* y′) :+ ((w′ :* w′) :* c′) :* y′)) refl A′ D C p y w))
    (≤-trans (*-mono p (+-mono (+-mono (*-mono A′ yw) (*-mono (w * D) y1)) (*-mono ((w * w) * C) y1)))
    (≤-trans (≤-reflexive (solve 5 (λ a d c′ p′ w′ → p′ :* ((a :* (con 1 :+ w′ :* w′) :+ (w′ :* d) :* con 1) :+ ((w′ :* w′) :* c′) :* con 1)
        := p′ :* (a :+ (w′ :* d :+ (w′ :* w′) :* (a :+ c′)))) refl A′ D C p w))
    (≤-trans (*-mono p (+-mono ≤-refl (+-mono ≤-refl (*-mono (w * w) AC))))
    (≤-trans (≤-reflexive (solve 5 (λ a d c′ p′ w′ → p′ :* (a :+ (w′ :* d :+ (w′ :* w′) :* c′))
        := (a :* p′ :+ w′ :* (d :* p′)) :+ (w′ :* w′) :* (c′ :* p′)) refl A′ D c p w))
      (+-mono ≤-refl (*-mono (w * w) (≤-trans (*-mono c p1) (≤-reflexive (*-identityʳ c)))))))))

  lem-hi : ∀ {A′ B D p y w c} → 1# ≤ y + w → A′ + w * D ≤ B → D ≤ c → p ≤ 1# →
    A′ * p + w * (D * p) ≤ (B * (p * y) + w * (A′ * p)) + (w * w) * c
  lem-hi {A′} {B} {D} {p} {y} {w} {c} yw AB Dc p1 =
    ≤-trans (+-mono s1 s2)
      (≤-trans (≤-reflexive (solve 6 (λ a d p′ y′ w′ c′ → (a :* p′) :* (y′ :+ w′) :+ ((w′ :* (d :* p′)) :* y′ :+ (w′ :* w′) :* c′)
          := (((a :+ w′ :* d) :* (p′ :* y′)) :+ w′ :* (a :* p′)) :+ (w′ :* w′) :* c′) refl A′ D p y w c))
        (+-mono (+-mono (*-monoʳ (p * y) AB) ≤-refl) ≤-refl))
    where
    s1 : A′ * p ≤ (A′ * p) * (y + w)
    s1 = ≤-trans (≤-reflexive (sym (*-identityʳ _))) (*-mono (A′ * p) yw)
    Dp : D * p ≤ c
    Dp = ≤-trans (*-mono D p1) (≤-trans (≤-reflexive (*-identityʳ D)) Dc)
    s2 : w * (D * p) ≤ (w * (D * p)) * y + (w * w) * c
    s2 = ≤-trans (≤-reflexive (sym (*-identityʳ _))) (≤-trans (*-mono (w * (D * p)) yw)
      (≤-trans (≤-reflexive (solve 3 (λ w′ dp y′ → (w′ :* dp) :* (y′ :+ w′) := (w′ :* dp) :* y′ :+ (w′ :* w′) :* dp) refl w (D * p) y))
        (+-mono ≤-refl (*-mono (w * w) Dp))))

  ----------------------------------------------------------------------------
  -- the exponential: `y + w ≤ 1 + w²` from the first-order facts

  yt : ∀ {y t} → y + t * y ≤ 1# → 1# ≤ y + t → y + t ≤ 1# + t * t
  yt {y} {t} b c = cancel≤P ℕ.zero {t * y} ty1 e
    where
    ty1 : t * y ≤ 1#
    ty1 = ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm (t * y) y))) b
    e : t * y + (y + t) ≤ t * y + (1# + t * t)
    e = ≤-trans (≤-reflexive (solve 2 (λ t′ y′ → (t′ :* y′) :+ (y′ :+ t′) := (y′ :+ t′ :* y′) :+ t′) refl t y))
      (≤-trans (+-mono b (≤-refl {t}))
      (≤-trans (≤-reflexive (solve 1 (λ t′ → con 1 :+ t′ := con 1 :+ t′ :* con 1) refl t))
      (≤-trans (+-mono (≤-refl {1#}) (*-mono t c))
        (≤-reflexive (solve 2 (λ t′ y′ → con 1 :+ t′ :* (y′ :+ t′) := t′ :* y′ :+ (con 1 :+ t′ :* t′)) refl t y)))))

  module Ex (E : ∣A∣ → ∣A∣) (M : ∣A∣) (m : ℕ) (Mm : M ≤ P m)
    (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ {a t} → a + t ≤ M → t ≤ 1# → E (a + t) ≈ E a * E t)
    (E-b : ∀ {t} → t ≤ 1# → E t + t * E t ≤ 1#) (E-c : ∀ {t} → t ≤ 1# → 1# ≤ E t + t) where
    hh : ℕ → ∣A∣ → ∣A∣
    hh i x = pw i x * E x

    -- e^{−a} ≤ e^{−(a+t)} + t
    E-lipD : ∀ {a t} → a + t ≤ M → t ≤ 1# → E a ≤ E (a + t) + t
    E-lipD {a} {t} at t1 = ≤-trans (≤-reflexive (sym (*-identityʳ (E a)))) (≤-trans (*-mono (E a) (E-c t1))
      (≤-trans (≤-reflexive (solve 3 (λ p y t′ → p :* (y :+ t′) := p :* y :+ t′ :* p) refl (E a) (E t) t))
        (+-mono (≤-reflexive (sym (E-add at t1))) (≤-trans (*-mono t (E≤1 a)) (≤-reflexive (*-identityʳ t))))))

    LipOK : (∣A∣ → ∣A∣) → ∣A∣ → Set₁
    LipOK u c = (∀ {a t} → a + t ≤ M → t ≤ 1# → u (a + t) ≤ u a + t * c)
              × (∀ {a t} → a + t ≤ M → t ≤ 1# → u a ≤ u (a + t) + t * c)

    -- xⁱ is Lipschitz on [0, M]
    pw-lip : ∀ i → Σ ℕ (λ K → ∀ {a t} → a + t ≤ M → t ≤ 1# → pw i (a + t) ≤ pw i a + t * P K)
    pw-lip i with up-bern m Mm i | dpwB m Mm i
    ... | C , f | D , g = suc (D ℕ.+ C) , (λ {a} {t} at t1 →
      ≤-trans (f at)
        (≤-trans (+-mono (+-mono (≤-refl {pw i a}) (*-mono t (g (≤-trans ≤-+ʳ at)))) (*-monoʳ (P C) (t*t≤t t1)))
          (≤-trans (≤-reflexive (solve 4 (λ q t′ d c → (q :+ t′ :* d) :+ t′ :* c := q :+ t′ :* (d :+ c)) refl (pw i a) t (P D) (P C)))
            (+-mono (≤-refl {pw i a}) (*-mono t (P-+ (≤-refl {P D}) (≤-refl {P C})))))))

    hh-lip : ∀ i → Σ ℕ (λ K → LipOK (hh i) (P K))
    hh-lip i with pw-lip i | pwB m Mm i
    ... | K₁ , f | K₂ , g = (K₁ ℕ.+ K₂) , up , down
      where
      up : ∀ {a t} → a + t ≤ M → t ≤ 1# → hh i (a + t) ≤ hh i a + t * P (K₁ ℕ.+ K₂)
      up {a} {t} at t1 = ≤-trans (*-mono₂ (f at t1) (E-anti (≤-+ʳ {a} {t})))
        (≤-trans (≤-reflexive (solve 4 (λ q t′ c e → (q :+ t′ :* c) :* e := q :* e :+ t′ :* (c :* e)) refl (pw i a) t (P K₁) (E a)))
          (+-mono (≤-refl {pw i a * E a}) (*-mono t (≤-trans (*-mono (P K₁) (E≤1 a))
            (≤-trans (≤-reflexive (*-identityʳ _)) (P-mono (ℕ.m≤m+n K₁ K₂)))))))
      down : ∀ {a t} → a + t ≤ M → t ≤ 1# → hh i a ≤ hh i (a + t) + t * P (K₁ ℕ.+ K₂)
      down {a} {t} at t1 = ≤-trans (*-mono₂ (pw-mono i (≤-+ʳ {a} {t})) (E-lipD at t1))
        (≤-trans (≤-reflexive (solve 3 (λ q e t′ → q :* (e :+ t′) := q :* e :+ t′ :* q) refl (pw i (a + t)) (E (a + t)) t))
          (+-mono (≤-refl {pw i (a + t) * E (a + t)})
            (*-mono t (≤-trans (g at) (P-mono (ℕ.m≤n+m K₂ K₁))))))

    -- the certificate for G = h = hh (j+1) and k = (j+1) hh j, up to w² 2ᴷ
    cert : ∀ j → Σ ℕ (λ K →
      (∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) (a + w) + w * hh (suc j) a ≤ (hh (suc j) a + w * (natE (suc j) * hh j a)) + (w * w) * P K)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) a + w * (natE (suc j) * hh j a) ≤ (hh (suc j) (a + w) + w * hh (suc j) a) + (w * w) * P K))
    cert j = K , c1 , c2
      where
      C K₁ K₃ : ℕ
      C = proj₁ (up-bern m Mm (suc j))
      K₁ = proj₁ (pwB m Mm (suc j))
      K₃ = proj₁ (dpwB m Mm (suc j))

      ub : ∀ {a t} → a + t ≤ M → pw (suc j) (a + t) ≤ (pw (suc j) a + t * dpw (suc j) a) + (t * t) * P C
      ub = proj₂ (up-bern m Mm (suc j))

      pb : ∀ {a} → a ≤ M → pw (suc j) a ≤ P K₁
      pb = proj₂ (pwB m Mm (suc j))

      db : ∀ {a} → a ≤ M → dpw (suc j) a ≤ P K₃
      db = proj₂ (dpwB m Mm (suc j))

      K₂ : ℕ
      K₂ = suc (K₁ ℕ.+ C)
      K : ℕ
      K = K₂ ℕ.+ K₃

      AC : ∀ {a} → a ≤ M → pw (suc j) a + P C ≤ P K
      AC aM = ≤-trans (P-+ (pb aM) (≤-refl {P C})) (P-mono (ℕ.m≤m+n K₂ K₃))

      Dc : ∀ {a} → a ≤ M → dpw (suc j) a ≤ P K
      Dc aM = ≤-trans (db aM) (P-mono (ℕ.m≤n+m K₃ K₂))

      kk : ∀ a → natE (suc j) * hh j a ≈ dpw (suc j) a * E a
      kk a = trans (sym (*-assoc _ _ _)) (*-cong (sym (dpw-eq j a)) refl)

      c1 : ∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) (a + w) + w * hh (suc j) a ≤ (hh (suc j) a + w * (natE (suc j) * hh j a)) + (w * w) * P K
      c1 {a} {w} aw w1 = ≤-trans (+-mono (*-mono₂ (ub aw) (≤-reflexive (E-add aw w1))) ≤-refl)
        (≤-trans (lem-lo {pw (suc j) a} {dpw (suc j) a} {P C} {E a} {E w} {w} {P K}
                   (yt (E-b w1) (E-c w1)) (E≤1 w) (E≤1 a) (AC (≤-trans ≤-+ʳ aw)))
          (≤-reflexive (+-cong (+-cong refl (*-cong refl (sym (kk a)))) refl)))

      c2 : ∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) a + w * (natE (suc j) * hh j a) ≤ (hh (suc j) (a + w) + w * hh (suc j) a) + (w * w) * P K
      c2 {a} {w} aw w1 = ≤-trans (≤-reflexive (+-cong refl (*-cong refl (kk a))))
        (≤-trans (lem-hi {pw (suc j) a} {pw (suc j) (a + w)} {dpw (suc j) a} {E a} {E w} {w} {P K}
                   (E-c w1) (lo-bern (suc j)) (Dc (≤-trans ≤-+ʳ aw)) (E≤1 a))
          (≤-reflexive (+-cong (+-cong (*-cong refl (sym (E-add aw w1))) refl) refl)))

    lip-mono : ∀ {u K K′} → K ℕ.≤ K′ → LipOK u (P K) → LipOK u (P K′)
    lip-mono e (up , down) =
      (λ at t1 → ≤-trans (up at t1) (+-mono ≤-refl (*-mono _ (P-mono e))))
      , (λ at t1 → ≤-trans (down at t1) (+-mono ≤-refl (*-mono _ (P-mono e))))

    -- scaling by a constant N ≤ 2ᴸ
    scale-step : ∀ {N x y t K L} → N ≤ P L → x ≤ y + t * P K → N * x ≤ N * y + t * P (L ℕ.+ K)
    scale-step {N} {x} {y} {t} {K} {L} NL h = ≤-trans (*-mono N h)
      (≤-trans (≤-reflexive (solve 4 (λ n y′ t′ c → n :* (y′ :+ t′ :* c) := n :* y′ :+ t′ :* (n :* c)) refl N y t (P K)))
        (+-mono ≤-refl (*-mono t (P-* NL (≤-refl {P K})))))

    lip-scale : ∀ {u K L N} → N ≤ P L → LipOK u (P K) → LipOK (λ x → N * u x) (P (L ℕ.+ K))
    lip-scale NL (up , down) = (λ at t1 → scale-step NL (up at t1)) , (λ at t1 → scale-step NL (down at t1))

    -- all the data for `hh (j+1)` against `(j+1) hh j` with one constant 2ˢ, bounds by 2^(sIdx S)
    sIdx : ℕ → ℕ
    sIdx S = suc (S ℕ.+ suc (S ℕ.+ S))

    Pack : ℕ → ℕ → Set₁
    Pack j S = (P S + (P S + P S) ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → hh (suc j) x + P S ≤ P (sIdx S))
      × (∀ {x} → x ≤ M → natE (suc j) * hh j x + P S ≤ P (sIdx S))
      × LipOK (hh (suc j)) (P S) × LipOK (λ x → natE (suc j) * hh j x) (P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          hh (suc j) (a + w) + w * hh (suc j) a ≤ (hh (suc j) a + w * (natE (suc j) * hh j a)) + (w * w) * P S)
      × (∀ {a w} → a + w ≤ M → w ≤ 1# →
          hh (suc j) a + w * (natE (suc j) * hh j a) ≤ (hh (suc j) (a + w) + w * hh (suc j) a) + (w * w) * P S)
      × (∀ {x} → x ≤ M → hh (suc j) x ≤ P (sIdx S))

    pack : ∀ j → Σ ℕ (Pack j)
    pack j = S , c3 , hb , kb , lip-mono i2 (proj₂ (hh-lip (suc j))) , lip-mono i1 kl , cr1 , cr2 , gb
      where
      K₁ K₂ K₃ K₄ K₅ : ℕ
      K₁ = proj₁ (hh-lip (suc j))
      K₂ = proj₁ (hh-lip j)
      K₃ = proj₁ (cert j)
      K₄ = proj₁ (pwB m Mm (suc j))
      K₅ = proj₁ (pwB m Mm j)
      S : ℕ
      S = (suc j ℕ.+ K₂) ℕ.+ (K₁ ℕ.+ (K₃ ℕ.+ (K₄ ℕ.+ (suc j ℕ.+ K₅))))

      i1 : (suc j ℕ.+ K₂) ℕ.≤ S
      i1 = ℕ.m≤m+n _ _
      i2 : K₁ ℕ.≤ S
      i2 = ℕ.≤-trans (ℕ.m≤m+n K₁ _) (ℕ.m≤n+m _ (suc j ℕ.+ K₂))
      i3 : K₃ ℕ.≤ S
      i3 = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n K₃ _) (ℕ.m≤n+m _ K₁)) (ℕ.m≤n+m _ (suc j ℕ.+ K₂))
      i4 : K₄ ℕ.≤ S
      i4 = ℕ.≤-trans (ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n K₄ _) (ℕ.m≤n+m _ K₃)) (ℕ.m≤n+m _ K₁)) (ℕ.m≤n+m _ (suc j ℕ.+ K₂))
      i5 : (suc j ℕ.+ K₅) ℕ.≤ S
      i5 = ℕ.≤-trans (ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤n+m _ K₄) (ℕ.m≤n+m _ K₃)) (ℕ.m≤n+m _ K₁)) (ℕ.m≤n+m _ (suc j ℕ.+ K₂))

      kl : LipOK (λ x → natE (suc j) * hh j x) (P (suc j ℕ.+ K₂))
      kl = lip-scale (natE≤P (suc j)) (proj₂ (hh-lip j))

      vh : ∀ {x} → x ≤ M → hh (suc j) x ≤ P S
      vh {x} xM = ≤-trans (*-mono (pw (suc j) x) (E≤1 x)) (≤-trans (≤-reflexive (*-identityʳ _))
        (≤-trans (proj₂ (pwB m Mm (suc j)) xM) (P-mono i4)))

      vk : ∀ {x} → x ≤ M → natE (suc j) * hh j x ≤ P S
      vk {x} xM = ≤-trans (P-* (natE≤P (suc j)) (≤-trans (*-mono (pw j x) (E≤1 x)) (≤-trans (≤-reflexive (*-identityʳ _))
        (proj₂ (pwB m Mm j) xM)))) (P-mono i5)

      sl : suc (S ℕ.+ S) ℕ.≤ sIdx S
      sl = ℕ.s≤s (ℕ.+-monoʳ-≤ S (ℕ.≤-trans (ℕ.m≤m+n S S) (ℕ.n≤1+n (S ℕ.+ S))))

      c3 : P S + (P S + P S) ≤ P (sIdx S)
      c3 = P-+ {i = S} {j = suc (S ℕ.+ S)} ≤-refl (P-+ {i = S} {j = S} ≤-refl ≤-refl)

      hb : ∀ {x} → x ≤ M → hh (suc j) x + P S ≤ P (sIdx S)
      hb xM = ≤-trans (P-+ {i = S} {j = S} (vh xM) ≤-refl) (P-mono sl)

      kb : ∀ {x} → x ≤ M → natE (suc j) * hh j x + P S ≤ P (sIdx S)
      kb xM = ≤-trans (P-+ {i = S} {j = S} (vk xM) ≤-refl) (P-mono sl)

      gb : ∀ {x} → x ≤ M → hh (suc j) x ≤ P (sIdx S)
      gb xM = ≤-trans (vh xM) (P-mono (ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n S S) (ℕ.n≤1+n _)) sl))

      cr1 : ∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) (a + w) + w * hh (suc j) a ≤ (hh (suc j) a + w * (natE (suc j) * hh j a)) + (w * w) * P S
      cr1 aw w1 = ≤-trans (proj₁ (proj₂ (cert j)) aw w1) (+-mono ≤-refl (*-mono (_ * _) (P-mono i3)))

      cr2 : ∀ {a w} → a + w ≤ M → w ≤ 1# →
        hh (suc j) a + w * (natE (suc j) * hh j a) ≤ (hh (suc j) (a + w) + w * hh (suc j) a) + (w * w) * P S
      cr2 aw w1 = ≤-trans (proj₂ (proj₂ (cert j)) aw w1) (+-mono ≤-refl (*-mono (_ * _) (P-mono i3)))

  ----------------------------------------------------------------------------
  -- natural numbers and powers of ½ (used for the tail `xʲ e^{−x} → 0`)

  natE-+ : ∀ a b → natE (a ℕ.+ b) ≈ natE a + natE b
  natE-+ zero b = sym (+-identityˡ (natE b))
  natE-+ (suc a) b = trans (+-cong (natE-+ a b) refl) (solve 3 (λ x y o → (x :+ y) :+ o := (x :+ o) :+ y) refl (natE a) (natE b) 1#)

  natE-* : ∀ a b → natE (a ℕ.* b) ≈ natE a * natE b
  natE-* zero b = solve 1 (λ x → con 0 := con 0 :* x) refl (natE b)
  natE-* (suc a) b = trans (natE-+ b (a ℕ.* b)) (trans (+-cong refl (natE-* a b))
    (solve 2 (λ x y → x :+ y :* x := (y :+ con 1) :* x) refl (natE b) (natE a)))

  -- 2ᵏ as a natural number
  pnat : ℕ → ℕ
  pnat zero = 1
  pnat (suc k) = pnat k ℕ.+ pnat k

  natE-pnat : ∀ k → natE (pnat k) ≈ P k
  natE-pnat zero = +-identityˡ 1#
  natE-pnat (suc k) = trans (natE-+ (pnat k) (pnat k)) (+-cong (natE-pnat k) (natE-pnat k))

  pw-mul : ∀ e x y → pw e (x * y) ≈ pw e x * pw e y
  pw-mul zero x y = sym (*-identityˡ 1#)
  pw-mul (suc e) x y = trans (*-cong refl (pw-mul e x y))
    (solve 4 (λ x′ y′ p q → (x′ :* y′) :* (p :* q) := (x′ :* p) :* (y′ :* q)) refl x y (pw e x) (pw e y))

  pw-one : ∀ e → pw e 1# ≈ 1#
  pw-one zero = refl
  pw-one (suc e) = trans (*-identityˡ _) (pw-one e)

  Phz : ∀ z m → P z * hp (z ℕ.+ m) ≈ hp m
  Phz zero m = *-identityˡ _
  Phz (suc z) m = trans (solve 3 (λ p h q → (p :+ p) :* (h :* q) := p :* ((h :+ h) :* q)) refl (P z) half (hp (z ℕ.+ m)))
    (trans (*-cong refl (trans (*-cong half+half refl) (*-identityˡ _))) (Phz z m))
