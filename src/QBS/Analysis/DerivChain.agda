{-# OPTIONS --safe --without-K #-}

-- A certificate calculus for the tail FTC (part 4: the chain rule for the exponential), over an abstract Archimedean
-- ω-semiring.
--
-- From `D M c u h k` (u′ = k − h) with u ≥ 0 bounded by c, the function G = E ∘ u, E = e^{−x}, has
--     h_G = E(u) · k,    k_G = E(u) · h        (so G′ = k_G − h_G = E(u) (h − k) = −E(u) u′).
-- The exponential enters through its facts at arguments bounded by B, a bound with c + (c + c) ≤ B (the increments of u
-- and the first-order terms are all ≤ c, so every sum below is ≤ c + (c + c)):
--     E (x + y) = E x E y,     E t + t E t ≤ 1,     1 ≤ E t + t           (x, y, x + y, t ≤ B),
-- exactly the form `Analysis/GaussExp` instantiates.  Write x = u a, y = u (a + w), P = w h(a), Q = w k(a), e = w² c;
-- the hypotheses of `D` read x + Q ≤ y + P + e (`Ct2`) and y + P ≤ x + Q + e (`Ct1`).  Two uses of the addition law and
-- of the first-order facts then close both certificates with additive arguments only (signed increments never appear):
--   * Ct1 (an upper bound for E y):  `Ct2` and anti-monotonicity give E y E(P + e) ≤ E x E Q; from 1 ≤ E(P+e) + (P+e),
--     E Q + Q ≤ 1 + Q² and the Lipschitz bound E y ≤ E x + w (c + c) (`Elip`, from `Gdn`) one gets
--       E y + E x Q ≤ E x + E x P + R,    R = E x Q² + E x e + w (c + c) (P + e)  ≤  w² (c² + c + (c + c)²);
--   * Ct2 (a lower bound for E y):  `Ct1` gives E x E(Q + e) ≤ E y E P; multiplying by 1 + P and using E P + P E P ≤ 1
--     gives E x E(Q+e) (1 + P) ≤ E y, and 1 ≤ E(Q+e) + (Q+e) turns this into
--       E x + E x P ≤ E y + E x Q + E x e + E x P (Q + e),    the error ≤ w² (c + c (c + c)).
-- Both errors are O(w²) with constants depending on c alone.  The Lipschitz bounds of E(u) k and E(u) h come from the
-- product Lipschitz lemma `lipP` of `Analysis/DerivProd` (E ∘ u is Lipschitz with constant c + c by `Elip`).  The wrapper
-- `DFexp` (module `Chain`) takes the exponential facts at every bound P s and a `Deriv` for u.
module QBS.Analysis.DerivChain where

import Level as L
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Analysis.DerivProd using (module AlgDP)

module AlgDX (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgT A R using (P)
  open AlgP A R using (*-monoʳ; *-mono₂; P-+; yt)
  open AlgD A R
  open AlgDP A R using (L₁; lipP)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the constants

  C1 C2 : ∣A∣ → ∣A∣
  C1 c = ((c * c) + c) + ((c + c) * (c + c))
  C2 c = c + (c * (c + c))

  Cx : ∣A∣ → ∣A∣
  Cx c = (c + L₁ c) + (C1 c + C2 c)

  Fin-Cx : ∀ {c} → Fin c → Fin (Cx c)
  Fin-Cx f = Fin-+ (Fin-+ f fL) (Fin-+ fC1 fC2)
    where
    fd = Fin-+ f f
    fcc = Fin-* f f
    fcd = Fin-* f fd
    fL = Fin-+ fcd (Fin-+ fcc fcd)
    fC1 = Fin-+ (Fin-+ fcc f) (Fin-* fd fd)
    fC2 = Fin-+ f fcd

  c≤Cx : ∀ {c} → c ≤ Cx c
  c≤Cx {c} = ≤-trans (≤-+ʳ {c} {L₁ c}) (≤-+ʳ {c + L₁ c} {C1 c + C2 c})

  L≤Cx : ∀ {c} → L₁ c ≤ Cx c
  L≤Cx {c} = ≤-trans (≤-+ˡ {c} {L₁ c}) (≤-+ʳ {c + L₁ c} {C1 c + C2 c})

  C1≤Cx : ∀ {c} → C1 c ≤ Cx c
  C1≤Cx {c} = ≤-trans (≤-+ʳ {C1 c} {C2 c}) (≤-+ˡ {c + L₁ c} {C1 c + C2 c})

  C2≤Cx : ∀ {c} → C2 c ≤ Cx c
  C2≤Cx {c} = ≤-trans (≤-+ˡ {C1 c} {C2 c}) (≤-+ˡ {c + L₁ c} {C1 c + C2 c})

  ----------------------------------------------------------------------------
  -- the algebra of the upper certificate (Ct1 of E ∘ u)

  T1e1 : ∀ f EQ q w l p e → (f * EQ + (f + w * l) * (p + e)) + f * q ≈ f * (EQ + q) + (f + w * l) * (p + e)
  T1e1 f EQ q w l p e = solve 7 (λ f′ EQ′ q′ w′ l′ p′ e′ → (f′ :* EQ′ :+ (f′ :+ w′ :* l′) :* (p′ :+ e′)) :+ f′ :* q′
    := f′ :* (EQ′ :+ q′) :+ (f′ :+ w′ :* l′) :* (p′ :+ e′)) refl f EQ q w l p e

  T1e2 : ∀ f q w l p e → f * (1# + q * q) + (f + w * l) * (p + e) ≈ (f + f * p) + ((f * (q * q) + f * e) + (w * l) * (p + e))
  T1e2 f q w l p e = solve 6 (λ f′ q′ w′ l′ p′ e′ → f′ :* (con 1 :+ q′ :* q′) :+ (f′ :+ w′ :* l′) :* (p′ :+ e′)
    := (f′ :+ f′ :* p′) :+ ((f′ :* (q′ :* q′) :+ f′ :* e′) :+ (w′ :* l′) :* (p′ :+ e′))) refl f q w l p e

  T1a : ∀ {f g EQ Ee p q e w l} → g * Ee ≤ f * EQ → 1# ≤ Ee + (p + e) → EQ + q ≤ 1# + q * q → g ≤ f + w * l →
    g + f * q ≤ (f + f * p) + ((f * (q * q) + f * e) + (w * l) * (p + e))
  T1a {f} {g} {EQ} {Ee} {p} {q} {e} {w} {l} s1 s2 s3 s4 =
    ≤-trans (+-mono (≤-trans g≤ (+-mono s1 (*-monoʳ (p + e) s4))) (≤-refl {f * q}))
      (≤-trans (≤-reflexive (T1e1 f EQ q w l p e))
        (≤-trans (+-mono (*-mono f s3) (≤-refl {(f + w * l) * (p + e)})) (≤-reflexive (T1e2 f q w l p e))))
    where
    g≤ : g ≤ g * Ee + g * (p + e)
    g≤ = ≤-trans (≤-reflexive (sym (*-identityʳ g))) (≤-trans (*-mono g s2) (≤-reflexive (distribˡ g Ee (p + e))))

  -- the error of the upper certificate, with e = w² c
  T1eq : ∀ w c → ((w * w) * (c * c) + (w * w) * c) + (w * w) * ((c + c) * (c + c)) ≈ (w * w) * C1 c
  T1eq w c = solve 2 (λ w′ c′ → ((w′ :* w′) :* (c′ :* c′) :+ (w′ :* w′) :* c′) :+ (w′ :* w′) :* ((c′ :+ c′) :* (c′ :+ c′))
    := (w′ :* w′) :* (((c′ :* c′) :+ c′) :+ ((c′ :+ c′) :* (c′ :+ c′)))) refl w c

  T1b : ∀ {f p q w c} → w ≤ 1# → f ≤ 1# → p ≤ w * c → q ≤ w * c →
    (f * (q * q) + f * ((w * w) * c)) + (w * (c + c)) * (p + (w * w) * c) ≤ (w * w) * C1 c
  T1b {f} {p} {q} {w} {c} w1 f1 hp hq = ≤-trans (+-mono (+-mono a b) cc) (≤-reflexive (T1eq w c))
    where
    fle : ∀ z → f * z ≤ z
    fle z = ≤-trans (*-monoʳ z f1) (≤-reflexive (*-identityˡ z))
    a : f * (q * q) ≤ (w * w) * (c * c)
    a = ≤-trans (fle (q * q)) (≤-trans (*-mono₂ hq hq)
      (≤-reflexive (solve 2 (λ w′ c′ → (w′ :* c′) :* (w′ :* c′) := (w′ :* w′) :* (c′ :* c′)) refl w c)))
    b : f * ((w * w) * c) ≤ (w * w) * c
    b = fle _
    pe : p + (w * w) * c ≤ w * (c + c)
    pe = ≤-trans (+-mono hp (www w1 c)) (≤-reflexive (solve 2 (λ w′ c′ → w′ :* c′ :+ w′ :* c′ := w′ :* (c′ :+ c′)) refl w c))
    cc : (w * (c + c)) * (p + (w * w) * c) ≤ (w * w) * ((c + c) * (c + c))
    cc = ≤-trans (*-mono (w * (c + c)) pe)
      (≤-reflexive (solve 2 (λ w′ c′ → (w′ :* (c′ :+ c′)) :* (w′ :* (c′ :+ c′)) := (w′ :* w′) :* ((c′ :+ c′) :* (c′ :+ c′))) refl w c))

  ----------------------------------------------------------------------------
  -- the algebra of the lower certificate (Ct2 of E ∘ u)

  T2e : ∀ f F p q e → f * (F + (q + e)) + f * (p * (F + (q + e))) ≈ ((f * F) * (1# + p) + f * q) + (f * e + f * (p * (q + e)))
  T2e f F p q e = solve 5 (λ f′ F′ p′ q′ e′ → f′ :* (F′ :+ (q′ :+ e′)) :+ f′ :* (p′ :* (F′ :+ (q′ :+ e′)))
    := ((f′ :* F′) :* (con 1 :+ p′) :+ f′ :* q′) :+ (f′ :* e′ :+ f′ :* (p′ :* (q′ :+ e′)))) refl f F p q e

  T2a : ∀ {f g F EP p q e} → f * F ≤ g * EP → 1# ≤ F + (q + e) → EP + p * EP ≤ 1# →
    f + f * p ≤ (g + f * q) + (f * e + f * (p * (q + e)))
  T2a {f} {g} {F} {EP} {p} {q} {e} s1 s2 s3 =
    ≤-trans (+-mono f≤ fp≤) (≤-trans (≤-reflexive (T2e f F p q e))
      (+-mono (+-mono gge (≤-refl {f * q})) (≤-refl {f * e + f * (p * (q + e))})))
    where
    gge : (f * F) * (1# + p) ≤ g
    gge = ≤-trans (*-monoʳ (1# + p) s1) (≤-trans (≤-reflexive
      (solve 4 (λ g′ EP′ p′ f′ → (g′ :* EP′) :* (con 1 :+ p′) := g′ :* (EP′ :+ p′ :* EP′)) refl g EP p f))
      (≤-trans (*-mono g s3) (≤-reflexive (*-identityʳ g))))
    f≤ : f ≤ f * (F + (q + e))
    f≤ = ≤-trans (≤-reflexive (sym (*-identityʳ f))) (*-mono f s2)
    fp≤ : f * p ≤ f * (p * (F + (q + e)))
    fp≤ = ≤-trans (≤-reflexive (solve 2 (λ f′ p′ → f′ :* p′ := f′ :* (p′ :* con 1)) refl f p)) (*-mono f (*-mono p s2))

  T2b : ∀ {f p q w c} → w ≤ 1# → f ≤ 1# → p ≤ w * c → q ≤ w * c →
    f * ((w * w) * c) + f * (p * (q + (w * w) * c)) ≤ (w * w) * C2 c
  T2b {f} {p} {q} {w} {c} w1 f1 hp hq = ≤-trans (+-mono b (≤-trans (fle _) cc)) (≤-reflexive eq)
    where
    fle : ∀ z → f * z ≤ z
    fle z = ≤-trans (*-monoʳ z f1) (≤-reflexive (*-identityˡ z))
    b : f * ((w * w) * c) ≤ (w * w) * c
    b = fle _
    qe : q + (w * w) * c ≤ w * (c + c)
    qe = ≤-trans (+-mono hq (www w1 c)) (≤-reflexive (solve 2 (λ w′ c′ → w′ :* c′ :+ w′ :* c′ := w′ :* (c′ :+ c′)) refl w c))
    cc : p * (q + (w * w) * c) ≤ (w * w) * (c * (c + c))
    cc = ≤-trans (*-mono₂ hp qe)
      (≤-reflexive (solve 2 (λ w′ c′ → (w′ :* c′) :* (w′ :* (c′ :+ c′)) := (w′ :* w′) :* (c′ :* (c′ :+ c′))) refl w c))
    eq : (w * w) * c + (w * w) * (c * (c + c)) ≈ (w * w) * C2 c
    eq = solve 2 (λ w′ c′ → (w′ :* w′) :* c′ :+ (w′ :* w′) :* (c′ :* (c′ :+ c′)) := (w′ :* w′) :* (c′ :+ c′ :* (c′ :+ c′))) refl w c

  ----------------------------------------------------------------------------
  -- the exponential at a bound B

  module Core (E : ∣A∣ → ∣A∣) (B : ∣A∣) (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ {x y} → x ≤ B → y ≤ B → x + y ≤ B → E (x + y) ≈ E x * E y)
    (E-b : ∀ {t} → t ≤ B → E t + t * E t ≤ 1#) (E-c : ∀ {t} → t ≤ B → 1# ≤ E t + t) where

    E-cong : ∀ {x y} → x ≈ y → E x ≈ E y
    E-cong e = ≤-antisym (E-anti (≤-reflexive (sym e))) (E-anti (≤-reflexive e))

    -- q ≤ p + t gives E p ≤ E q + t
    Elip : ∀ {p q t} → q ≤ p + t → p ≤ B → t ≤ B → p + t ≤ B → E p ≤ E q + t
    Elip {p} {q} {t} qpt pB tB ptB = ≤-trans (≤-reflexive (sym (*-identityʳ (E p)))) (≤-trans (*-mono (E p) (E-c tB))
      (≤-trans (≤-reflexive (solve 3 (λ x y z → x :* (y :+ z) := x :* y :+ z :* x) refl (E p) (E t) t))
        (+-mono (≤-trans (≤-reflexive (sym (E-add pB tB ptB))) (E-anti qpt))
          (≤-trans (*-mono t (E≤1 p)) (≤-reflexive (*-identityʳ t))))))

    module _ {M c : ∣A∣} {u h k : ∣A∣ → ∣A∣} (d : D M c u h k) (c1 : 1# ≤ c) (cB : c + (c + c) ≤ B) where
      private
        G H K : ∣A∣ → ∣A∣
        G x = E (u x)
        H x = k x * E (u x)
        K x = h x * E (u x)

        aM : ∀ {a w} → a + w ≤ M → a ≤ M
        aM aw = ≤-trans ≤-+ʳ aw

        -- sizes: s ≤ c, s ≤ c + c, s ≤ c + (c + c) give s ≤ B
        b1 : ∀ {s} → s ≤ c → s ≤ B
        b1 sc = ≤-trans (≤-trans sc (≤-+ʳ {c} {c + c})) cB

        b2 : ∀ {s} → s ≤ c + c → s ≤ B
        b2 sc = ≤-trans (≤-trans sc (+-mono (≤-refl {c}) (≤-+ʳ {c} {c}))) cB

        b3 : ∀ {s} → s ≤ c + (c + c) → s ≤ B
        b3 sc = ≤-trans sc cB

        c2 : ∀ {z} → z ≤ c → z + z ≤ c + c
        c2 zc = +-mono zc zc

        -- w z ≤ z ≤ c
        wc : ∀ {w z} → w ≤ 1# → z ≤ c → w * z ≤ c
        wc {w} {z} w1 zc = ≤-trans (wle w1 z) zc

        ec : ∀ {w} → w ≤ 1# → (w * w) * c ≤ c
        ec w1 = wle (ww≤1 w1) c

        wL : ∀ {w} → w ≤ 1# → w * (c + c) ≤ c + c
        wL w1 = wle w1 (c + c)

        E≤c : ∀ x → E x ≤ c
        E≤c x = ≤-trans (E≤1 x) c1

        -- the Lipschitz bounds of E ∘ u
        Gl-up : ∀ {a w} → a + w ≤ M → w ≤ 1# → E (u (a + w)) ≤ E (u a) + w * (c + c)
        Gl-up {a} {w} aw w1 = Elip (Gdn d aw w1) (b1 (D-bG d aw)) (b2 (wL w1)) (b3 (+-mono (D-bG d aw) (wL w1)))

        Gl-dn : ∀ {a w} → a + w ≤ M → w ≤ 1# → E (u a) ≤ E (u (a + w)) + w * (c + c)
        Gl-dn {a} {w} aw w1 = Elip (Gup d aw w1) (b1 (D-bG d (aM aw))) (b2 (wL w1)) (b3 (+-mono (D-bG d (aM aw)) (wL w1)))

        lipX : ∀ {m : ∣A∣ → ∣A∣} → Bnd M c m → LpU M c m → LpD M c m →
          LpU M (L₁ c) (λ x → m x * E (u x)) × LpD M (L₁ c) (λ x → m x * E (u x))
        lipX {m} bm lu ld = (λ {a} {w} aw w1 → lipP {m (a + w)} {m a} {E (u (a + w))} {E (u a)} {w} {c} w1
                                (lu aw w1) (Gl-up aw w1) (bm (aM aw)) (E≤c _)) ,
                            (λ {a} {w} aw w1 → lipP {m a} {m (a + w)} {E (u a)} {E (u (a + w))} {w} {c} w1
                                (ld aw w1) (Gl-dn aw w1) (bm aw) (E≤c _))

        bX : ∀ {m : ∣A∣ → ∣A∣} → Bnd M c m → Bnd M c (λ x → m x * E (u x))
        bX bm xM = ≤-trans (*-mono _ (E≤1 _)) (≤-trans (≤-reflexive (*-identityʳ _)) (bm xM))

        cX : ∀ {m : ∣A∣ → ∣A∣} → Cg m → Cg (λ x → m x * E (u x))
        cX cm e = *-cong (cm e) (E-cong (D-cG d e))

        -- sizes at a point pair
        module _ {a w : ∣A∣} (aw : a + w ≤ M) (w1 : w ≤ 1#) where
          x y p q ee : ∣A∣
          x = u a
          y = u (a + w)
          p = w * h a
          q = w * k a
          ee = (w * w) * c

          hx : x ≤ c
          hx = D-bG d (aM aw)
          hy : y ≤ c
          hy = D-bG d aw
          hp : p ≤ c
          hp = wc w1 (D-bh d (aM aw))
          hq : q ≤ c
          hq = wc w1 (D-bk d (aM aw))
          pe : p + ee ≤ c + c
          pe = +-mono hp (ec w1)
          qe : q + ee ≤ c + c
          qe = +-mono hq (ec w1)

          -- upper certificate
          u1 : E y * E (p + ee) ≤ E x * E q
          u1 = ≤-trans (≤-reflexive (sym (E-add (b1 hy) (b2 pe) (b3 (+-mono hy pe)))))
            (≤-trans (E-anti (≤-trans (D-c2 d aw w1) (≤-reflexive (+-assoc y p ee))))
              (≤-reflexive (E-add (b1 hx) (b1 hq) (b2 (+-mono hx hq)))))

          T1 : E y + E x * q ≤ (E x + E x * p) + (w * w) * C1 c
          T1 = ≤-trans (T1a {E x} {E y} {E q} {E (p + ee)} {p} {q} {ee} {w} {c + c} u1 (E-c (b2 pe))
                 (yt (E-b (b1 hq)) (E-c (b1 hq))) (Gl-up aw w1))
            (+-mono ≤-refl (T1b {E x} {p} {q} {w} {c} w1 (E≤1 _) (*-mono w (D-bh d (aM aw))) (*-mono w (D-bk d (aM aw)))))

          -- lower certificate
          l1 : E x * E (q + ee) ≤ E y * E p
          l1 = ≤-trans (≤-reflexive (sym (E-add (b1 hx) (b2 qe) (b3 (+-mono hx qe)))))
            (≤-trans (E-anti (≤-trans (D-c1 d aw w1) (≤-reflexive (+-assoc x q ee))))
              (≤-reflexive (E-add (b1 hy) (b1 hp) (b2 (+-mono hy hp)))))

          T2 : E x + E x * p ≤ (E y + E x * q) + (w * w) * C2 c
          T2 = ≤-trans (T2a {E x} {E y} {E (q + ee)} {E p} {p} {q} {ee} l1 (E-c (b2 qe)) (E-b (b1 hp)))
            (+-mono ≤-refl (T2b {E x} {p} {q} {w} {c} w1 (E≤1 _) (*-mono w (D-bh d (aM aw))) (*-mono w (D-bk d (aM aw)))))

        sw : ∀ f w z → f * (w * z) ≈ w * (z * f)
        sw f w z = solve 3 (λ f′ w′ z′ → f′ :* (w′ :* z′) := w′ :* (z′ :* f′)) refl f w z

        ct1′ : Ct1 M (C1 c) G H K
        ct1′ {a} {w} aw w1 = ≤-resp (+-cong refl (sw (E (u a)) w (k a))) (+-cong (+-cong refl (sw (E (u a)) w (h a))) refl) (T1 aw w1)

        ct2′ : Ct2 M (C2 c) G H K
        ct2′ {a} {w} aw w1 = ≤-resp (+-cong refl (sw (E (u a)) w (h a))) (+-cong (+-cong refl (sw (E (u a)) w (k a))) refl) (T2 aw w1)

      DX : D M (Cx c) (λ x → E (u x)) (λ x → k x * E (u x)) (λ x → h x * E (u x))
      DX = mkD (λ e → E-cong (D-cG d e)) (cX (D-ck d)) (cX (D-ch d))
        (λ xM → ≤-trans (E≤c _) c≤Cx)
        (Bnd-mono {M} {c} {Cx c} c≤Cx (bX (D-bk d))) (Bnd-mono {M} {c} {Cx c} c≤Cx (bX (D-bh d)))
        (LpU-mono {M} {L₁ c} {Cx c} L≤Cx (proj₁ (lipX (D-bk d) (D-kU d) (D-kD d))))
        (LpD-mono {M} {L₁ c} {Cx c} L≤Cx (proj₂ (lipX (D-bk d) (D-kU d) (D-kD d))))
        (LpU-mono {M} {L₁ c} {Cx c} L≤Cx (proj₁ (lipX (D-bh d) (D-hU d) (D-hD d))))
        (LpD-mono {M} {L₁ c} {Cx c} L≤Cx (proj₂ (lipX (D-bh d) (D-hU d) (D-hD d))))
        (Ct1-mono {M} {C1 c} {Cx c} C1≤Cx ct1′) (Ct2-mono {M} {C2 c} {Cx c} C2≤Cx ct2′)

  ----------------------------------------------------------------------------
  -- the rule on the wrapper `Deriv`: the exponential facts at every bound P s

  module Chain (E : ∣A∣ → ∣A∣) (E≤1 : ∀ x → E x ≤ 1#) (E-anti : ∀ {x y} → x ≤ y → E y ≤ E x)
    (E-add : ∀ s {x y} → x ≤ P s → y ≤ P s → x + y ≤ P s → E (x + y) ≈ E x * E y)
    (E-b : ∀ s {t} → t ≤ P s → E t + t * E t ≤ 1#) (E-c : ∀ s {t} → t ≤ P s → 1# ≤ E t + t) where

    DFexp : ∀ {M u h k} → Deriv M u h k →
      Deriv M (λ x → E (u x)) (λ x → E (u x) * k x) (λ x → E (u x) * h x)
    DFexp {M} {u} {h} {k} (c , fc , d) = Cx c₁ , Fin-Cx f₁ , D-resp {M} {Cx c₁} {λ x → E (u x)} {λ x → E (u x)}
      {λ x → k x * E (u x)} {λ x → E (u x) * k x} {λ x → h x * E (u x)} {λ x → E (u x) * h x}
      (λ _ → refl) (λ x → *-comm _ _) (λ x → *-comm _ _) (X.DX d₁ (≤-+ˡ {c} {1#}) cB)
      where
      c₁ : ∣A∣
      c₁ = c + 1#
      f₁ : Fin c₁
      f₁ = Fin-+ fc Fin-1
      d₁ : D M c₁ u h k
      d₁ = Dmono {M} {c} {c₁} (≤-+ʳ {c} {1#}) d
      s : ℕ
      s = suc (proj₁ f₁ ℕ.+ suc (proj₁ f₁ ℕ.+ proj₁ f₁))
      cB : c₁ + (c₁ + c₁) ≤ P s
      cB = P-+ {i = proj₁ f₁} {j = suc (proj₁ f₁ ℕ.+ proj₁ f₁)} (proj₂ f₁) (P-+ {i = proj₁ f₁} {j = proj₁ f₁} (proj₂ f₁) (proj₂ f₁))
      module X = Core E (P s) E≤1 E-anti (E-add s) (E-b s) (E-c s)
