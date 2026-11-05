{-# OPTIONS --safe --without-K #-}

-- A certificate calculus for the tail FTC (part 1: the notion, and the linear closure rules).
--
-- Lower reals have no derivative, so the hypotheses of the Lipschitz tail FTC (`Continuous/TailFTCLip`) were proved by hand
-- for every integrand (`Analysis/PolyExpCert`, `Analysis/GaussCert`, ...).  Here they are packaged once, as a notion that
-- composes.  Over an abstract Archimedean ω-semiring, for functions G, h, k on the interval [0, M] and one constant c,
--     D M c G h k
-- says that G′ = k − h (a signed derivative: the formal difference of two non-negative parts), in the form
--   * G, h, k respect ≈;  G x, h x, k x ≤ c for x ≤ M  (`Bnd`);
--   * h and k are Lipschitz with constant c, both ways, for every point pair a, a + w with a + w ≤ M, w ≤ 1 (`LpU`, `LpD`);
--   * the two-sided certificate up to w² c at the same point pairs (`Ct1`, `Ct2`):
--       G (a + w) + w h(a) ≤ G a + w k(a) + w² c    and    G a + w k(a) ≤ G (a + w) + w h(a) + w² c.
-- Why this shape.  (1) It is exactly what `LipJ` needs: its dyadic pieces [a, a + ½ⁿ] and sample points a + ½ⁿ x are
-- point pairs (a, w) with w ≤ 1 (`Continuous/DerivBridge`), so the bridge is bookkeeping and the closure proofs are
-- pointwise algebra (ring solver, in this abstract setting only).  (2) One constant c bounds everything, so rules need no
-- bookkeeping of several constants; a rule returns a new c as an explicit polynomial and `Dmono` weakens.  (3) The
-- Lipschitz property of G is not a field: it follows from the certificate and the bounds (`Gup`, `Gdn`, constant c + c),
-- which is what the product rule needs for its cross terms.  (4) Finiteness (c ≤ 2ˢ, needed by `LipJ`) is kept out of
-- the algebra and carried by the wrapper `Deriv M G h k = Σ c (Fin c × D M c G h k)`, closed under the rules by
-- `Fin-+` and `Fin-*`; users compose `Deriv` values and never see constants.
--
-- Rules proved here: constants, the identity, sums, scalar multiples, `D-resp` (changing G, h, k pointwise up to ≈),
-- translation x ↦ t + x (`Dshift`), and composition with x ↦ l x for l ≤ 1 (`Daff`, which generalises `Analysis/ExpRate`;
-- l ≤ 1 so that the width l w stays ≤ 1).  The product rule is in `Analysis/DerivProd`, the exponential in
-- `Analysis/DerivExp`.  A chain rule with a monotone inner function does not fall out: it needs the exponential's
-- addition law on signed increments, not only the certificate.
module QBS.Analysis.Deriv where

import Level as L
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; _,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.PolyExpCert using (module AlgP)

module AlgD (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgT A R using (P)
  open AlgP A R using (P-+; P-*; *-monoʳ; *-mono₂)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the notion

  Cg : (∣A∣ → ∣A∣) → Set₁
  Cg u = ∀ {x y} → x ≈ y → u x ≈ u y

  Bnd : ∣A∣ → ∣A∣ → (∣A∣ → ∣A∣) → Set₁
  Bnd M c u = ∀ {x} → x ≤ M → u x ≤ c

  LpU LpD : ∣A∣ → ∣A∣ → (∣A∣ → ∣A∣) → Set₁
  LpU M c u = ∀ {a w} → a + w ≤ M → w ≤ 1# → u (a + w) ≤ u a + w * c
  LpD M c u = ∀ {a w} → a + w ≤ M → w ≤ 1# → u a ≤ u (a + w) + w * c

  Ct1 Ct2 : ∣A∣ → ∣A∣ → (∣A∣ → ∣A∣) → (∣A∣ → ∣A∣) → (∣A∣ → ∣A∣) → Set₁
  Ct1 M c G h k = ∀ {a w} → a + w ≤ M → w ≤ 1# → G (a + w) + w * h a ≤ (G a + w * k a) + (w * w) * c
  Ct2 M c G h k = ∀ {a w} → a + w ≤ M → w ≤ 1# → G a + w * k a ≤ (G (a + w) + w * h a) + (w * w) * c

  data D (M c : ∣A∣) (G h k : ∣A∣ → ∣A∣) : Set₁ where
    mkD : Cg G → Cg h → Cg k → Bnd M c G → Bnd M c h → Bnd M c k →
      LpU M c h → LpD M c h → LpU M c k → LpD M c k → Ct1 M c G h k → Ct2 M c G h k → D M c G h k

  module _ {M c : ∣A∣} {G h k : ∣A∣ → ∣A∣} where
    D-cG : D M c G h k → Cg G
    D-cG (mkD f _ _ _ _ _ _ _ _ _ _ _) = f
    D-ch : D M c G h k → Cg h
    D-ch (mkD _ f _ _ _ _ _ _ _ _ _ _) = f
    D-ck : D M c G h k → Cg k
    D-ck (mkD _ _ f _ _ _ _ _ _ _ _ _) = f
    D-bG : D M c G h k → Bnd M c G
    D-bG (mkD _ _ _ f _ _ _ _ _ _ _ _) = f
    D-bh : D M c G h k → Bnd M c h
    D-bh (mkD _ _ _ _ f _ _ _ _ _ _ _) = f
    D-bk : D M c G h k → Bnd M c k
    D-bk (mkD _ _ _ _ _ f _ _ _ _ _ _) = f
    D-hU : D M c G h k → LpU M c h
    D-hU (mkD _ _ _ _ _ _ f _ _ _ _ _) = f
    D-hD : D M c G h k → LpD M c h
    D-hD (mkD _ _ _ _ _ _ _ f _ _ _ _) = f
    D-kU : D M c G h k → LpU M c k
    D-kU (mkD _ _ _ _ _ _ _ _ f _ _ _) = f
    D-kD : D M c G h k → LpD M c k
    D-kD (mkD _ _ _ _ _ _ _ _ _ f _ _) = f
    D-c1 : D M c G h k → Ct1 M c G h k
    D-c1 (mkD _ _ _ _ _ _ _ _ _ _ f _) = f
    D-c2 : D M c G h k → Ct2 M c G h k
    D-c2 (mkD _ _ _ _ _ _ _ _ _ _ _ f) = f

  ----------------------------------------------------------------------------
  -- elementary inequalities

  -- w ≤ 1 gives w q ≤ q and w w ≤ 1
  wle : ∀ {w} → w ≤ 1# → ∀ q → w * q ≤ q
  wle {w} w1 q = ≤-trans (*-monoʳ q w1) (≤-reflexive (*-identityˡ q))

  ww≤1 : ∀ {w} → w ≤ 1# → w * w ≤ 1#
  ww≤1 {w} w1 = ≤-trans (wle w1 w) w1

  -- (w w) q ≤ w q
  www : ∀ {w} → w ≤ 1# → ∀ q → (w * w) * q ≤ w * q
  www {w} w1 q = ≤-trans (≤-reflexive (*-assoc w w q)) (*-mono w (wle w1 q))

  -- x ≤ x + y and y ≤ x + y
  ≤-+ˡ : ∀ {x y} → y ≤ x + y
  ≤-+ˡ {x} {y} = ≤-trans ≤-+ʳ (≤-reflexive (+-comm y x))

  ----------------------------------------------------------------------------
  -- weakening of the constant, and changing the functions up to ≈

  module _ {M c c′ : ∣A∣} (cc : c ≤ c′) where
    Bnd-mono : ∀ {u} → Bnd M c u → Bnd M c′ u
    Bnd-mono b xM = ≤-trans (b xM) cc

    LpU-mono : ∀ {u} → LpU M c u → LpU M c′ u
    LpU-mono l aw w1 = ≤-trans (l aw w1) (+-mono ≤-refl (*-mono _ cc))

    LpD-mono : ∀ {u} → LpD M c u → LpD M c′ u
    LpD-mono l aw w1 = ≤-trans (l aw w1) (+-mono ≤-refl (*-mono _ cc))

    Ct1-mono : ∀ {G h k} → Ct1 M c G h k → Ct1 M c′ G h k
    Ct1-mono t aw w1 = ≤-trans (t aw w1) (+-mono ≤-refl (*-mono _ cc))

    Ct2-mono : ∀ {G h k} → Ct2 M c G h k → Ct2 M c′ G h k
    Ct2-mono t aw w1 = ≤-trans (t aw w1) (+-mono ≤-refl (*-mono _ cc))

    Dmono : ∀ {G h k} → D M c G h k → D M c′ G h k
    Dmono (mkD cG ch ck bG bh bk hU hD kU kD t1 t2) = mkD cG ch ck (Bnd-mono bG) (Bnd-mono bh) (Bnd-mono bk)
      (LpU-mono hU) (LpD-mono hD) (LpU-mono kU) (LpD-mono kD) (Ct1-mono t1) (Ct2-mono t2)

  module _ {M c : ∣A∣} {G G′ h h′ k k′ : ∣A∣ → ∣A∣} (eG : ∀ x → G x ≈ G′ x) (eh : ∀ x → h x ≈ h′ x) (ek : ∀ x → k x ≈ k′ x) where
    Cg-resp : ∀ {u u′ : ∣A∣ → ∣A∣} → (∀ x → u x ≈ u′ x) → Cg u → Cg u′
    Cg-resp e cu xy = trans (sym (e _)) (trans (cu xy) (e _))

    Bnd-resp : ∀ {u u′ : ∣A∣ → ∣A∣} → (∀ x → u x ≈ u′ x) → Bnd M c u → Bnd M c u′
    Bnd-resp e b xM = ≤-trans (≤-reflexive (sym (e _))) (b xM)

    LpU-resp : ∀ {u u′ : ∣A∣ → ∣A∣} → (∀ x → u x ≈ u′ x) → LpU M c u → LpU M c u′
    LpU-resp e l aw w1 = ≤-resp (e _) (+-cong (e _) refl) (l aw w1)

    LpD-resp : ∀ {u u′ : ∣A∣ → ∣A∣} → (∀ x → u x ≈ u′ x) → LpD M c u → LpD M c u′
    LpD-resp e l aw w1 = ≤-resp (e _) (+-cong (e _) refl) (l aw w1)

    D-resp : D M c G h k → D M c G′ h′ k′
    D-resp (mkD cG ch ck bG bh bk hU hD kU kD t1 t2) = mkD (Cg-resp eG cG) (Cg-resp eh ch) (Cg-resp ek ck)
      (Bnd-resp eG bG) (Bnd-resp eh bh) (Bnd-resp ek bk)
      (LpU-resp eh hU) (LpD-resp eh hD) (LpU-resp ek kU) (LpD-resp ek kD)
      (λ aw w1 → ≤-resp (+-cong (eG _) (*-cong refl (eh _))) (+-cong (+-cong (eG _) (*-cong refl (ek _))) refl) (t1 aw w1))
      (λ aw w1 → ≤-resp (+-cong (eG _) (*-cong refl (ek _))) (+-cong (+-cong (eG _) (*-cong refl (eh _))) refl) (t2 aw w1))

  ----------------------------------------------------------------------------
  -- G is Lipschitz with constant c + c (from the certificate)

  module _ {M c : ∣A∣} {G h k : ∣A∣ → ∣A∣} (d : D M c G h k) where
    private
      a≤M : ∀ {a w} → a + w ≤ M → a ≤ M
      a≤M aw = ≤-trans ≤-+ʳ aw

      -- w k ≤ w c, (w w) c ≤ w c
      cut : ∀ {w g x} → w ≤ 1# → x ≤ c → (g + w * x) + (w * w) * c ≤ g + w * (c + c)
      cut {w} {g} {x} w1 xc = ≤-trans (+-mono (+-mono ≤-refl (*-mono w xc)) (www w1 c))
        (≤-reflexive (solve 3 (λ g′ w′ c′ → (g′ :+ w′ :* c′) :+ w′ :* c′ := g′ :+ w′ :* (c′ :+ c′)) refl g w c))

    Gup : ∀ {a w} → a + w ≤ M → w ≤ 1# → G (a + w) ≤ G a + w * (c + c)
    Gup {a} {w} aw w1 = ≤-trans ≤-+ʳ (≤-trans (D-c1 d aw w1) (cut w1 (D-bk d (a≤M aw))))

    Gdn : ∀ {a w} → a + w ≤ M → w ≤ 1# → G a ≤ G (a + w) + w * (c + c)
    Gdn {a} {w} aw w1 = ≤-trans ≤-+ʳ (≤-trans (D-c2 d aw w1) (cut w1 (D-bh d (a≤M aw))))

  ----------------------------------------------------------------------------
  -- constants and the identity

  Dconst : ∀ M q → D M q (λ _ → q) (λ _ → 0#) (λ _ → 0#)
  Dconst M q = mkD (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → ≤-refl) (λ _ → 0-least) (λ _ → 0-least)
    (λ _ _ → 0-least) (λ _ _ → 0-least) (λ _ _ → 0-least) (λ _ _ → 0-least) (λ _ _ → ≤-+ʳ) (λ _ _ → ≤-+ʳ)

  Did : ∀ M → D M (M + 1#) (λ x → x) (λ _ → 0#) (λ _ → 1#)
  Did M = mkD (λ e → e) (λ _ → refl) (λ _ → refl) (λ xM → ≤-trans xM ≤-+ʳ) (λ _ → 0-least) (λ _ → ≤-+ˡ)
    (λ _ _ → 0-least) (λ _ _ → 0-least) (λ _ _ → ≤-+ʳ) (λ _ _ → ≤-+ʳ)
    (λ {a} {w} _ _ → ≤-trans (≤-reflexive (solve 2 (λ a′ w′ → (a′ :+ w′) :+ w′ :* con 0 := a′ :+ w′ :* con 1) refl a w)) ≤-+ʳ)
    (λ {a} {w} _ _ → ≤-trans (≤-reflexive (solve 2 (λ a′ w′ → a′ :+ w′ :* con 1 := (a′ :+ w′) :+ w′ :* con 0) refl a w)) ≤-+ʳ)

  ----------------------------------------------------------------------------
  -- sums and scalar multiples

  module _ {M c₁ c₂ : ∣A∣} {G₁ h₁ k₁ G₂ h₂ k₂ : ∣A∣ → ∣A∣} (d₁ : D M c₁ G₁ h₁ k₁) (d₂ : D M c₂ G₂ h₂ k₂) where
    private
      lin : ∀ x₁ x₂ w y₁ y₂ → (x₁ + w * y₁) + (x₂ + w * y₂) ≈ (x₁ + x₂) + w * (y₁ + y₂)
      lin x₁ x₂ w y₁ y₂ = solve 5 (λ a b w′ c d → (a :+ w′ :* c) :+ (b :+ w′ :* d) := (a :+ b) :+ w′ :* (c :+ d)) refl x₁ x₂ w y₁ y₂

      lin2 : ∀ x₁ x₂ w y₁ y₂ e₁ e₂ → ((x₁ + w * y₁) + (w * w) * e₁) + ((x₂ + w * y₂) + (w * w) * e₂)
        ≈ ((x₁ + x₂) + w * (y₁ + y₂)) + (w * w) * (e₁ + e₂)
      lin2 x₁ x₂ w y₁ y₂ e₁ e₂ = solve 7 (λ a b w′ c d e f → ((a :+ w′ :* c) :+ (w′ :* w′) :* e) :+ ((b :+ w′ :* d) :+ (w′ :* w′) :* f)
        := ((a :+ b) :+ w′ :* (c :+ d)) :+ (w′ :* w′) :* (e :+ f)) refl x₁ x₂ w y₁ y₂ e₁ e₂

    private
      lpU+ : ∀ {u₁ u₂ : ∣A∣ → ∣A∣} → LpU M c₁ u₁ → LpU M c₂ u₂ → LpU M (c₁ + c₂) (λ x → u₁ x + u₂ x)
      lpU+ {u₁} {u₂} l₁ l₂ {a} {w} aw w1 = ≤-trans (+-mono (l₁ aw w1) (l₂ aw w1)) (≤-reflexive (lin (u₁ a) (u₂ a) w c₁ c₂))

      lpD+ : ∀ {u₁ u₂ : ∣A∣ → ∣A∣} → LpD M c₁ u₁ → LpD M c₂ u₂ → LpD M (c₁ + c₂) (λ x → u₁ x + u₂ x)
      lpD+ {u₁} {u₂} l₁ l₂ {a} {w} aw w1 =
        ≤-trans (+-mono (l₁ aw w1) (l₂ aw w1)) (≤-reflexive (lin (u₁ (a + w)) (u₂ (a + w)) w c₁ c₂))

      ct1+ : Ct1 M (c₁ + c₂) (λ x → G₁ x + G₂ x) (λ x → h₁ x + h₂ x) (λ x → k₁ x + k₂ x)
      ct1+ {a} {w} aw w1 = ≤-trans (≤-reflexive (sym (lin (G₁ (a + w)) (G₂ (a + w)) w (h₁ a) (h₂ a))))
        (≤-trans (+-mono (D-c1 d₁ aw w1) (D-c1 d₂ aw w1)) (≤-reflexive (lin2 (G₁ a) (G₂ a) w (k₁ a) (k₂ a) c₁ c₂)))

      ct2+ : Ct2 M (c₁ + c₂) (λ x → G₁ x + G₂ x) (λ x → h₁ x + h₂ x) (λ x → k₁ x + k₂ x)
      ct2+ {a} {w} aw w1 = ≤-trans (≤-reflexive (sym (lin (G₁ a) (G₂ a) w (k₁ a) (k₂ a))))
        (≤-trans (+-mono (D-c2 d₁ aw w1) (D-c2 d₂ aw w1))
          (≤-reflexive (lin2 (G₁ (a + w)) (G₂ (a + w)) w (h₁ a) (h₂ a) c₁ c₂)))

    Dsum : D M (c₁ + c₂) (λ x → G₁ x + G₂ x) (λ x → h₁ x + h₂ x) (λ x → k₁ x + k₂ x)
    Dsum = mkD (λ e → +-cong (D-cG d₁ e) (D-cG d₂ e)) (λ e → +-cong (D-ch d₁ e) (D-ch d₂ e)) (λ e → +-cong (D-ck d₁ e) (D-ck d₂ e))
      (λ xM → +-mono (D-bG d₁ xM) (D-bG d₂ xM)) (λ xM → +-mono (D-bh d₁ xM) (D-bh d₂ xM)) (λ xM → +-mono (D-bk d₁ xM) (D-bk d₂ xM))
      (lpU+ (D-hU d₁) (D-hU d₂)) (lpD+ (D-hD d₁) (D-hD d₂)) (lpU+ (D-kU d₁) (D-kU d₂)) (lpD+ (D-kD d₁) (D-kD d₂)) ct1+ ct2+

  module _ {M c : ∣A∣} {G h k : ∣A∣ → ∣A∣} (q : ∣A∣) (d : D M c G h k) where
    private
      sl : ∀ q x w y → q * x + w * (q * y) ≈ q * (x + w * y)
      sl q x w y = solve 4 (λ q′ x′ w′ y′ → q′ :* x′ :+ w′ :* (q′ :* y′) := q′ :* (x′ :+ w′ :* y′)) refl q x w y

      sl2 : ∀ q g w x t → q * ((g + w * x) + (w * w) * t) ≈ (q * g + w * (q * x)) + (w * w) * (q * t)
      sl2 q g w x t = solve 5 (λ q′ g′ w′ x′ t′ → q′ :* ((g′ :+ w′ :* x′) :+ (w′ :* w′) :* t′)
        := (q′ :* g′ :+ w′ :* (q′ :* x′)) :+ (w′ :* w′) :* (q′ :* t′)) refl q g w x t

      sl3 : ∀ q x w t → q * (x + w * t) ≈ q * x + w * (q * t)
      sl3 q x w t = solve 4 (λ q′ x′ w′ t′ → q′ :* (x′ :+ w′ :* t′) := q′ :* x′ :+ w′ :* (q′ :* t′)) refl q x w t

      lpU : ∀ {u} → LpU M c u → LpU M (q * c) (λ x → q * u x)
      lpU l aw w1 = ≤-trans (*-mono q (l aw w1)) (≤-reflexive (sl3 q _ _ c))

      lpD : ∀ {u} → LpD M c u → LpD M (q * c) (λ x → q * u x)
      lpD l aw w1 = ≤-trans (*-mono q (l aw w1)) (≤-reflexive (sl3 q _ _ c))

    Dscale : D M (q * c) (λ x → q * G x) (λ x → q * h x) (λ x → q * k x)
    Dscale = mkD (λ e → *-cong refl (D-cG d e)) (λ e → *-cong refl (D-ch d e)) (λ e → *-cong refl (D-ck d e))
      (λ xM → *-mono q (D-bG d xM)) (λ xM → *-mono q (D-bh d xM)) (λ xM → *-mono q (D-bk d xM))
      (lpU (D-hU d)) (lpD (D-hD d)) (lpU (D-kU d)) (lpD (D-kD d))
      (λ {a} {w} aw w1 → ≤-trans (≤-reflexive (sl q (G (a + w)) w (h a)))
        (≤-trans (*-mono q (D-c1 d aw w1)) (≤-reflexive (sl2 q (G a) w (k a) c))))
      (λ {a} {w} aw w1 → ≤-trans (≤-reflexive (sl q (G a) w (k a)))
        (≤-trans (*-mono q (D-c2 d aw w1)) (≤-reflexive (sl2 q (G (a + w)) w (h a) c))))

  ----------------------------------------------------------------------------
  -- translation x ↦ t + x

  module _ {M M′ c : ∣A∣} {G h k : ∣A∣ → ∣A∣} (t : ∣A∣) (tM : t + M ≤ M′) (d : D M′ c G h k) where
    private
      pt : ∀ {a w} → a + w ≤ M → (t + a) + w ≤ M′
      pt aw = ≤-trans (≤-reflexive (+-assoc t _ _)) (≤-trans (+-mono ≤-refl aw) tM)

      ptx : ∀ {x} → x ≤ M → t + x ≤ M′
      ptx xM = ≤-trans (+-mono ≤-refl xM) tM

    Dshift : D M c (λ x → G (t + x)) (λ x → h (t + x)) (λ x → k (t + x))
    Dshift = mkD (λ e → D-cG d (+-cong refl e)) (λ e → D-ch d (+-cong refl e)) (λ e → D-ck d (+-cong refl e))
      (λ xM → D-bG d (ptx xM)) (λ xM → D-bh d (ptx xM)) (λ xM → D-bk d (ptx xM))
      (λ {a} {w} aw w1 → ≤-resp (D-ch d (+-assoc t _ _)) refl (D-hU d {t + a} {w} (pt aw) w1))
      (λ {a} {w} aw w1 → ≤-resp refl (+-cong (D-ch d (+-assoc t _ _)) refl) (D-hD d {t + a} {w} (pt aw) w1))
      (λ {a} {w} aw w1 → ≤-resp (D-ck d (+-assoc t _ _)) refl (D-kU d {t + a} {w} (pt aw) w1))
      (λ {a} {w} aw w1 → ≤-resp refl (+-cong (D-ck d (+-assoc t _ _)) refl) (D-kD d {t + a} {w} (pt aw) w1))
      (λ {a} {w} aw w1 → ≤-resp (+-cong (D-cG d (+-assoc t _ _)) refl) refl (D-c1 d {t + a} {w} (pt aw) w1))
      (λ {a} {w} aw w1 → ≤-resp refl (+-cong (+-cong (D-cG d (+-assoc t _ _)) refl) refl) (D-c2 d {t + a} {w} (pt aw) w1))

  ----------------------------------------------------------------------------
  -- composition with x ↦ l x, l ≤ 1

  module _ {M M′ c : ∣A∣} {G h k : ∣A∣ → ∣A∣} (l : ∣A∣) (l1 : l ≤ 1#) (lM : l * M ≤ M′) (d : D M′ c G h k) where
    private
      pt : ∀ {a w} → a + w ≤ M → (l * a) + (l * w) ≤ M′
      pt aw = ≤-trans (≤-reflexive (sym (distribˡ l _ _))) (≤-trans (*-mono l aw) lM)

      ptx : ∀ {x} → x ≤ M → l * x ≤ M′
      ptx xM = ≤-trans (*-mono l xM) lM

      lw≤w : ∀ {w} → l * w ≤ w
      lw≤w {w} = ≤-trans (*-monoʳ w l1) (≤-reflexive (*-identityˡ w))

      lw1 : ∀ {w} → w ≤ 1# → l * w ≤ 1#
      lw1 w1 = ≤-trans lw≤w w1

      lc≤c : l * c ≤ c
      lc≤c = ≤-trans (*-monoʳ c l1) (≤-reflexive (*-identityˡ c))

      llc : l * (l * c) ≤ c
      llc = ≤-trans (*-mono l lc≤c) lc≤c

      ldist : ∀ a w → G ((l * a) + (l * w)) ≈ G (l * (a + w))
      ldist a w = D-cG d (sym (distribˡ l a w))

      -- the scaled Lipschitz bound
      lip : ∀ {u : ∣A∣ → ∣A∣} {y z w : ∣A∣} → u y ≤ u z + (l * w) * c → l * u y ≤ l * u z + w * c
      lip {u} {y} {z} {w} le = ≤-trans (*-mono l le)
        (≤-trans (≤-reflexive (solve 4 (λ l′ x′ w′ c′ → l′ :* (x′ :+ (l′ :* w′) :* c′) := l′ :* x′ :+ w′ :* (l′ :* (l′ :* c′)))
            refl l (u z) w c))
          (+-mono ≤-refl (*-mono w llc)))

      lipU : ∀ {u : ∣A∣ → ∣A∣} (uc : Cg u) → LpU M′ c u → LpU M c (λ x → l * u (l * x))
      lipU {u} uc lp {a} {w} aw w1 =
        lip {u} {w = w} (≤-resp (uc (sym (distribˡ l a w))) refl (lp {l * a} {l * w} (pt aw) (lw1 w1)))

      lipD : ∀ {u : ∣A∣ → ∣A∣} (uc : Cg u) → LpD M′ c u → LpD M c (λ x → l * u (l * x))
      lipD {u} uc lp {a} {w} aw w1 =
        lip {u} {w = w} (≤-resp refl (+-cong (uc (sym (distribˡ l a w))) refl) (lp {l * a} {l * w} (pt aw) (lw1 w1)))

      sw : ∀ l w x → w * (l * x) ≈ (l * w) * x
      sw l w x = solve 3 (λ l′ w′ x′ → w′ :* (l′ :* x′) := (l′ :* w′) :* x′) refl l w x

      ww : ∀ {w} → (l * w) * (l * w) ≤ w * w
      ww {w} = *-mono₂ lw≤w lw≤w

      err : ∀ {w} (e : ∣A∣) → ((l * w) * (l * w)) * c ≤ (w * w) * c
      err {w} _ = *-monoʳ c ww

    private
      ctA1 : Ct1 M c (λ x → G (l * x)) (λ x → l * h (l * x)) (λ x → l * k (l * x))
      ctA1 {a} {w} aw w1 = ≤-resp (+-cong (ldist a w) (sym (sw l w (h (l * a)))))
        (+-cong (+-cong refl (sym (sw l w (k (l * a))))) refl)
        (≤-trans (D-c1 d {l * a} {l * w} (pt aw) (lw1 w1)) (+-mono ≤-refl (err c)))

      ctA2 : Ct2 M c (λ x → G (l * x)) (λ x → l * h (l * x)) (λ x → l * k (l * x))
      ctA2 {a} {w} aw w1 = ≤-resp refl (+-cong (+-cong (ldist a w) (sym (sw l w (h (l * a))))) refl)
        (≤-trans (≤-reflexive (+-cong refl (sw l w (k (l * a)))))
          (≤-trans (D-c2 d {l * a} {l * w} (pt aw) (lw1 w1)) (+-mono ≤-refl (err c))))

    Daff : D M c (λ x → G (l * x)) (λ x → l * h (l * x)) (λ x → l * k (l * x))
    Daff = mkD (λ e → D-cG d (*-cong refl e)) (λ e → *-cong refl (D-ch d (*-cong refl e)))
      (λ e → *-cong refl (D-ck d (*-cong refl e)))
      (λ xM → D-bG d (ptx xM)) (λ xM → ≤-trans (*-mono l (D-bh d (ptx xM))) lc≤c) (λ xM → ≤-trans (*-mono l (D-bk d (ptx xM))) lc≤c)
      (lipU (D-ch d) (D-hU d)) (lipD (D-ch d) (D-hD d)) (lipU (D-ck d) (D-kU d)) (lipD (D-ck d) (D-kD d)) ctA1 ctA2

  ----------------------------------------------------------------------------
  -- finiteness: c ≤ 2ˢ, and the wrapper `Deriv` that hides the constant

  Fin : ∣A∣ → Set₁
  Fin c = Σ ℕ (λ S → c ≤ P S)

  Fin-0 : Fin 0#
  Fin-0 = 0 , 0-least

  Fin-1 : Fin 1#
  Fin-1 = 0 , ≤-refl

  Fin-+ : ∀ {x y} → Fin x → Fin y → Fin (x + y)
  Fin-+ (i , xi) (j , yj) = suc (i ℕ.+ j) , P-+ xi yj

  Fin-* : ∀ {x y} → Fin x → Fin y → Fin (x * y)
  Fin-* (i , xi) (j , yj) = (i ℕ.+ j) , P-* xi yj

  Deriv : ∣A∣ → (∣A∣ → ∣A∣) → (∣A∣ → ∣A∣) → (∣A∣ → ∣A∣) → Set₁
  Deriv M G h k = Σ ∣A∣ (λ c → Fin c × D M c G h k)

  module _ {M : ∣A∣} where
    DFconst : ∀ q → Fin q → Deriv M (λ _ → q) (λ _ → 0#) (λ _ → 0#)
    DFconst q fq = q , fq , Dconst M q

    DFid : Fin M → Deriv M (λ x → x) (λ _ → 0#) (λ _ → 1#)
    DFid fM = M + 1# , Fin-+ fM Fin-1 , Did M

    module _ {G₁ h₁ k₁ G₂ h₂ k₂ : ∣A∣ → ∣A∣} where
      DFsum : Deriv M G₁ h₁ k₁ → Deriv M G₂ h₂ k₂ →
        Deriv M (λ x → G₁ x + G₂ x) (λ x → h₁ x + h₂ x) (λ x → k₁ x + k₂ x)
      DFsum (c₁ , f₁ , d₁) (c₂ , f₂ , d₂) = c₁ + c₂ , Fin-+ f₁ f₂ , Dsum d₁ d₂

    module _ {G h k : ∣A∣ → ∣A∣} where
      DFscale : ∀ q → Fin q → Deriv M G h k → Deriv M (λ x → q * G x) (λ x → q * h x) (λ x → q * k x)
      DFscale q fq (c , f , d) = q * c , Fin-* fq f , Dscale q d

      module _ {G′ h′ k′ : ∣A∣ → ∣A∣} where
        DFresp : (∀ x → G x ≈ G′ x) → (∀ x → h x ≈ h′ x) → (∀ x → k x ≈ k′ x) → Deriv M G h k → Deriv M G′ h′ k′
        DFresp eG eh ek (c , f , d) = c , f , D-resp eG eh ek d

  module _ {M M′ : ∣A∣} {G h k : ∣A∣ → ∣A∣} where
    DFshift : ∀ t → t + M ≤ M′ → Deriv M′ G h k → Deriv M (λ x → G (t + x)) (λ x → h (t + x)) (λ x → k (t + x))
    DFshift t tM (c , f , d) = c , f , Dshift t tM d

    DFaff : ∀ l → l ≤ 1# → l * M ≤ M′ → Deriv M′ G h k →
      Deriv M (λ x → G (l * x)) (λ x → l * h (l * x)) (λ x → l * k (l * x))
    DFaff l l1 lM (c , f , d) = c , f , Daff l l1 lM d
