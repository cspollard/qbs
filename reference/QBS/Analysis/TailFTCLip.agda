{-# OPTIONS --safe --without-K #-}

-- A tail-form fundamental theorem of calculus with Lipschitz errors (part 1: the algebra).
--
-- Two integrands h, k and a tail antiderivative G with `G′ = −(h − k)` (integration by parts: `∫ h + G(b) = G(a) + ∫ k`).
-- On a dyadic piece [a, b], b = a + w, w = ½ⁿ, with piece integrals Dg of h and Df of k and e = w² c, the claims are
--   UpL Dg Df Ga Gb E :  Dg + Gb ≤ (Ga + Df) + E        LoL Dg Df Ga Gb E :  Ga + Df ≤ (Dg + Gb) + E.
-- A piece splits into two halves with the same c and half the width, and the claims for the halves add up to the
-- claim for the whole after cancelling the bounded middle term `G m` (`cancel≤P`); the error budget
-- `E = (w² ½ᵈ)(3c)` is additive under halving (`err-split`).  Unlike `Analysis/TailFTC` there is no monotonicity:
-- the pointwise input is that h, k are Lipschitz (constant c) and the certificate holds up to `w² c`.  Over an abstract
-- Archimedean ω-semiring.  Also the scaling by `½ˢ`: `P s · ½ˢ = 1`, `unscale`.
module QBS.Analysis.TailFTCLip where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.TailFTC using (module AlgT)

module AlgL (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp; hp-zero; hp-double; arch; cancel≤)
  open AlgT A R using (P; P≥1; hp≤1; cancel≤P; eps)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  UpL : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  UpL Dg Df Ga Gb E = Dg + Gb ≤ (Ga + Df) + E

  LoL : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  LoL Dg Df Ga Gb E = Ga + Df ≤ (Dg + Gb) + E

  UpL-cong : ∀ {Dg Dg′ Df Df′ Ga Gb E E′} → Dg ≈ Dg′ → Df ≈ Df′ → E ≈ E′ → UpL Dg Df Ga Gb E → UpL Dg′ Df′ Ga Gb E′
  UpL-cong eg ef ee = ≤-resp (+-cong eg refl) (+-cong (+-cong refl ef) ee)

  LoL-cong : ∀ {Dg Dg′ Df Df′ Ga Gb E E′} → Dg ≈ Dg′ → Df ≈ Df′ → E ≈ E′ → LoL Dg Df Ga Gb E → LoL Dg′ Df′ Ga Gb E′
  LoL-cong eg ef ee = ≤-resp (+-cong refl ef) (+-cong (+-cong eg refl) ee)

  -- the base case: Dg ≤ Wh + e, Gb + Wh ≤ Ga + Wk + e, Wk ≤ Df + e
  base-upL : ∀ {Dg Df Ga Gb Wh Wk e} → Dg ≤ Wh + e → Gb + Wh ≤ (Ga + Wk) + e → Wk ≤ Df + e →
    UpL Dg Df Ga Gb (e + (e + e))
  base-upL {Dg} {Df} {Ga} {Gb} {Wh} {Wk} {e} dg cert wk =
    ≤-trans (+-mono dg (≤-refl {Gb}))
      (≤-trans (≤-reflexive (solve 3 (λ w e′ b → (w :+ e′) :+ b := (b :+ w) :+ e′) refl Wh e Gb))
        (≤-trans (+-mono cert (≤-refl {e}))
          (≤-trans (+-mono (+-mono (+-mono (≤-refl {Ga}) wk) (≤-refl {e})) (≤-refl {e}))
            (≤-reflexive (solve 3 (λ g d e′ → ((g :+ (d :+ e′)) :+ e′) :+ e′ := (g :+ d) :+ (e′ :+ (e′ :+ e′))) refl Ga Df e)))))

  base-loL : ∀ {Dg Df Ga Gb Wh Wk e} → Wh ≤ Dg + e → Ga + Wk ≤ (Gb + Wh) + e → Df ≤ Wk + e →
    LoL Dg Df Ga Gb (e + (e + e))
  base-loL {Dg} {Df} {Ga} {Gb} {Wh} {Wk} {e} wh cert df =
    ≤-trans (+-mono (≤-refl {Ga}) df)
      (≤-trans (≤-reflexive (solve 3 (λ g k e′ → g :+ (k :+ e′) := (g :+ k) :+ e′) refl Ga Wk e))
        (≤-trans (+-mono cert (≤-refl {e}))
          (≤-trans (+-mono (+-mono (+-mono (≤-refl {Gb}) wh) (≤-refl {e})) (≤-refl {e}))
            (≤-reflexive (solve 3 (λ b d e′ → ((b :+ (d :+ e′)) :+ e′) :+ e′ := (d :+ b) :+ (e′ :+ (e′ :+ e′))) refl Gb Dg e)))))

  -- gluing two halves
  up-stepL : ∀ {k DgL DgR DfL DfR Ga Gm Gb E₁ E₂} → Gm ≤ P k →
    UpL DgL DfL Ga Gm E₁ → UpL DgR DfR Gm Gb E₂ → UpL (DgL + DgR) (DfL + DfR) Ga Gb (E₁ + E₂)
  up-stepL {k} {DgL} {DgR} {DfL} {DfR} {Ga} {Gm} {Gb} {E₁} {E₂} bx uL uR =
    cancel≤P k bx (≤-resp e1 e2 (+-mono uL uR))
    where
    e1 : (DgL + Gm) + (DgR + Gb) ≈ Gm + ((DgL + DgR) + Gb)
    e1 = solve 4 (λ l g r b → (l :+ g) :+ (r :+ b) := g :+ ((l :+ r) :+ b)) refl DgL Gm DgR Gb
    e2 : ((Ga + DfL) + E₁) + ((Gm + DfR) + E₂) ≈ Gm + (((Ga + (DfL + DfR))) + (E₁ + E₂))
    e2 = solve 6 (λ a l e m r f → ((a :+ l) :+ e) :+ ((m :+ r) :+ f) := m :+ ((a :+ (l :+ r)) :+ (e :+ f))) refl Ga DfL E₁ Gm DfR E₂

  lo-stepL : ∀ {k DgL DgR DfL DfR Ga Gm Gb E₁ E₂} → Gm ≤ P k →
    LoL DgL DfL Ga Gm E₁ → LoL DgR DfR Gm Gb E₂ → LoL (DgL + DgR) (DfL + DfR) Ga Gb (E₁ + E₂)
  lo-stepL {k} {DgL} {DgR} {DfL} {DfR} {Ga} {Gm} {Gb} {E₁} {E₂} bx lL lR =
    cancel≤P k bx (≤-resp e1 e2 (+-mono lL lR))
    where
    e1 : (Ga + DfL) + (Gm + DfR) ≈ Gm + (Ga + (DfL + DfR))
    e1 = solve 4 (λ a l m r → (a :+ l) :+ (m :+ r) := m :+ (a :+ (l :+ r))) refl Ga DfL Gm DfR
    e2 : ((DgL + Gm) + E₁) + ((DgR + Gb) + E₂) ≈ Gm + (((DgL + DgR) + Gb) + (E₁ + E₂))
    e2 = solve 6 (λ l g e r b f → ((l :+ g) :+ e) :+ ((r :+ b) :+ f) := g :+ (((l :+ r) :+ b) :+ (e :+ f))) refl DgL Gm E₁ DgR Gb E₂

  -- the error budget: the two halves (width ½ⁿ⁺¹, depth d) add up to the whole (width ½ⁿ, depth d+1)
  err : ℕ → ℕ → ∣A∣ → ∣A∣
  err n d c = ((hp n * hp n) * hp d) * c

  err-split : ∀ n d c → err (suc n) d c + err (suc n) d c ≈ err n (suc d) c
  err-split n d c = trans (sym (distribʳ c X X)) (*-cong twoX refl)
    where
    u = hp (suc n)
    X = (u * u) * hp d
    -- 2 (u u q) = u (u + u) q = u v q = v (u q) = v (v ½ᵈ⁺¹)
    twoX : X + X ≈ (hp n * hp n) * hp (suc d)
    twoX = trans (solve 2 (λ x q → (x :* x) :* q :+ (x :* x) :* q := (x :* (x :+ x)) :* q) refl u (hp d))
      (trans (*-cong (*-cong refl (hp-double n)) refl)
        (trans (solve 3 (λ x v q → (x :* v) :* q := v :* (x :* q)) refl u (hp n) (hp d))
          (trans (*-cong refl (sym (eps n d))) (sym (*-assoc (hp n) (hp n) (hp (suc d)))))))

  -- the budget at the root is at most ½ᵈ when 3c ≤ 1
  err-root : ∀ d {c} → c ≤ 1# → err 0 d c ≤ hp d
  err-root d {c} c1 = ≤-trans (≤-reflexive (*-cong (trans (*-cong (*-cong hp-zero hp-zero) refl)
    (trans (*-cong (*-identityˡ 1#) refl) (*-identityˡ (hp d)))) refl))
    (≤-trans (*-mono (hp d) c1) (≤-reflexive (*-identityʳ (hp d))))

  close : ∀ {X Y} {E : ℕ → ∣A∣} → (∀ d → E d ≤ hp d) → (∀ d → X ≤ Y + E d) → X ≤ Y
  close eb le = arch (λ d → ≤-trans (le d) (+-mono ≤-refl (eb d)))

  ----------------------------------------------------------------------------
  -- scaling by ½ˢ

  P*hp : ∀ s → P s * hp s ≈ 1#
  P*hp zero = *-identityˡ 1#
  P*hp (suc s) = trans (solve 2 (λ p h → (p :+ p) :* h := p :* (h :+ h)) refl (P s) (hp (suc s)))
    (trans (*-cong refl (hp-double s)) (P*hp s))

  unscale : ∀ s {x y} → hp s * x ≈ hp s * y → x ≈ y
  unscale s {x} {y} e = trans (sym (*-identityˡ x)) (trans (*-cong (sym (P*hp s)) refl) (trans (*-assoc _ _ _)
    (trans (*-cong refl e) (trans (sym (*-assoc _ _ _)) (trans (*-cong (P*hp s) refl) (*-identityˡ y))))))
