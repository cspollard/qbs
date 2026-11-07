{-# OPTIONS --safe --without-K #-}

-- The value-level algebra behind the `idT` laws of `RQArith`, over [0, ∞].  (The `Alg` modules hold value-level lemmas over the abstract carrier, kept apart so that the modules with the QBS morphisms typecheck quickly.)
--   * `monus-add*`: t ≤ x gives t + (x ∸ t) ≈ x for every t, bounded or not;
--   * `Inv p n P N`, "the point with parts (p, n) is the real number P − N": the cross equality p + N ≈ P + n, and
--     bounded P, N force bounded p, n.  `Inv` composes through sums (`step-inv`) although `≐` does not (≐ is not
--     transitive at infinite points);
--   * `step-inv`: from `Inv v a b`, `Inv u P N` and the addition law at (v, u), `Inv w (a + P) (b + N)`, with one part of
--     each of u, v, w zero; `Inv-of`: a cross equality with one zero part, and the bounded consequence, is an `Inv`.
-- Route: classify each of v, u by its parts (both bounded, or one of them ∞ and the other bounded: a part is
-- zero) and treat the nine cases: all bounded by cancelling the bounded sum Vp + Vn + Up + Un from the sum of the three
-- equations, otherwise both sides of the goal are ∞ (`sum-top-bnd`, `top-sum`).  `monus-add*` splits on `Bnd t`.
module QBS.Continuous.RQArithAlg where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (infC)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.InfAlg using (module InfAlg)
open import QBS.Continuous.Monus using (module Monus)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)

module RQArithAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; refl; sym; trans; +-cong; +-comm; ≤-trans; ≤-reflexive; ≤-+ʳ;
    commutativeSemiring) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; finite)
  open SubSemiring finite using (Is-0; Is-+; Is-resp)
  open InfAlg lem₁ using (cancel-bnd; top-sum; sum-top-bnd; not-bnd-top; bnd-top-⊥; top-⊑)
  open Monus lem₁ using (monus; monus-add)
  open LebesgueShiftAlg (lemOf lem₁) using (total)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- small facts

  bnd-mono : ∀ {x y} → y ≤ x → Bnd x → Bnd y
  bnd-mono yx (n , le) = n , ≤-trans yx le

  le+ˡ : ∀ {x y} → y ≤ x + y
  le+ˡ {x} {y} = ≤-trans (≤-+ʳ {y} {x}) (≤-reflexive (+-comm y x))

  z+ : ∀ x → x + 0# ≈ x
  z+ x = solve 1 (λ x → x :+ con 0 := x) refl x

  +z : ∀ x → 0# + x ≈ x
  +z x = solve 1 (λ x → con 0 :+ x := x) refl x

  zero-top : 0# ≈ infC → ⊥
  zero-top e = bnd-top-⊥ (Is-resp {0#} {infC} e Is-0)

  tR : ∀ {p q} → q ≈ infC → p + q ≈ infC
  tR {p} {q} h = trans (+-comm p q) (top-sum h p)

  eqTop : ∀ {p q} → p ≈ infC → q ≈ infC → p ≈ q
  eqTop h k = trans h (sym k)

  -- t ≤ x gives t + (x ∸ t) ≈ x, also for t = ∞
  monus-add* : ∀ t x → t ≤ x → t + monus x t ≈ x
  monus-add* t x tx with lem₁ (Bnd t)
  ... | inj₁ bt = monus-add x t bt tx
  ... | inj₂ nt = trans (top-sum ti _) (sym (top-⊑ {x} (≤-trans (≤-reflexive (sym ti)) tx)))
    where ti = not-bnd-top t nt

  -- the order is total: not (n ≤ p) gives p ≤ n
  not-le : ∀ {p n} → (n ≤ p → ⊥) → p ≤ n
  not-le {p} {n} h = [ (λ pn → pn) , (λ np → ⊥-elim (h np)) ]′ (total p n)

  ----------------------------------------------------------------------------
  -- the invariant

  Inv : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  Inv p n P N = (p + N ≈ P + n) × (Bnd P → Bnd N → Bnd p × Bnd n)

  -- a cross equality with a zero part is an invariant
  Inv-of : ∀ {p n a b} → (p ≈ 0# ⊎ n ≈ 0#) → p + b ≈ a + n → Inv p n a b
  Inv-of {p} {n} {a} {b} (inj₁ p0) e = e , λ ba bb → Is-resp {0#} {p} (sym p0) Is-0 ,
    bnd-mono {b} {n} (≤-trans (le+ˡ {a} {n}) (≤-reflexive (trans (sym e) (trans (+-cong p0 refl) (+z b))))) bb
  Inv-of {p} {n} {a} {b} (inj₂ n0) e = e , λ ba bb → bnd-mono {a} {p}
    (≤-trans (≤-+ʳ {p} {b}) (≤-reflexive (trans e (trans (+-cong refl n0) (z+ a))))) ba ,
    Is-resp {0#} {n} (sym n0) Is-0

  -- the classes of a point with a zero part
  Cls : ∣A∣ → ∣A∣ → Set₁
  Cls p n = (Bnd p × Bnd n) ⊎ ((p ≈ infC × Bnd n) ⊎ (n ≈ infC × Bnd p))

  cls : ∀ {p n} → (p ≈ 0# ⊎ n ≈ 0#) → Cls p n
  cls {p} {n} z with lem₁ (Bnd p) | lem₁ (Bnd n)
  ... | inj₁ bp | inj₁ bn = inj₁ (bp , bn)
  ... | inj₁ bp | inj₂ nn = inj₂ (inj₂ (not-bnd-top n nn , bp))
  ... | inj₂ np | _ = inj₂ (inj₁ (not-bnd-top p np , bn))
    where
      bn : Bnd _
      bn = [ (λ p0 → ⊥-elim (zero-top (trans (sym p0) (not-bnd-top p np)))) , (λ n0 → Is-resp {0#} {n} (sym n0) Is-0) ]′ z

  ----------------------------------------------------------------------------
  -- the bounded case, and the sums that are ∞

  fin-case : ∀ {Vp Vn Up Un Wp Wn a b P N} → Bnd Vp → Bnd Vn → Bnd Up → Bnd Un → Vp + b ≈ a + Vn → Up + N ≈ P + Un →
    Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Wp + (b + N) ≈ (a + P) + Wn
  fin-case {Vp} {Vn} {Up} {Un} {Wp} {Wn} {a} {b} {P} {N} bVp bVn bUp bUn e3 e2 e1 =
    cancel-bnd {(Vp + Vn) + (Up + Un)} (Is-+ {Vp + Vn} {Up + Un} (Is-+ {Vp} {Vn} bVp bVn) (Is-+ {Up} {Un} bUp bUn))
      (trans (solve 10 (λ Vp Vn Up Un Wp Wn a b P N → ((Vp :+ Vn) :+ (Up :+ Un)) :+ (Wp :+ (b :+ N))
        := (Wp :+ (Vn :+ Un)) :+ ((Vp :+ b) :+ (Up :+ N))) refl Vp Vn Up Un Wp Wn a b P N)
      (trans (+-cong e1 (+-cong e3 e2)) (solve 10 (λ Vp Vn Up Un Wp Wn a b P N →
        ((Vp :+ Up) :+ Wn) :+ ((a :+ Vn) :+ (P :+ Un)) := ((Vp :+ Vn) :+ (Up :+ Un)) :+ ((a :+ P) :+ Wn))
        refl Vp Vn Up Un Wp Wn a b P N)))

  -- the shared tops
  aTop : ∀ {Vp Vn a b} → Vp ≈ infC → Bnd Vn → Vp + b ≈ a + Vn → a ≈ infC
  aTop {Vp} {Vn} {a} {b} h bn e = sum-top-bnd {a} {Vn} bn (trans (sym e) (top-sum h b))

  bTop : ∀ {Vp Vn a b} → Vn ≈ infC → Bnd Vp → Vp + b ≈ a + Vn → b ≈ infC
  bTop {Vp} {Vn} {a} {b} h bp e = sum-top-bnd {b} {Vp} bp (trans (+-comm b Vp) (trans e (tR h)))

  PTop : ∀ {Up Un P N} → Up ≈ infC → Bnd Un → Up + N ≈ P + Un → P ≈ infC
  PTop {Up} {Un} {P} {N} h bn e = sum-top-bnd {P} {Un} bn (trans (sym e) (top-sum h N))

  NTop : ∀ {Up Un P N} → Un ≈ infC → Bnd Up → Up + N ≈ P + Un → N ≈ infC
  NTop {Up} {Un} {P} {N} h bu e = sum-top-bnd {N} {Up} bu (trans (+-comm N Up) (trans e (tR h)))

  WpTop : ∀ {Vp Vn Up Un Wp Wn} → Vp + Up ≈ infC → Bnd (Vn + Un) → Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Wp ≈ infC
  WpTop {Vp} {Vn} {Up} {Un} {Wp} {Wn} h b e = sum-top-bnd {Wp} {Vn + Un} b (trans e (top-sum h Wn))

  WnTop : ∀ {Vp Vn Up Un Wp Wn} → Vn + Un ≈ infC → Bnd (Vp + Up) → Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Wn ≈ infC
  WnTop {Vp} {Vn} {Up} {Un} {Wp} {Wn} h b e =
    sum-top-bnd {Wn} {Vp + Up} b (trans (+-comm Wn _) (trans (sym e) (tR h)))

  ----------------------------------------------------------------------------
  -- the nine cases

  -- both sides of the goal are ∞
  topGoal : ∀ {Wp Wn a b P N} → (Wp ≈ infC ⊎ b ≈ infC ⊎ N ≈ infC) → (a ≈ infC ⊎ P ≈ infC ⊎ Wn ≈ infC) →
    Wp + (b + N) ≈ (a + P) + Wn
  topGoal {Wp} {Wn} {a} {b} {P} {N} l r = eqTop
    ([ (λ h → top-sum h _) , [ (λ h → tR {Wp} (top-sum h N)) , (λ h → tR {Wp} (tR h)) ]′ ]′ l)
    ([ (λ h → top-sum (top-sum h P) Wn) , [ (λ h → top-sum (tR {a} h) Wn) , (λ h → tR h) ]′ ]′ r)

  step-B : ∀ {Vp Vn Up Un Wp Wn a b P N} → Vp + b ≈ a + Vn → Up + N ≈ P + Un →
    Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Bnd Vp × Bnd Vn → Cls Up Un → Wp + (b + N) ≈ (a + P) + Wn
  step-B e3 e2 e1 (bVp , bVn) (inj₁ (bUp , bUn)) = fin-case bVp bVn bUp bUn e3 e2 e1
  step-B e3 e2 e1 (bVp , bVn) (inj₂ (inj₁ (hUp , bUn))) = topGoal (inj₁ (WpTop (tR hUp) (Is-+ bVn bUn) e1))
    (inj₂ (inj₁ (PTop hUp bUn e2)))
  step-B e3 e2 e1 (bVp , bVn) (inj₂ (inj₂ (hUn , bUp))) = topGoal (inj₂ (inj₂ (NTop hUn bUp e2)))
    (inj₂ (inj₂ (WnTop (tR hUn) (Is-+ bVp bUp) e1)))

  step-P : ∀ {Vp Vn Up Un Wp Wn a b P N} → Vp + b ≈ a + Vn → Up + N ≈ P + Un →
    Wp + (Vn + Un) ≈ (Vp + Up) + Wn → (Vp ≈ infC × Bnd Vn) → Cls Up Un → Wp + (b + N) ≈ (a + P) + Wn
  step-P e3 e2 e1 (hVp , bVn) (inj₁ (bUp , bUn)) = topGoal (inj₁ (WpTop (top-sum hVp _) (Is-+ bVn bUn) e1))
    (inj₁ (aTop hVp bVn e3))
  step-P e3 e2 e1 (hVp , bVn) (inj₂ (inj₁ (hUp , bUn))) = topGoal (inj₁ (WpTop (top-sum hVp _) (Is-+ bVn bUn) e1))
    (inj₁ (aTop hVp bVn e3))
  step-P e3 e2 e1 (hVp , bVn) (inj₂ (inj₂ (hUn , bUp))) = topGoal (inj₂ (inj₂ (NTop hUn bUp e2)))
    (inj₁ (aTop hVp bVn e3))

  step-N : ∀ {Vp Vn Up Un Wp Wn a b P N} → Vp + b ≈ a + Vn → Up + N ≈ P + Un →
    Wp + (Vn + Un) ≈ (Vp + Up) + Wn → (Vn ≈ infC × Bnd Vp) → Cls Up Un → Wp + (b + N) ≈ (a + P) + Wn
  step-N e3 e2 e1 (hVn , bVp) (inj₁ (bUp , bUn)) = topGoal (inj₂ (inj₁ (bTop hVn bVp e3)))
    (inj₂ (inj₂ (WnTop (top-sum hVn _) (Is-+ bVp bUp) e1)))
  step-N e3 e2 e1 (hVn , bVp) (inj₂ (inj₁ (hUp , bUn))) = topGoal (inj₂ (inj₁ (bTop hVn bVp e3)))
    (inj₂ (inj₁ (PTop hUp bUn e2)))
  step-N e3 e2 e1 (hVn , bVp) (inj₂ (inj₂ (hUn , bUp))) = topGoal (inj₂ (inj₁ (bTop hVn bVp e3)))
    (inj₂ (inj₂ (WnTop (top-sum hVn _) (Is-+ bVp bUp) e1)))

  step-alg : ∀ {Vp Vn Up Un Wp Wn a b P N} → (Vp ≈ 0# ⊎ Vn ≈ 0#) → (Up ≈ 0# ⊎ Un ≈ 0#) →
    Vp + b ≈ a + Vn → Up + N ≈ P + Un → Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Wp + (b + N) ≈ (a + P) + Wn
  step-alg zV zU e3 e2 e1 = [ (λ c → step-B e3 e2 e1 c (cls zU))
    , [ (λ c → step-P e3 e2 e1 c (cls zU)) , (λ c → step-N e3 e2 e1 c (cls zU)) ]′ ]′ (cls zV)

  -- bounded parts give bounded sum parts
  step-bnd : ∀ {Vp Vn Up Un Wp Wn} → (Wp ≈ 0# ⊎ Wn ≈ 0#) → Bnd Vp → Bnd Vn → Bnd Up → Bnd Un →
    Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Bnd Wp × Bnd Wn
  step-bnd {Vp} {Vn} {Up} {Un} {Wp} {Wn} (inj₁ w0) bVp bVn bUp bUn e = Is-resp {0#} {Wp} (sym w0) Is-0 ,
    bnd-mono {Vn + Un} {Wn} (≤-trans (le+ˡ {Vp + Up} {Wn}) (≤-reflexive (trans (sym e) (trans (+-cong w0 refl) (+z _)))))
      (Is-+ {Vn} {Un} bVn bUn)
  step-bnd {Vp} {Vn} {Up} {Un} {Wp} {Wn} (inj₂ w0) bVp bVn bUp bUn e =
    bnd-mono {Vp + Up} {Wp} (≤-trans (≤-+ʳ {Wp} {Vn + Un}) (≤-reflexive (trans e (trans (+-cong refl w0) (z+ _)))))
      (Is-+ {Vp} {Up} bVp bUp) , Is-resp {0#} {Wn} (sym w0) Is-0

  -- the invariant composes through the sum
  step-inv : ∀ {Vp Vn Up Un Wp Wn a b P N} → (Vp ≈ 0# ⊎ Vn ≈ 0#) → (Up ≈ 0# ⊎ Un ≈ 0#) → (Wp ≈ 0# ⊎ Wn ≈ 0#) →
    Inv Vp Vn a b → Inv Up Un P N → Wp + (Vn + Un) ≈ (Vp + Up) + Wn → Inv Wp Wn (a + P) (b + N)
  step-inv {Vp} {Vn} {Up} {Un} {Wp} {Wn} {a} {b} {P} {N} zV zU zW (e3 , iV) (e2 , iU) e1 =
    step-alg zV zU e3 e2 e1 , λ bs bt →
      let bP = bnd-mono {a + P} {P} (le+ˡ {a} {P}) bs ; bN = bnd-mono {b + N} {N} (le+ˡ {b} {N}) bt
          ba = bnd-mono {a + P} {a} (≤-+ʳ {a} {P}) bs ; bb = bnd-mono {b + N} {b} (≤-+ʳ {b} {N}) bt
      in step-bnd zW (proj₁ (iV ba bb)) (proj₂ (iV ba bb)) (proj₁ (iU bP bN)) (proj₂ (iU bP bN)) e1
