{-# OPTIONS --safe --without-K #-}

-- Squares respect `≐` (used by `SignedVar`).
--   * `sq-alg`: a + d ≈ c + b gives a² + b² + (c d + d c) ≈ c² + d² + (a b + b a) in [0, ∞], including infinite values;
--   * `sq-cong`: f ≐ g gives f *T f ≐ g *T g.
-- Route: all four values bounded: cross-add S₂ = (a + d)(b + d) + (c + b)(a + c) (the two sides differ by S₁ − S₂ and
-- S₁ ≈ S₂ by a + d ≈ c + b) and cancel the bounded S₂ (`cancel-bnd`); otherwise some value is ∞ (excluded middle on
-- `Bnd`), then a + d ≈ c + b forces a second one, and both sides contain the square or product of the two (`top-mul`).
module QBS.Continuous.SignedSq where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (infC)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.InfAlg using (module InfAlg)
open import QBS.Continuous.SignedTest using (module SignedTest)

module SignedSq (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; _*_; 1#; refl; sym; trans; +-cong; *-cong; +-comm; *-identityʳ;
    ≤-trans; ≤-reflexive; *-mono; commutativeSemiring) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; finite)
  open SubSemiring finite using (Is-+; Is-*)
  open InfAlg lem₁ using (cancel-bnd; top-sum; top-ge; sum-top-bnd; not-bnd-top; top-⊑; bnd-top-⊥)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _≐_; _*T_)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  -- ∞ · ∞ = ∞
  top-mul : ∀ {x y} → x ≈ infC → y ≈ infC → x * y ≈ infC
  top-mul {x} {y} hx hy = top-⊑ {x * y} (≤-trans (≤-reflexive (sym hx))
    (≤-trans (≤-reflexive (sym (*-identityʳ x))) (*-mono x (top-ge hy 1#))))

  -- a sum equal to ∞ has an infinite summand
  sum-top : ∀ {x y} → x + y ≈ infC → x ≈ infC ⊎ y ≈ infC
  sum-top {x} {y} e with lem₁ (Bnd y)
  ... | inj₁ by = inj₁ (sum-top-bnd {x} by e)
  ... | inj₂ ny = inj₂ (not-bnd-top y ny)

  inL : ∀ {p} q → p ≈ infC → p + q ≈ infC
  inL q h = top-sum h q

  inR : ∀ p {q} → q ≈ infC → p + q ≈ infC
  inR p {q} h = trans (+-comm p q) (top-sum h p)

  module _ (a b c d : ∣A∣) where
    T₁ T₂ : ∣A∣
    T₁ = (a * a + b * b) + (c * d + d * c)
    T₂ = (c * c + d * d) + (a * b + b * a)

  open import Data.Product.Base using (_×_; _,_)

  topA : ∀ {a b c d} → a + d ≈ c + b → a ≈ infC → T₁ a b c d ≈ infC × T₂ a b c d ≈ infC
  topA {a} {b} {c} {d} h ha with sum-top {c} {b} (trans (sym h) (inL d ha))
  ... | inj₁ hc = inL _ (inL _ (top-mul ha ha)) , inL _ (inL _ (top-mul hc hc))
  ... | inj₂ hb = inL _ (inL _ (top-mul ha ha)) , inR _ (inL _ (top-mul ha hb))

  topB : ∀ {a b c d} → a + d ≈ c + b → b ≈ infC → T₁ a b c d ≈ infC × T₂ a b c d ≈ infC
  topB {a} {b} {c} {d} h hb with sum-top {a} {d} (trans h (inR c hb))
  ... | inj₁ ha = topA h ha
  ... | inj₂ hd = inL _ (inR _ (top-mul hb hb)) , inL _ (inR _ (top-mul hd hd))

  topC : ∀ {a b c d} → a + d ≈ c + b → c ≈ infC → T₁ a b c d ≈ infC × T₂ a b c d ≈ infC
  topC {a} {b} {c} {d} h hc with sum-top {a} {d} (trans h (inL b hc))
  ... | inj₁ ha = topA h ha
  ... | inj₂ hd = inR _ (inL _ (top-mul hc hd)) , inL _ (inR _ (top-mul hd hd))

  topD : ∀ {a b c d} → a + d ≈ c + b → d ≈ infC → T₁ a b c d ≈ infC × T₂ a b c d ≈ infC
  topD {a} {b} {c} {d} h hd with sum-top {c} {b} (trans (sym h) (inR a hd))
  ... | inj₁ hc = topC h hc
  ... | inj₂ hb = topB h hb

  -- all four bounded: the cross sums S₁, S₂ (equal by a + d ≈ c + b), then cancel the bounded S₂
  S₁ S₂ : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣
  S₁ a b c d = (a + d) * (a + c) + (c + b) * (b + d)
  S₂ a b c d = (a + d) * (b + d) + (c + b) * (a + c)

  S-eq : ∀ {a b c d} → a + d ≈ c + b → S₁ a b c d ≈ S₂ a b c d
  S-eq {a} {b} {c} {d} h = trans (+-cong refl (*-cong (sym h) refl)) (trans (solve 4 (λ a b c d →
    (a :+ d) :* (a :+ c) :+ (a :+ d) :* (b :+ d) := (a :+ d) :* (b :+ d) :+ (a :+ d) :* (a :+ c)) refl a b c d)
    (+-cong refl (*-cong h refl)))

  key : ∀ a b c d → T₁ a b c d + S₂ a b c d ≈ T₂ a b c d + S₁ a b c d
  key a b c d = solve 4 (λ a b c d →
    ((a :* a :+ b :* b) :+ (c :* d :+ d :* c)) :+ ((a :+ d) :* (b :+ d) :+ (c :+ b) :* (a :+ c))
    := ((c :* c :+ d :* d) :+ (a :* b :+ b :* a)) :+ ((a :+ d) :* (a :+ c) :+ (c :+ b) :* (b :+ d))) refl a b c d

  S-bnd : ∀ {a b c d} → Bnd a → Bnd b → Bnd c → Bnd d → Bnd (S₂ a b c d)
  S-bnd {a} {b} {c} {d} ba bb bc bd = Is-+ {(a + d) * (b + d)} {(c + b) * (a + c)}
    (Is-* {a + d} {b + d} (Is-+ {a} {d} ba bd) (Is-+ {b} {d} bb bd))
    (Is-* {c + b} {a + c} (Is-+ {c} {b} bc bb) (Is-+ {a} {c} ba bc))

  fin-case : ∀ {a b c d} → Bnd a → Bnd b → Bnd c → Bnd d → a + d ≈ c + b → T₁ a b c d ≈ T₂ a b c d
  fin-case {a} {b} {c} {d} ba bb bc bd h = cancel-bnd {S₂ a b c d} (S-bnd ba bb bc bd)
    (trans (+-comm (S₂ a b c d) (T₁ a b c d)) (trans (key a b c d)
      (trans (+-cong refl (S-eq h)) (+-comm (T₂ a b c d) (S₂ a b c d)))))

  both : ∀ {a b c d} → T₁ a b c d ≈ infC × T₂ a b c d ≈ infC → T₁ a b c d ≈ T₂ a b c d
  both (x , y) = trans x (sym y)

  sq-alg : ∀ {a b c d} → a + d ≈ c + b → T₁ a b c d ≈ T₂ a b c d
  sq-alg {a} {b} {c} {d} h with lem₁ (Bnd a)
  ... | inj₂ na = both (topA h (not-bnd-top a na))
  ... | inj₁ ba with lem₁ (Bnd b)
  ...   | inj₂ nb = both (topB h (not-bnd-top b nb))
  ...   | inj₁ bb with lem₁ (Bnd c)
  ...     | inj₂ nc = both (topC h (not-bnd-top c nc))
  ...     | inj₁ bc with lem₁ (Bnd d)
  ...       | inj₂ nd = both (topD h (not-bnd-top d nd))
  ...       | inj₁ bd = fin-case ba bb bc bd h

  sq-cong : ∀ {X : QBS S} {f g : SgT X} → f ≐ g → (f *T f) ≐ (g *T g)
  sq-cong {X} {f} {g} e x = sq-alg {at⁺ f x} {at⁻ f x} {at⁺ g x} {at⁻ g x} (e x)
