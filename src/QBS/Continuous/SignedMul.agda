{-# OPTIONS --safe --without-K #-}

-- Products respect `≐` (plan 05, item 55b; helper for `RandomVectorLaw`; the twin of `SignedSq`).
--   * `mul-alg`: a + d ≈ c + b and u + z ≈ w + v give (a u + b v) + (c z + d w) ≈ (c w + d z) + (a v + b u) in [0, ∞],
--     including infinite values (f = (a, b), g = (c, d), f′ = (u, v), g′ = (w, z));
--   * `mul-cong`: f ≐ g and f′ ≐ g′ give f *T f′ ≐ g *T g′.
-- Route: all eight values bounded: cross-add S₂ = (a + d) v + (c + b) u + (u + z) d + (w + v) c to the two sides (they
-- differ by S₁ − S₂, S₁ ≈ S₂ by the hypotheses) and cancel the bounded S₂ (`cancel-bnd`).  Otherwise a side of a
-- hypothesis is ∞, so one of {a, d} and one of {c, b} is (`sum-top`); in each of the four combinations the two sides are
-- ∞·s plus a remainder (`rep`, distributivity), and `absorb` handles s ≈ 0 (the remainders agree, `top-pos`
-- gives ∞·s ≈ ∞ otherwise).  An infinite primed value is the same with the roles of f, g and f′, g′ exchanged.
module QBS.Continuous.SignedMul where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import QBS.Core
open import QBS.Continuous.Sample using (S)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (infC)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.InfAlg using (module InfAlg; module TopMulPos)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedSq using (module SignedSq)
open TopMulPos using (top-pos)

module SignedMul (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; +-comm; +-identityˡ; +-identityʳ; zeroʳ;
    distribˡ; ≤-trans; ≤-reflexive; ≤-antisym; ≤-+ʳ; 0-least; commutativeSemiring) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; finite)
  open SubSemiring finite using (Is-+; Is-*)
  open InfAlg lem₁ using (cancel-bnd; top-sum; not-bnd-top)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _≐_; _*T_)
  open SignedSq lem₁ using (sum-top; inL; inR)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  module _ (a b c d u v w z : ∣A∣) where
    T₁ T₂ S₁ S₂ : ∣A∣
    T₁ = (a * u + b * v) + (c * z + d * w)
    T₂ = (c * w + d * z) + (a * v + b * u)
    S₁ = ((a + d) * u + (c + b) * v) + ((u + z) * c + (w + v) * d)
    S₂ = ((a + d) * v + (c + b) * u) + ((u + z) * d + (w + v) * c)

  ----------------------------------------------------------------------------
  -- all values bounded

  key : ∀ a b c d u v w z → T₁ a b c d u v w z + S₂ a b c d u v w z ≈ T₂ a b c d u v w z + S₁ a b c d u v w z
  key a b c d u v w z = solve 8 (λ a b c d u v w z →
    ((a :* u :+ b :* v) :+ (c :* z :+ d :* w)) :+ (((a :+ d) :* v :+ (c :+ b) :* u) :+ ((u :+ z) :* d :+ (w :+ v) :* c))
    := ((c :* w :+ d :* z) :+ (a :* v :+ b :* u)) :+ (((a :+ d) :* u :+ (c :+ b) :* v) :+ ((u :+ z) :* c :+ (w :+ v) :* d)))
    refl a b c d u v w z

  S-eq : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → S₁ a b c d u v w z ≈ S₂ a b c d u v w z
  S-eq {a} {b} {c} {d} {u} {v} {w} {z} h h′ = trans (+-cong (+-cong (*-cong h refl) refl) (+-cong (*-cong h′ refl) refl))
    (trans (solve 6 (λ β β′ u v c d → (β :* u :+ β :* v) :+ (β′ :* c :+ β′ :* d)
        := (β :* v :+ β :* u) :+ (β′ :* d :+ β′ :* c)) refl (c + b) (w + v) u v c d)
      (sym (+-cong (+-cong (*-cong h refl) refl) (+-cong (*-cong h′ refl) refl))))

  S-bnd : ∀ {a b c d u v w z} → Bnd a → Bnd b → Bnd c → Bnd d → Bnd u → Bnd v → Bnd w → Bnd z →
    Bnd (S₂ a b c d u v w z)
  S-bnd {a} {b} {c} {d} {u} {v} {w} {z} ba bb bc bd bu bv bw bz = Is-+ {_} {_}
    (Is-+ {_} {_} (Is-* {_} {_} (Is-+ {a} {d} ba bd) bv) (Is-* {_} {_} (Is-+ {c} {b} bc bb) bu))
    (Is-+ {_} {_} (Is-* {_} {_} (Is-+ {u} {z} bu bz) bd) (Is-* {_} {_} (Is-+ {w} {v} bw bv) bc))

  fin-case : ∀ {a b c d u v w z} → Bnd a → Bnd b → Bnd c → Bnd d → Bnd u → Bnd v → Bnd w → Bnd z →
    a + d ≈ c + b → u + z ≈ w + v → T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  fin-case {a} {b} {c} {d} {u} {v} {w} {z} ba bb bc bd bu bv bw bz h h′ =
    cancel-bnd {S₂ a b c d u v w z} (S-bnd ba bb bc bd bu bv bw bz)
      (trans (+-comm (S₂ a b c d u v w z) _) (trans (key a b c d u v w z)
        (trans (+-cong refl (S-eq h h′)) (+-comm _ (S₂ a b c d u v w z)))))

  ----------------------------------------------------------------------------
  -- infinite values: ∞ · s plus a remainder

  -- x ≈ ∞ and y ≈ ∞ give x p + y q ≈ ∞ (p + q)
  rep : ∀ {x y p q} → x ≈ infC → y ≈ infC → x * p + y * q ≈ infC * (p + q)
  rep hx hy = trans (+-cong (*-cong hx refl) (*-cong hy refl)) (sym (distribˡ infC _ _))

  -- ∞ s + R₁ ≈ ∞ s + R₂ as soon as R₁ ≈ R₂ when s ≈ 0
  absorb : ∀ {s R₁ R₂} → (s ≈ 0# → R₁ ≈ R₂) → infC * s + R₁ ≈ infC * s + R₂
  absorb {s} {R₁} {R₂} f with lem₁ (s ≈ 0#)
  ... | inj₂ nz = trans (top-sum e R₁) (sym (top-sum e R₂))
    where e = top-pos (lemOf lem₁) s nz
  ... | inj₁ z0 = trans (+-cong e0 refl) (trans (+-identityˡ R₁)
    (trans (f z0) (sym (trans (+-cong e0 refl) (+-identityˡ R₂)))))
    where e0 = trans (*-cong refl z0) (zeroʳ infC)

  z-sum : ∀ {x y} → x + y ≈ 0# → x ≈ 0# × y ≈ 0#
  z-sum {x} {y} h = ≤-antisym {x} {0#} (≤-trans (≤-+ʳ {x} {y}) (≤-reflexive h)) 0-least ,
    ≤-antisym {y} {0#} (≤-trans (≤-+ʳ {y} {x}) (≤-trans (≤-reflexive (+-comm y x)) (≤-reflexive h))) 0-least

  -- a sum of two products with vanishing second factors vanishes
  z2 : ∀ {x y p q} → p ≈ 0# → q ≈ 0# → x * p + y * q ≈ 0#
  z2 {x} {y} hp hq = trans (+-cong (trans (*-cong refl hp) (zeroʳ x)) (trans (*-cong refl hq) (zeroʳ y))) (+-identityˡ 0#)

  -- u + z ≈ w + v with u ≈ 0 and v ≈ 0 gives z ≈ w, and so on
  cancel0 : ∀ {p x y q} → p ≈ 0# → q ≈ 0# → p + x ≈ y + q → x ≈ y
  cancel0 {p} {x} {y} {q} hp hq h = trans (sym (trans (+-cong hp refl) (+-identityˡ x)))
    (trans h (trans (+-cong refl hq) (trans (+-comm y 0#) (+-identityˡ y))))

  -- the common shape of the four infinite cases
  case-gen : ∀ {a b c d u v w z M₁ M₂ R₁ R₂ s} →
    T₁ a b c d u v w z ≈ M₁ + R₁ → T₂ a b c d u v w z ≈ M₂ + R₂ →
    M₁ ≈ infC * s → M₂ ≈ infC * s → (s ≈ 0# → R₁ ≈ R₂) → T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  case-gen e₁ e₂ m₁ m₂ f = trans e₁ (trans (+-cong m₁ refl) (trans (absorb f) (sym (trans e₂ (+-cong m₂ refl)))))

  cancel0′ : ∀ {x y p q} → p ≈ 0# → q ≈ 0# → x + p ≈ q + y → x ≈ y
  cancel0′ {x} {y} {p} {q} hp hq h = trans (sym (trans (+-cong refl hp) (+-identityʳ x)))
    (trans h (trans (+-cong hq refl) (+-identityˡ y)))

  -- a ≈ ∞ and c ≈ ∞
  core-ac : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → a ≈ infC → c ≈ infC →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  core-ac {a} {b} {c} {d} {u} {v} {w} {z} h h′ ha hc = case-gen {s = u + z}
    (solve 8 (λ a b c d u v w z → (a :* u :+ b :* v) :+ (c :* z :+ d :* w) := (a :* u :+ c :* z) :+ (b :* v :+ d :* w))
      refl a b c d u v w z)
    (solve 8 (λ a b c d u v w z → (c :* w :+ d :* z) :+ (a :* v :+ b :* u) := (c :* w :+ a :* v) :+ (d :* z :+ b :* u))
      refl a b c d u v w z)
    (rep ha hc) (trans (rep hc ha) (*-cong refl (sym h′)))
    (λ s0 → trans (z2 (proj₂ (z-sum (trans (sym h′) s0))) (proj₁ (z-sum (trans (sym h′) s0))))
      (sym (z2 (proj₂ (z-sum s0)) (proj₁ (z-sum s0)))))

  -- a ≈ ∞ and b ≈ ∞
  core-ab : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → a ≈ infC → b ≈ infC →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  core-ab {a} {b} {c} {d} {u} {v} {w} {z} h h′ ha hb = case-gen {s = u + v} refl
    (solve 8 (λ a b c d u v w z → (c :* w :+ d :* z) :+ (a :* v :+ b :* u) := (a :* v :+ b :* u) :+ (c :* w :+ d :* z))
      refl a b c d u v w z)
    (rep ha hb) (trans (rep ha hb) (*-cong refl (+-comm v u))) f
    where
      zw : u + v ≈ 0# → z ≈ w
      zw s0 = cancel0 (proj₁ (z-sum s0)) (proj₂ (z-sum s0)) h′
      f : u + v ≈ 0# → c * z + d * w ≈ c * w + d * z
      f s0 = trans (+-cong (*-cong refl (zw s0)) refl) (sym (+-cong refl (*-cong refl (zw s0))))

  -- d ≈ ∞ and c ≈ ∞
  core-dc : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → d ≈ infC → c ≈ infC →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  core-dc {a} {b} {c} {d} {u} {v} {w} {z} h h′ hd hc = case-gen {s = z + w}
    (solve 8 (λ a b c d u v w z → (a :* u :+ b :* v) :+ (c :* z :+ d :* w) := (c :* z :+ d :* w) :+ (a :* u :+ b :* v))
      refl a b c d u v w z)
    refl (rep hc hd) (trans (rep hc hd) (*-cong refl (+-comm w z))) f
    where
      uv : z + w ≈ 0# → u ≈ v
      uv s0 = cancel0′ (proj₁ (z-sum s0)) (proj₂ (z-sum s0)) h′
      f : z + w ≈ 0# → a * u + b * v ≈ a * v + b * u
      f s0 = trans (+-cong (*-cong refl (uv s0)) refl) (sym (+-cong refl (*-cong refl (uv s0))))

  -- d ≈ ∞ and b ≈ ∞
  core-db : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → d ≈ infC → b ≈ infC →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  core-db {a} {b} {c} {d} {u} {v} {w} {z} h h′ hd hb = case-gen {s = v + w}
    (solve 8 (λ a b c d u v w z → (a :* u :+ b :* v) :+ (c :* z :+ d :* w) := (b :* v :+ d :* w) :+ (a :* u :+ c :* z))
      refl a b c d u v w z)
    (solve 8 (λ a b c d u v w z → (c :* w :+ d :* z) :+ (a :* v :+ b :* u) := (d :* z :+ b :* u) :+ (c :* w :+ a :* v))
      refl a b c d u v w z)
    (rep hb hd) (trans (rep hd hb) (*-cong refl (trans (+-comm z u) (trans h′ (+-comm w v)))))
    (λ s0 → trans (z2 (proj₁ (z-sum (trans h′ (trans (+-comm w v) s0))))
      (proj₂ (z-sum (trans h′ (trans (+-comm w v) s0)))))
      (sym (z2 (proj₂ (z-sum s0)) (proj₁ (z-sum s0)))))

  ----------------------------------------------------------------------------
  -- the four combinations, the exchange of the two factors, and the bounded remainder

  Inf : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  Inf a d c b = (a ≈ infC ⊎ d ≈ infC) ⊎ (c ≈ infC ⊎ b ≈ infC)

  pairs : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v →
    (a ≈ infC ⊎ d ≈ infC) → (c ≈ infC ⊎ b ≈ infC) →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  pairs h h′ (inj₁ ha) (inj₁ hc) = core-ac h h′ ha hc
  pairs h h′ (inj₁ ha) (inj₂ hb) = core-ab h h′ ha hb
  pairs h h′ (inj₂ hd) (inj₁ hc) = core-dc h h′ hd hc
  pairs h h′ (inj₂ hd) (inj₂ hb) = core-db h h′ hd hb

  e-inf : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → Inf a d c b →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  e-inf {a} {b} {c} {d} h h′ (inj₁ (inj₁ ha)) = pairs h h′ (inj₁ ha) (sum-top (trans (sym h) (inL d ha)))
  e-inf {a} {b} {c} {d} h h′ (inj₁ (inj₂ hd)) = pairs h h′ (inj₂ hd) (sum-top (trans (sym h) (inR a hd)))
  e-inf {a} {b} {c} {d} h h′ (inj₂ (inj₁ hc)) = pairs h h′ (sum-top (trans h (inL b hc))) (inj₁ hc)
  e-inf {a} {b} {c} {d} h h′ (inj₂ (inj₂ hb)) = pairs h h′ (sum-top (trans h (inR c hb))) (inj₂ hb)

  -- exchanging (f, g) with (f′, g′)
  swap-eq : ∀ a b c d u v w z → T₁ a b c d u v w z ≈ T₁ u v w z a b c d × T₂ a b c d u v w z ≈ T₂ u v w z a b c d
  swap-eq a b c d u v w z =
    solve 8 (λ a b c d u v w z → (a :* u :+ b :* v) :+ (c :* z :+ d :* w) := (u :* a :+ v :* b) :+ (w :* d :+ z :* c)) refl
      a b c d u v w z ,
    solve 8 (λ a b c d u v w z → (c :* w :+ d :* z) :+ (a :* v :+ b :* u) := (w :* c :+ z :* d) :+ (u :* b :+ v :* a)) refl
      a b c d u v w z

  mixed : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → Inf u z w v →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  mixed {a} {b} {c} {d} {u} {v} {w} {z} h h′ x =
    trans (proj₁ (swap-eq a b c d u v w z)) (trans (e-inf h′ h x) (sym (proj₂ (swap-eq a b c d u v w z))))

  bnd-of : ∀ x → (x ≈ infC → ⊥) → Bnd x
  bnd-of x ne with lem₁ (Bnd x)
  ... | inj₁ bx = bx
  ... | inj₂ nb = ⊥-elim (ne (not-bnd-top x nb))

  bnd4 : ∀ {a d c b} → (Inf a d c b → ⊥) → Bnd a × Bnd d × Bnd c × Bnd b
  bnd4 {a} {d} {c} {b} ne = bnd-of a (λ x → ne (inj₁ (inj₁ x))) , bnd-of d (λ x → ne (inj₁ (inj₂ x))) ,
    bnd-of c (λ x → ne (inj₂ (inj₁ x))) , bnd-of b (λ x → ne (inj₂ (inj₂ x)))

  fin-from : ∀ {a b c d u v w z} → (Inf a d c b → ⊥) → (Inf u z w v → ⊥) → a + d ≈ c + b → u + z ≈ w + v →
    T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  fin-from n n′ h h′ with bnd4 n | bnd4 n′
  ... | (ba , bd , bc , bb) | (bu , bz , bw , bv) = fin-case ba bb bc bd bu bv bw bz h h′

  mul-alg : ∀ {a b c d u v w z} → a + d ≈ c + b → u + z ≈ w + v → T₁ a b c d u v w z ≈ T₂ a b c d u v w z
  mul-alg {a} {b} {c} {d} {u} {v} {w} {z} h h′ with lem₁ (Inf a d c b) | lem₁ (Inf u z w v)
  ... | inj₁ x | _ = e-inf h h′ x
  ... | inj₂ n | inj₁ y = mixed h h′ y
  ... | inj₂ n | inj₂ n′ = fin-from n n′ h h′

  mul-cong : ∀ {X : QBS S} {f g f′ g′ : SgT X} → f ≐ g → f′ ≐ g′ → (f *T f′) ≐ (g *T g′)
  mul-cong {X} {f} {g} {f′} {g′} e e′ x =
    mul-alg {at⁺ f x} {at⁻ f x} {at⁺ g x} {at⁻ g x} {at⁺ f′ x} {at⁻ f′ x} {at⁺ g′ x} {at⁻ g′ x}
      (e x) (e′ x)
