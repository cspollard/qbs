{-# OPTIONS --safe --without-K #-}

-- A derivative-free fundamental theorem of calculus in tail form (part 1: the algebra).
--
-- On a dyadic piece [a, b], b = a + ½ⁿ, with piece integral D and a certificate `G b + ½ⁿ h(b) ≤ G a ≤ G b + ½ⁿ h(a)`
-- (the additive form of ½ⁿ h(b) ≤ G a − G b ≤ ½ⁿ h(a)), the pair `Up`/`Lo` below says that D and the drop of G agree up to
-- the error ε (h a − h b):
--   Up D Ga Gb ha hb ε :  (D + Gb) + ε hb ≤ Ga + ε ha        Lo D Ga Gb ha hb ε :  Ga + ε hb ≤ (D + Gb) + ε ha.
-- A piece splits into two halves with the same ε (and half the width), and the claims for the halves add up to the claim
-- for the whole after cancelling the bounded middle term `G m + ε h(m)` (`cancel≤P`).  Over an abstract Archimedean
-- ω-semiring (the solver is slow on the concrete cut semiring).
module QBS.Analysis.TailFTC where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Series using (module Series)

module AlgT (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; arch; cancel≤; hp; hp-≤; hp-double; half-twice)
  open Series A using (psum; ∑ᶠ; ∑ᶠ-lub; psum≤∑ᶠ)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the dyadic pieces [a, a + ½ⁿ] of [0,1]: [0,1] itself, and the left and right halves of a piece

  data Dy : ℕ → ∣A∣ → Set₁ where
    dy0 : Dy 0 0#
    dyL : ∀ {n a} → Dy n a → Dy (suc n) a
    dyR : ∀ {n a} → Dy n a → Dy (suc n) (a + hp (suc n))

  hp≤1 : ∀ n → hp n ≤ 1#
  hp≤1 zero = ≤-refl
  hp≤1 (suc n) = ≤-trans (hp-≤ n) (hp≤1 n)

  hpp≤1 : ∀ n d → hp n * hp d ≤ 1#
  hpp≤1 n d = ≤-trans (*-mono (hp n) (hp≤1 d)) (≤-trans (≤-reflexive (*-identityʳ (hp n))) (hp≤1 n))

  dy-bound : ∀ {n a} → Dy n a → a + hp n ≤ 1#
  dy-bound dy0 = ≤-reflexive (+-identityˡ 1#)
  dy-bound (dyL {n} d) = ≤-trans (+-mono ≤-refl (hp-≤ n)) (dy-bound d)
  dy-bound (dyR {n} {a} d) = ≤-trans (≤-reflexive (trans (+-assoc a _ _) (+-cong refl (hp-double n)))) (dy-bound d)

  -- the right half's right end is the whole piece's right end
  dy-end : ∀ n a b → b ≈ a + hp n → b ≈ (a + hp (suc n)) + hp (suc n)
  dy-end n a b e = trans e (trans (+-cong refl (sym (hp-double n))) (sym (+-assoc a _ _)))

  -- the sample points inside the halves: if y = ½ + ½ x (right) or y = ½ x (left) then a + ½ⁿ y is the left end plus ½ⁿ⁺¹ x
  ptL : ∀ n a x y → y ≈ half * x → a + hp n * y ≈ a + hp (suc n) * x
  ptL n a x y e = trans (+-cong refl (*-cong refl e))
    (+-cong refl (solve 3 (λ p h x′ → p :* (h :* x′) := (h :* p) :* x′) refl (hp n) half x))

  ptR : ∀ n a x y → y ≈ half + half * x → a + hp n * y ≈ (a + hp (suc n)) + hp (suc n) * x
  ptR n a x y e = trans (+-cong refl (*-cong refl e))
    (solve 4 (λ a′ p h x′ → a′ :+ p :* (h :+ h :* x′) := (a′ :+ h :* p) :+ (h :* p) :* x′) refl a (hp n) half x)

  -- the piece integral of a function is the sum of the halves, and the error scales
  Dsplit : ∀ n I T F → I ≈ half * T + half * F → hp n * I ≈ hp (suc n) * F + hp (suc n) * T
  Dsplit n I T F e = trans (*-cong refl e)
    (solve 4 (λ p h t f → p :* (h :* t :+ h :* f) := (h :* p) :* f :+ (h :* p) :* t) refl (hp n) half T F)

  eps : ∀ n d → hp n * hp (suc d) ≈ hp (suc n) * hp d
  eps n d = solve 3 (λ p h q → p :* (h :* q) := (h :* p) :* q) refl (hp n) half (hp d)

  ----------------------------------------------------------------------------
  -- the claims

  Up : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  Up D Ga Gb ha hb ε = (D + Gb) + ε * hb ≤ Ga + ε * ha

  Lo : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → Set₁
  Lo D Ga Gb ha hb ε = Ga + ε * hb ≤ (D + Gb) + ε * ha

  Up-cong : ∀ {D D′ Ga Gb ha hb ε ε′} → D ≈ D′ → ε ≈ ε′ → Up D Ga Gb ha hb ε → Up D′ Ga Gb ha hb ε′
  Up-cong eD eε = ≤-resp (+-cong (+-cong eD refl) (*-cong eε refl)) (+-cong refl (*-cong eε refl))

  Lo-cong : ∀ {D D′ Ga Gb ha hb ε ε′} → D ≈ D′ → ε ≈ ε′ → Lo D Ga Gb ha hb ε → Lo D′ Ga Gb ha hb ε′
  Lo-cong eD eε = ≤-resp (+-cong refl (*-cong eε refl)) (+-cong (+-cong eD refl) (*-cong eε refl))

  ----------------------------------------------------------------------------
  -- cancellation of elements bounded by 2ᵏ

  P : ℕ → ∣A∣
  P zero = 1#
  P (suc k) = P k + P k

  P≥1 : ∀ k → 1# ≤ P k
  P≥1 zero = ≤-refl
  P≥1 (suc k) = ≤-trans (P≥1 k) ≤-+ʳ

  open HalfOrder A R using (hm)

  cancel≤P : ∀ k {a x y} → a ≤ P k → a + x ≤ a + y → x ≤ y
  cancel≤P zero le e = cancel≤ le e
  cancel≤P (suc k) {a} {x} {y} le e =
    ≤-trans (≤-reflexive (sym (hm x))) (≤-trans (+-mono hxy hxy) (≤-reflexive (hm y)))
    where
    small : half * a ≤ P k
    small = ≤-trans (*-mono half le) (≤-reflexive (half-twice (P k)))
    e′ : half * a + half * x ≤ half * a + half * y
    e′ = ≤-resp (distribˡ half a x) (distribˡ half a y) (*-mono half e)
    hxy : half * x ≤ half * y
    hxy = cancel≤P k small e′

  -- g ≤ 2ᴷ, t ≤ 1, h ≤ 1 give g + t h ≤ 2ᴷ⁺¹
  bndX : ∀ {K g t h} → g ≤ P K → t ≤ 1# → h ≤ 1# → g + t * h ≤ P (suc K)
  bndX {K} {g} {t} {h} gb tb hb =
    ≤-trans (+-mono gb (≤-trans (*-mono t hb) (≤-trans (≤-reflexive (*-identityʳ t)) tb))) (+-mono ≤-refl (P≥1 K))

  ----------------------------------------------------------------------------
  -- the base case (a single piece) and the splitting of a piece

  base-up : ∀ {D Ga Gb ha hb w} → D ≤ w * ha → Gb + w * hb ≤ Ga → Up D Ga Gb ha hb w
  base-up {D} {Ga} {Gb} {ha} {hb} {w} dle cle =
    ≤-trans (≤-reflexive (+-assoc D Gb (w * hb))) (≤-trans (+-mono dle cle) (≤-reflexive (+-comm (w * ha) Ga)))

  base-lo : ∀ {D Ga Gb ha hb w} → w * hb ≤ D → Ga ≤ Gb + w * ha → Lo D Ga Gb ha hb w
  base-lo {D} {Ga} {Gb} {ha} {hb} {w} dle cle = ≤-trans (+-mono cle dle)
    (≤-reflexive (solve 3 (λ g x d → (g :+ x) :+ d := (d :+ g) :+ x) refl Gb (w * ha) D))

  up-step : ∀ {k DL DR Ga Gm Gb ha hm hb t} → Gm + t * hm ≤ P k →
    Up DL Ga Gm ha hm t → Up DR Gm Gb hm hb t → Up (DL + DR) Ga Gb ha hb t
  up-step {k} {DL} {DR} {Ga} {Gm} {Gb} {ha} {hm} {hb} {t} bx uL uR =
    cancel≤P k bx (≤-resp e1 (+-comm _ _) (+-mono uL uR))
    where
    e1 : ((DL + Gm) + t * hm) + ((DR + Gb) + t * hb) ≈ (Gm + t * hm) + (((DL + DR) + Gb) + t * hb)
    e1 = solve 7 (λ dl g x m dr gb y → ((dl :+ g) :+ x :* m) :+ ((dr :+ gb) :+ x :* y)
                                      := (g :+ x :* m) :+ (((dl :+ dr) :+ gb) :+ x :* y)) refl DL Gm t hm DR Gb hb

  lo-step : ∀ {k DL DR Ga Gm Gb ha hm hb t} → Gm + t * hm ≤ P k →
    Lo DL Ga Gm ha hm t → Lo DR Gm Gb hm hb t → Lo (DL + DR) Ga Gb ha hb t
  lo-step {k} {DL} {DR} {Ga} {Gm} {Gb} {ha} {hm} {hb} {t} bx lL lR =
    cancel≤P k bx (≤-resp e1 e2 (+-mono lL lR))
    where
    e1 : (Ga + t * hm) + (Gm + t * hb) ≈ (Gm + t * hm) + (Ga + t * hb)
    e1 = solve 6 (λ ga x m g y b → (ga :+ x :* m) :+ (g :+ x :* b) := (g :+ x :* m) :+ (ga :+ x :* b)) refl Ga t hm Gm t hb
    e2 : ((DL + Gm) + t * ha) + ((DR + Gb) + t * hm) ≈ (Gm + t * hm) + (((DL + DR) + Gb) + t * ha)
    e2 = solve 7 (λ dl g x a dr gb m → ((dl :+ g) :+ x :* a) :+ ((dr :+ gb) :+ x :* m)
                                      := (g :+ x :* m) :+ (((dl :+ dr) :+ gb) :+ x :* a)) refl DL Gm t ha DR Gb hm

  ----------------------------------------------------------------------------
  -- the conclusion: errors ε = ½ᵈ → 0 squeeze the integral between the two bounds

  squeeze : ∀ {I g₀ g₁ h₀ h₁} → h₀ ≤ 1# →
    (∀ d → (I + g₁) + hp d * h₁ ≤ g₀ + hp d * h₀) → (∀ d → g₀ + hp d * h₁ ≤ (I + g₁) + hp d * h₀) → I + g₁ ≈ g₀
  squeeze {I} {g₀} {g₁} {h₀} {h₁} h0 up lo = ≤-antisym (arch (λ d → ≤-trans ≤-+ʳ (≤-trans (up d) (+-mono ≤-refl (tail d)))))
    (arch (λ d → ≤-trans ≤-+ʳ (≤-trans (lo d) (+-mono ≤-refl (tail d)))))
    where
    tail : ∀ d → hp d * h₀ ≤ hp d
    tail d = ≤-trans (*-mono (hp d) h0) (≤-reflexive (*-identityʳ (hp d)))

  ----------------------------------------------------------------------------
  -- the certificate for the exponential: from y e = 1 and 1 + w ≤ e ≤ 1 + w + w², with y = e^{−w}, the facts
  -- y (1 + w) ≤ 1 ≤ y + w give, for p = e^{−a}, `p y + w (p y) ≤ p ≤ p y + w p` (e^{−(a+w)} = p y)

  exp-facts : ∀ {y w e} → y * e ≈ 1# → 1# + w ≤ e → e ≤ 1# + (w + w * w) → (y + w * y ≤ 1#) × (1# ≤ y + w)
  exp-facts {y} {w} {e} ye lo hi = b , c
    where
    b : y + w * y ≤ 1#
    b = ≤-trans (≤-reflexive (solve 2 (λ y′ w′ → y′ :+ w′ :* y′ := y′ :* (con 1 :+ w′)) refl y w))
          (≤-trans (*-mono y lo) (≤-reflexive ye))
    c : 1# ≤ y + w
    c = ≤-trans (≤-reflexive (sym ye)) (≤-trans (*-mono y hi)
          (≤-trans (≤-reflexive (solve 2 (λ y′ w′ → y′ :* (con 1 :+ (w′ :+ w′ :* w′)) := y′ :+ w′ :* (y′ :+ w′ :* y′)) refl y w))
          (≤-trans (+-mono ≤-refl (*-mono w b)) (≤-reflexive (+-cong refl (*-identityʳ w))))))

  exp-cert : ∀ {p y w} → y + w * y ≤ 1# → 1# ≤ y + w → (p * y + w * (p * y) ≤ p) × (p ≤ p * y + w * p)
  exp-cert {p} {y} {w} b c =
    ≤-trans (≤-reflexive (solve 3 (λ p′ y′ w′ → p′ :* y′ :+ w′ :* (p′ :* y′) := p′ :* (y′ :+ w′ :* y′)) refl p y w))
      (≤-trans (*-mono p b) (≤-reflexive (*-identityʳ p)))
    , ≤-trans (≤-reflexive (sym (*-identityʳ p))) (≤-trans (*-mono p c)
        (≤-reflexive (solve 3 (λ p′ y′ w′ → p′ :* (y′ :+ w′) := p′ :* y′ :+ w′ :* p′) refl p y w)))

  ----------------------------------------------------------------------------
  -- the half-line: summing the unit-interval identities `Iₙ + g (n+1) = g n` over n

  tele : ∀ (I g : ℕ → ∣A∣) → (∀ n → I n + g (suc n) ≈ g n) → ∀ N → psum I N + g N ≈ g 0
  tele I g e zero = +-identityˡ _
  tele I g e (suc N) = trans (+-assoc (psum I N) (I N) (g (suc N))) (trans (+-cong refl (e N)) (tele I g e N))

  -- the sum is at most g 0, and equals it when g tends to 0
  tail-le : ∀ (I g : ℕ → ∣A∣) → (∀ n → I n + g (suc n) ≈ g n) → ∑ᶠ I ≤ g 0
  tail-le I g e = ∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-reflexive (tele I g e N)))

  tail-eq : ∀ (I g : ℕ → ∣A∣) → (∀ n → I n + g (suc n) ≈ g n) → (∀ m → Σ ℕ (λ N → g N ≤ hp m)) → ∑ᶠ I ≈ g 0
  tail-eq I g e tl = ≤-antisym (tail-le I g e) (arch (λ m → go m (tl m)))
    where
    go : ∀ m → Σ ℕ (λ N → g N ≤ hp m) → g 0 ≤ ∑ᶠ I + hp m
    go m (N , gb) = ≤-trans (≤-reflexive (sym (tele I g e N))) (+-mono (psum≤∑ᶠ I N) gb)
