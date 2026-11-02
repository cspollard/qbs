{-# OPTIONS --safe --without-K #-}

-- A certificate calculus for the tail FTC (part 2: the product rule), over an abstract Archimedean ω-semiring.
--
-- From `D M c G₁ h₁ k₁` and `D M c G₂ h₂ k₂` (`Analysis/Deriv`) the product G = G₁G₂ has the data
--     h = h₁G₂ + G₁h₂,    k = k₁G₂ + G₁k₂        (so G′ = k − h: (G₁G₂)′ = G₁′G₂ + G₁G₂′ with G′ = k − h),
-- with the explicit constant `Cp c`.  There is no cancellation: write X = G(a+w) + w h(a) and Y = G a + w k(a), so the
-- hypotheses are X ≤ Y + e, Y ≤ X + e (e = w² c), and the product of the factors' certificates, multiplied out,
--     X₁X₂ ≤ (Y₁ + e)(Y₂ + e)    and    Y₁Y₂ ≤ (X₁ + e)(X₂ + e),
-- gives the certificate of the product up to w² times a bracket, once the cross terms h₁G₂(a + w) are moved back to
-- h₁G₂(a) with the Lipschitz bound of G (`Gup`, `Gdn`: constant c + c) at a cost w² (c + c) h₁.  Every bracket is
-- bounded by `Cc c`, the Lipschitz constants of h and k by `L₁ c + L₁ c`, and everything by `Cp c`.
-- `DFprod` is the rule on the wrapper `Deriv`: the constants of the factors are added (`Dmono`) and finiteness follows.
module QBS.Analysis.DerivProd where

import Level as L
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Analysis.Deriv using (module AlgD)

module AlgDP (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open AlgP A R using (*-monoʳ; *-mono₂)
  open AlgD A R
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  ----------------------------------------------------------------------------
  -- the constants

  -- Lipschitz constant of a product of a Lipschitz-c function and a Lipschitz-(c+c) one, bounded by c
  L₁ : ∣A∣ → ∣A∣
  L₁ c = (c * (c + c)) + ((c * c) + (c * (c + c)))

  -- the bracket of the certificate
  Cc : ∣A∣ → ∣A∣
  Cc c = (c * c) + ((c * ((c + c) + (c + c))) + ((c * c) + ((c + c) * (c + c))))

  -- the constant of the product
  Cp : ∣A∣ → ∣A∣
  Cp c = (Cc c + (L₁ c + L₁ c)) + (c * c + c * c)

  Fin-Cp : ∀ {c} → Fin c → Fin (Cp c)
  Fin-Cp f = Fin-+ (Fin-+ fCc (Fin-+ fL fL)) (Fin-+ fcc fcc)
    where
    fd = Fin-+ f f
    fcc = Fin-* f f
    fcd = Fin-* f fd
    fL = Fin-+ fcd (Fin-+ fcc fcd)
    fCc = Fin-+ fcc (Fin-+ (Fin-* f (Fin-+ fd fd)) (Fin-+ fcc (Fin-* fd fd)))

  ----------------------------------------------------------------------------
  -- the pointwise Lipschitz bound of a product

  lipP : ∀ {u′ u g′ g w c} → w ≤ 1# → u′ ≤ u + w * c → g′ ≤ g + w * (c + c) → u ≤ c → g ≤ c → u′ * g′ ≤ u * g + w * L₁ c
  lipP {u′} {u} {g′} {g} {w} {c} w1 hu hg ub gb =
    ≤-trans (*-mono₂ hu hg)
      (≤-trans (≤-reflexive (solve 5 (λ u₀ g₀ w₀ c₀ d₀ → (u₀ :+ w₀ :* c₀) :* (g₀ :+ w₀ :* d₀)
          := u₀ :* g₀ :+ w₀ :* (u₀ :* d₀ :+ (c₀ :* g₀ :+ w₀ :* (c₀ :* d₀)))) refl u g w c (c + c)))
        (+-mono ≤-refl (*-mono w (+-mono (*-monoʳ (c + c) ub) (+-mono (*-mono c gb) (wle w1 (c * (c + c))))))))

  twoL : ∀ x y w l → (x + w * l) + (y + w * l) ≈ (x + y) + w * (l + l)
  twoL x y w l = solve 4 (λ x′ y′ w′ l′ → (x′ :+ w′ :* l′) :+ (y′ :+ w′ :* l′) := (x′ :+ y′) :+ w′ :* (l′ :+ l′)) refl x y w l

  module Lip {M c : ∣A∣} {G₁ h₁ k₁ G₂ h₂ k₂ : ∣A∣ → ∣A∣} (d₁ : D M c G₁ h₁ k₁) (d₂ : D M c G₂ h₂ k₂)
    {u₁ u₂ : ∣A∣ → ∣A∣} (b₁ : Bnd M c u₁) (b₂ : Bnd M c u₂)
    (U₁ : LpU M c u₁) (D₁ : LpD M c u₁) (U₂ : LpU M c u₂) (D₂ : LpD M c u₂) where
    private
      a≤M : ∀ {a w} → a + w ≤ M → a ≤ M
      a≤M aw = ≤-trans ≤-+ʳ aw

    P-up : LpU M (L₁ c + L₁ c) (λ x → u₁ x * G₂ x + G₁ x * u₂ x)
    P-up {a} {w} aw w1 = ≤-trans
      (+-mono (lipP w1 (U₁ aw w1) (Gup d₂ aw w1) (b₁ (a≤M aw)) (D-bG d₂ (a≤M aw)))
        (≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (lipP w1 (U₂ aw w1) (Gup d₁ aw w1) (b₂ (a≤M aw)) (D-bG d₁ (a≤M aw)))
          (+-mono (≤-reflexive (*-comm _ _)) ≤-refl))))
      (≤-reflexive (twoL _ _ w (L₁ c)))

    P-dn : LpD M (L₁ c + L₁ c) (λ x → u₁ x * G₂ x + G₁ x * u₂ x)
    P-dn {a} {w} aw w1 = ≤-trans
      (+-mono (lipP w1 (D₁ aw w1) (Gdn d₂ aw w1) (b₁ aw) (D-bG d₂ aw))
        (≤-trans (≤-reflexive (*-comm _ _)) (≤-trans (lipP w1 (D₂ aw w1) (Gdn d₁ aw w1) (b₂ aw) (D-bG d₁ aw))
          (+-mono (≤-reflexive (*-comm _ _)) ≤-refl))))
      (≤-reflexive (twoL _ _ w (L₁ c)))

  ----------------------------------------------------------------------------
  -- the pointwise certificate of a product

  -- the bracket of the certificate, and its bound by `Cc c`
  Br : ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣ → ∣A∣
  Br c w m y₁ y₂ hs = m + (c * (y₁ + y₂) + ((w * w) * (c * c) + (c + c) * hs))

  Bbound : ∀ {w c m Y₁ Y₂ hs} → w ≤ 1# → m ≤ c * c → Y₁ ≤ c + c → Y₂ ≤ c + c → hs ≤ c + c → Br c w m Y₁ Y₂ hs ≤ Cc c
  Bbound {w} {c} w1 mb y1 y2 hb = +-mono mb (+-mono (*-mono c (+-mono y1 y2))
    (+-mono (≤-trans (*-monoʳ (c * c) (ww≤1 w1)) (≤-reflexive (*-identityˡ _))) (*-mono (c + c) hb)))

  -- g + w q ≤ c + c from g ≤ c, q ≤ c
  Xb : ∀ {w c g q} → w ≤ 1# → g ≤ c → q ≤ c → g + w * q ≤ c + c
  Xb w1 gb qb = +-mono gb (≤-trans (wle w1 _) qb)

  ----------------------------------------------------------------------------
  -- the first certificate: X₁X₂ ≤ (Y₁ + e)(Y₂ + e), with the cross terms moved back to the point a

  ct1a : ∀ {g₁ g₁′ g₂ g₂′ h₁ h₂ w c} → g₁ ≤ g₁′ + w * (c + c) → g₂ ≤ g₂′ + w * (c + c) →
    (g₁′ * g₂′) + w * (h₁ * g₂ + g₁ * h₂) ≤ (g₁′ + w * h₁) * (g₂′ + w * h₂) + (w * w) * ((c + c) * (h₁ + h₂))
  ct1a {g₁} {g₁′} {g₂} {g₂′} {h₁} {h₂} {w} {c} gd₁ gd₂ =
    ≤-trans (+-mono ≤-refl (*-mono w (+-mono (*-mono h₁ gd₂) (*-monoʳ h₂ gd₁)))) (≤-trans ≤-+ʳ (≤-reflexive eqB))
    where
    eqB : (g₁′ * g₂′ + w * (h₁ * (g₂′ + w * (c + c)) + (g₁′ + w * (c + c)) * h₂)) + (w * w) * (h₁ * h₂)
      ≈ (g₁′ + w * h₁) * (g₂′ + w * h₂) + (w * w) * ((c + c) * (h₁ + h₂))
    eqB = solve 6 (λ a b p q w₀ d₀ → (a :* b :+ w₀ :* (p :* (b :+ w₀ :* d₀) :+ (a :+ w₀ :* d₀) :* q)) :+ (w₀ :* w₀) :* (p :* q)
      := (a :+ w₀ :* p) :* (b :+ w₀ :* q) :+ (w₀ :* w₀) :* (d₀ :* (p :+ q))) refl g₁′ g₂′ h₁ h₂ w (c + c)

  eq1c : ∀ g₁ g₂ h₁ h₂ k₁ k₂ w c →
    ((g₁ + w * k₁) + (w * w) * c) * ((g₂ + w * k₂) + (w * w) * c) + (w * w) * ((c + c) * (h₁ + h₂))
    ≈ ((g₁ * g₂) + w * (k₁ * g₂ + g₁ * k₂)) + (w * w) * Br c w (k₁ * k₂) (g₁ + w * k₁) (g₂ + w * k₂) (h₁ + h₂)
  eq1c g₁ g₂ h₁ h₂ k₁ k₂ w c = solve 8 (λ a b r s p q w₀ c₀ →
      ((a :+ w₀ :* p) :+ (w₀ :* w₀) :* c₀) :* ((b :+ w₀ :* q) :+ (w₀ :* w₀) :* c₀) :+ (w₀ :* w₀) :* ((c₀ :+ c₀) :* (r :+ s))
    := (a :* b :+ w₀ :* (p :* b :+ a :* q)) :+ (w₀ :* w₀) :* (p :* q :+ (c₀ :* ((a :+ w₀ :* p) :+ (b :+ w₀ :* q))
      :+ ((w₀ :* w₀) :* (c₀ :* c₀) :+ (c₀ :+ c₀) :* (r :+ s))))) refl g₁ g₂ h₁ h₂ k₁ k₂ w c

  ct1 : ∀ {g₁ g₁′ g₂ g₂′ h₁ h₂ k₁ k₂ w c} → w ≤ 1# → g₁ ≤ c → g₂ ≤ c → h₁ ≤ c → h₂ ≤ c → k₁ ≤ c → k₂ ≤ c →
    g₁ ≤ g₁′ + w * (c + c) → g₂ ≤ g₂′ + w * (c + c) →
    g₁′ + w * h₁ ≤ (g₁ + w * k₁) + (w * w) * c → g₂′ + w * h₂ ≤ (g₂ + w * k₂) + (w * w) * c →
    (g₁′ * g₂′) + w * (h₁ * g₂ + g₁ * h₂) ≤ ((g₁ * g₂) + w * (k₁ * g₂ + g₁ * k₂)) + (w * w) * Cc c
  ct1 {g₁} {_} {g₂} {_} {h₁} {h₂} {k₁} {k₂} {w} {c} w1 g₁b g₂b h₁b h₂b k₁b k₂b gd₁ gd₂ t₁ t₂ =
    ≤-trans (ct1a gd₁ gd₂) (≤-trans (+-mono (*-mono₂ t₁ t₂) ≤-refl) (≤-trans (≤-reflexive (eq1c g₁ g₂ h₁ h₂ k₁ k₂ w c))
      (+-mono ≤-refl (*-mono (w * w) (Bbound w1 (*-mono₂ k₁b k₂b) (Xb w1 g₁b k₁b) (Xb w1 g₂b k₂b) (+-mono h₁b h₂b))))))

  ----------------------------------------------------------------------------
  -- the second certificate: Y₁Y₂ ≤ (X₁ + e)(X₂ + e)

  eq2a : ∀ g₁ g₂ k₁ k₂ w → ((g₁ * g₂) + w * (k₁ * g₂ + g₁ * k₂)) + (w * w) * (k₁ * k₂) ≈ (g₁ + w * k₁) * (g₂ + w * k₂)
  eq2a g₁ g₂ k₁ k₂ w = solve 5 (λ a b p q w₀ → (a :* b :+ w₀ :* (p :* b :+ a :* q)) :+ (w₀ :* w₀) :* (p :* q)
    := (a :+ w₀ :* p) :* (b :+ w₀ :* q)) refl g₁ g₂ k₁ k₂ w

  eq2c : ∀ g₁′ g₂′ h₁ h₂ w c → ((g₁′ + w * h₁) + (w * w) * c) * ((g₂′ + w * h₂) + (w * w) * c)
    ≈ ((g₁′ * g₂′) + w * (g₁′ * h₂ + h₁ * g₂′)) + (w * w) * (h₁ * h₂ + (c * ((g₁′ + w * h₁) + (g₂′ + w * h₂)) + (w * w) * (c * c)))
  eq2c g₁′ g₂′ h₁ h₂ w c = solve 6 (λ a b p q w₀ c₀ → ((a :+ w₀ :* p) :+ (w₀ :* w₀) :* c₀) :* ((b :+ w₀ :* q) :+ (w₀ :* w₀) :* c₀)
    := (a :* b :+ w₀ :* (a :* q :+ p :* b)) :+ (w₀ :* w₀) :* (p :* q :+ (c₀ :* ((a :+ w₀ :* p) :+ (b :+ w₀ :* q))
      :+ (w₀ :* w₀) :* (c₀ :* c₀)))) refl g₁′ g₂′ h₁ h₂ w c

  eq2g : ∀ g₁ g₁′ g₂ g₂′ h₁ h₂ w c →
    (g₁′ * g₂′ + w * ((g₁ + w * (c + c)) * h₂ + h₁ * (g₂ + w * (c + c))))
      + (w * w) * (h₁ * h₂ + (c * ((g₁′ + w * h₁) + (g₂′ + w * h₂)) + (w * w) * (c * c)))
    ≈ ((g₁′ * g₂′) + w * (h₁ * g₂ + g₁ * h₂)) + (w * w) * Br c w (h₁ * h₂) (g₁′ + w * h₁) (g₂′ + w * h₂) (h₁ + h₂)
  eq2g g₁ g₁′ g₂ g₂′ h₁ h₂ w c = solve 8 (λ a b p q w₀ c₀ r s →
      (a :* b :+ w₀ :* ((r :+ w₀ :* (c₀ :+ c₀)) :* q :+ p :* (s :+ w₀ :* (c₀ :+ c₀))))
        :+ (w₀ :* w₀) :* (p :* q :+ (c₀ :* ((a :+ w₀ :* p) :+ (b :+ w₀ :* q)) :+ (w₀ :* w₀) :* (c₀ :* c₀)))
    := (a :* b :+ w₀ :* (p :* s :+ r :* q)) :+ (w₀ :* w₀) :* (p :* q :+ (c₀ :* ((a :+ w₀ :* p) :+ (b :+ w₀ :* q))
      :+ ((w₀ :* w₀) :* (c₀ :* c₀) :+ (c₀ :+ c₀) :* (p :+ q))))) refl g₁′ g₂′ h₁ h₂ w c g₁ g₂

  ct2b : ∀ {g₁ g₁′ g₂ g₂′ h₁ h₂ w c} → g₁′ ≤ g₁ + w * (c + c) → g₂′ ≤ g₂ + w * (c + c) →
    ((g₁′ + w * h₁) + (w * w) * c) * ((g₂′ + w * h₂) + (w * w) * c)
    ≤ ((g₁′ * g₂′) + w * (h₁ * g₂ + g₁ * h₂)) + (w * w) * Br c w (h₁ * h₂) (g₁′ + w * h₁) (g₂′ + w * h₂) (h₁ + h₂)
  ct2b {g₁} {g₁′} {g₂} {g₂′} {h₁} {h₂} {w} {c} gu₁ gu₂ =
    ≤-trans (≤-reflexive (eq2c g₁′ g₂′ h₁ h₂ w c))
      (≤-trans (+-mono (+-mono ≤-refl (*-mono w (+-mono (*-monoʳ h₂ gu₁) (*-mono h₁ gu₂)))) ≤-refl)
        (≤-reflexive (eq2g g₁ g₁′ g₂ g₂′ h₁ h₂ w c)))

  ct2 : ∀ {g₁ g₁′ g₂ g₂′ h₁ h₂ k₁ k₂ w c} → w ≤ 1# → g₁′ ≤ c → g₂′ ≤ c → h₁ ≤ c → h₂ ≤ c →
    g₁′ ≤ g₁ + w * (c + c) → g₂′ ≤ g₂ + w * (c + c) →
    g₁ + w * k₁ ≤ (g₁′ + w * h₁) + (w * w) * c → g₂ + w * k₂ ≤ (g₂′ + w * h₂) + (w * w) * c →
    ((g₁ * g₂) + w * (k₁ * g₂ + g₁ * k₂)) ≤ ((g₁′ * g₂′) + w * (h₁ * g₂ + g₁ * h₂)) + (w * w) * Cc c
  ct2 {g₁} {_} {g₂} {_} {h₁} {h₂} {k₁} {k₂} {w} {_} w1 g₁b g₂b h₁b h₂b gu₁ gu₂ t₁ t₂ =
    ≤-trans (≤-trans ≤-+ʳ (≤-reflexive (eq2a g₁ g₂ k₁ k₂ w))) (≤-trans (*-mono₂ t₁ t₂)
      (≤-trans (ct2b gu₁ gu₂) (+-mono ≤-refl (*-mono (w * w)
        (Bbound w1 (*-mono₂ h₁b h₂b) (Xb w1 g₁b h₁b) (Xb w1 g₂b h₂b) (+-mono h₁b h₂b))))))

  ----------------------------------------------------------------------------
  -- the product rule

  module _ {M c : ∣A∣} {G₁ h₁ k₁ G₂ h₂ k₂ : ∣A∣ → ∣A∣} (d₁ : D M c G₁ h₁ k₁) (d₂ : D M c G₂ h₂ k₂) where
    private
      a≤M : ∀ {a w} → a + w ≤ M → a ≤ M
      a≤M aw = ≤-trans ≤-+ʳ aw

      cc≤ : c * c ≤ Cp c
      cc≤ = ≤-trans (≤-+ʳ {c * c} {c * c}) ≤-+ˡ

      bb≤ : (c * c) + (c * c) ≤ Cp c
      bb≤ = ≤-+ˡ

      LL≤ : (L₁ c + L₁ c) ≤ Cp c
      LL≤ = ≤-trans ≤-+ˡ ≤-+ʳ

      Cc≤ : Cc c ≤ Cp c
      Cc≤ = ≤-trans ≤-+ʳ ≤-+ʳ

      bnd : ∀ {u₁ u₂ : ∣A∣ → ∣A∣} → Bnd M c u₁ → Bnd M c u₂ → Bnd M (Cp c) (λ x → u₁ x * G₂ x + G₁ x * u₂ x)
      bnd b₁ b₂ xM = ≤-trans (+-mono (*-mono₂ (b₁ xM) (D-bG d₂ xM)) (*-mono₂ (D-bG d₁ xM) (b₂ xM))) bb≤

      module LH = Lip d₁ d₂ (D-bh d₁) (D-bh d₂) (D-hU d₁) (D-hD d₁) (D-hU d₂) (D-hD d₂)
      module LK = Lip d₁ d₂ (D-bk d₁) (D-bk d₂) (D-kU d₁) (D-kD d₁) (D-kU d₂) (D-kD d₂)

      ctP1 : Ct1 M (Cp c) (λ x → G₁ x * G₂ x) (λ x → h₁ x * G₂ x + G₁ x * h₂ x) (λ x → k₁ x * G₂ x + G₁ x * k₂ x)
      ctP1 {a} {w} aw w1 = ≤-trans (ct1 {w = w} {c = c} w1 (D-bG d₁ (a≤M aw)) (D-bG d₂ (a≤M aw))
        (D-bh d₁ (a≤M aw)) (D-bh d₂ (a≤M aw)) (D-bk d₁ (a≤M aw)) (D-bk d₂ (a≤M aw))
        (Gdn d₁ aw w1) (Gdn d₂ aw w1) (D-c1 d₁ aw w1) (D-c1 d₂ aw w1)) (+-mono ≤-refl (*-mono _ Cc≤))

      ctP2 : Ct2 M (Cp c) (λ x → G₁ x * G₂ x) (λ x → h₁ x * G₂ x + G₁ x * h₂ x) (λ x → k₁ x * G₂ x + G₁ x * k₂ x)
      ctP2 {a} {w} aw w1 = ≤-trans (ct2 {w = w} {c = c} w1 (D-bG d₁ aw) (D-bG d₂ aw)
        (D-bh d₁ (a≤M aw)) (D-bh d₂ (a≤M aw)) (Gup d₁ aw w1) (Gup d₂ aw w1) (D-c2 d₁ aw w1) (D-c2 d₂ aw w1))
        (+-mono ≤-refl (*-mono _ Cc≤))

    Dprod : D M (Cp c) (λ x → G₁ x * G₂ x) (λ x → h₁ x * G₂ x + G₁ x * h₂ x) (λ x → k₁ x * G₂ x + G₁ x * k₂ x)
    Dprod = mkD (λ e → *-cong (D-cG d₁ e) (D-cG d₂ e))
      (λ e → +-cong (*-cong (D-ch d₁ e) (D-cG d₂ e)) (*-cong (D-cG d₁ e) (D-ch d₂ e)))
      (λ e → +-cong (*-cong (D-ck d₁ e) (D-cG d₂ e)) (*-cong (D-cG d₁ e) (D-ck d₂ e)))
      (λ xM → ≤-trans (*-mono₂ (D-bG d₁ xM) (D-bG d₂ xM)) cc≤)
      (bnd (D-bh d₁) (D-bh d₂)) (bnd (D-bk d₁) (D-bk d₂))
      (LpU-mono LL≤ LH.P-up) (LpD-mono LL≤ LH.P-dn) (LpU-mono LL≤ LK.P-up) (LpD-mono LL≤ LK.P-dn) ctP1 ctP2

  DFprod : ∀ {M G₁ h₁ k₁ G₂ h₂ k₂} → Deriv M G₁ h₁ k₁ → Deriv M G₂ h₂ k₂ →
    Deriv M (λ x → G₁ x * G₂ x) (λ x → h₁ x * G₂ x + G₁ x * h₂ x) (λ x → k₁ x * G₂ x + G₁ x * k₂ x)
  DFprod (c₁ , f₁ , d₁) (c₂ , f₂ , d₂) = Cp (c₁ + c₂) , Fin-Cp (Fin-+ f₁ f₂) , Dprod (Dmono ≤-+ʳ d₁) (Dmono ≤-+ˡ d₂)
