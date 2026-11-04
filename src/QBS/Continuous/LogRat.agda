{-# OPTIONS --safe --without-K #-}

-- The exponential of a rational, as a cut (plan 03, "Signed layer", helper for `SignedLog`).
--   * `rc p` is the cut {t | t < p or t < 0}, the rational cut `qC p` for p > 0 (`rc≋qC`), defined for every p;
--   * `E p = expC (rc p)`, with `E-add : E (p + η) ≋ E p ⊗ E η`, `E-mono`, the lower bound `E-lo` (every t < 1 + p is in
--     E p) and the upper bound `E-hi` (every t ∈ E p is below 1 + (p + p²) for p ≤ 1);
--   * `Le p s` says e^p ≤ s (all elements of E p are below s), and `E-prod` bounds the elements of E (p + η) when
--     `Le p s` and η is small: they are below s · (1 + (η + η²)), with the converse `E-prod-lo`;
--   * `small-ε`: for 0 < s < s′ some ε with m = 3ε ≤ 1 and s (1 + (m + m²)) < s′.
-- Route: `ExpLower.expC` on the rational cuts, `LowerRealsArch.qC-add`, `ExpLower.qC-mul` for the sums and products.
module QBS.Continuous.LogRat where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.LowerRealsArch using (qC; qC-cong; qC-add)
open import QBS.Analysis.ExpLower
open import QBS.Classical using (LEM₀)

-- the rational cut clipped at 0
rc : ℚᵘ → Cut
rc p = record
  { mem = λ t → t < p ⊎ t < 0ℚᵘ
  ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt) ; le (inj₂ lt) → inj₂ (≤-<-trans le lt) }
  ; open′ = λ { (inj₁ lt) → let q , a , b = dense lt in q , a , inj₁ b
              ; (inj₂ lt) → let q , a , b = dense lt in q , a , inj₂ b }
  ; neg = inj₂ }

rc≋qC : ∀ {p} (0<p : 0ℚᵘ < p) → rc p ≋ qC p 0<p
rc≋qC 0<p = mk⊑ (λ { t (inj₁ lt) → lt ; t (inj₂ lt) → <-trans lt 0<p }) , mk⊑ (λ t lt → inj₁ lt)

rc-mono : ∀ {p p′} → p ≤ p′ → rc p ⊑ rc p′
rc-mono le = mk⊑ (λ { t (inj₁ lt) → inj₁ (<-≤-trans lt le) ; t (inj₂ lt) → inj₂ lt })

-- `rc p` below `q` forces all its elements below `q` or 0
rc-sub : ∀ {p} (y : Cut) → (∀ u → mem y u → u < p) → y ⊑ rc p
rc-sub y f = mk⊑ (λ u m → inj₁ (f u m))

-- 1 + (m + m²)
cst : ℚᵘ → ℚᵘ
cst m = 1ℚᵘ + (m + m * m)

0<cst : ∀ {m} → 0ℚᵘ < m → 0ℚᵘ < cst m
0<cst 0<m = +-pos 0<1 (+-pos 0<m (*-pos 0<m 0<m))

-- the inverse of 1 + (s + s) is at most 1
inv-le1 : ∀ {s t} → 0ℚᵘ < s → 0ℚᵘ < t → t * (1ℚᵘ + (s + s)) ≃ 1ℚᵘ → t ≤ 1ℚᵘ
inv-le1 {s} {t} 0<s 0<t ht = ≤-trans (≤-≃ (≃-sym (P-id t))) (≤-trans (*-mono-≤-nn (<-≤ 0<t) 1≤L) (≤-≃ ht))
  where
    1≤L : 1ℚᵘ ≤ 1ℚᵘ + (s + s)
    1≤L = <-≤ (lt-add {1ℚᵘ} (+-pos 0<s 0<s))

-- a small m with (s + s) m < d, for d ≤ 1
small-d : ∀ {s d} → 0ℚᵘ < s → 0ℚᵘ < d → d ≤ 1ℚᵘ → Σ ℚᵘ (λ m → 0ℚᵘ < m × m ≤ 1ℚᵘ × (s + s) * m < d)
small-d {s} {d} 0<s 0<d d≤1 = m , 0<m , m≤1 , ≃-<ʳ eq (lt-add {(s + s) * m} 0<m)
  where
    L = 1ℚᵘ + (s + s)
    0<L = +-pos 0<1 (+-pos 0<s 0<s)
    t = proj₁ (inv 0<L)
    ht = proj₂ (inv 0<L)
    0<t = pos-inv 0<L ht
    t≤1 = inv-le1 0<s 0<t ht
    m = d * t
    0<m = *-pos 0<d 0<t
    m≤1 : m ≤ 1ℚᵘ
    m≤1 = ≤-trans (*-mono-≤-nn (<-≤ 0<d) t≤1) (≤-trans (≤-≃ (P-id d)) d≤1)
    eq : (s + s) * m + m ≃ d
    eq = ≃-trans (solve 3 (λ s d t → (s :+ s) :* (d :* t) :+ d :* t := d :* (t :* (con 1ℚᵘ :+ (s :+ s)))) ≃-refl s d t)
           (≃-trans (*-cong (≃-refl {d}) ht) (P-id d))

-- 1 + (m + m²) ≤ 1 + 2m for m ≤ 1
cst-bd : ∀ {s m} → 0ℚᵘ < s → 0ℚᵘ < m → m ≤ 1ℚᵘ → s * cst m ≤ s + (s + s) * m
cst-bd {s} {m} 0<s 0<m m≤1 =
  ≤-trans (≤-≃ (solve 2 (λ s m → s :* (con 1ℚᵘ :+ (m :+ m :* m)) := s :+ (s :* m :+ s :* (m :* m))) ≃-refl s m))
  (≤-trans (+-mono-≤ (≤-refl {s}) (+-mono-≤ (≤-refl {s * m}) (*-mono-≤-nn (<-≤ 0<s) mm≤m)))
    (≤-≃ (solve 2 (λ s m → s :+ (s :* m :+ s :* m) := s :+ (s :+ s) :* m) ≃-refl s m)))
  where
    mm≤m : m * m ≤ m
    mm≤m = ≤-trans (*-mono-≤-nn (<-≤ 0<m) m≤1) (≤-≃ (P-id m))

-- ε with 2ε < m
half-ε : ∀ {m} → 0ℚᵘ < m → Σ ℚᵘ (λ ε → 0ℚᵘ < ε × ε + ε < m)
half-ε {m} 0<m with dense (*-pos 0<½ 0<m)
... | ε , 0<ε , lt = ε , 0<ε , ≃-<ʳ (≃-trans (solve 1 (λ m → con ½ :* m :+ con ½ :* m := (con ½ :+ con ½) :* m) ≃-refl m)
    (≃-trans (*-cong ½+½ (≃-refl {m})) (*-identityˡ m)))
  (<-trans (+-mono-<-≤ lt (≤-refl {ε})) (+-mono-≤-< (≤-refl {½ * m}) lt))

small-fin : ∀ {s s′ d} → 0ℚᵘ < s → s + d ≤ s′ → Σ ℚᵘ (λ m → 0ℚᵘ < m × m ≤ 1ℚᵘ × (s + s) * m < d) →
  Σ ℚᵘ (λ m → 0ℚᵘ < m × m ≤ 1ℚᵘ × s * cst m < s′ × Σ ℚᵘ (λ ε → 0ℚᵘ < ε × ε + ε < m))
small-fin {s} 0<s sd (m , 0<m , m≤1 , lt) = m , 0<m , m≤1 ,
  ≤-<-trans (cst-bd 0<s 0<m m≤1) (<-≤-trans (+-mono-≤-< (≤-refl {s}) lt) sd) , half-ε 0<m

-- m small enough that s (1 + (m + m²)) < s′, and ε with 2ε < m
small-ε : ∀ {s s′} → 0ℚᵘ < s → s < s′ →
  Σ ℚᵘ (λ m → 0ℚᵘ < m × m ≤ 1ℚᵘ × s * cst m < s′ × Σ ℚᵘ (λ ε → 0ℚᵘ < ε × ε + ε < m))
small-ε {s} {s′} 0<s lt with ≤-or-> s′ (s + 1ℚᵘ)
... | inj₁ le = small-fin 0<s (≤-≃ (add-sub s s′)) (small-d 0<s (pos-diff lt) d≤1)
  where
    d≤1 : s′ + - s ≤ 1ℚᵘ
    d≤1 = ≤-trans (+-mono-≤ le (≤-refl {(- s)}))
      (≤-≃ (solve 1 (λ s → (s :+ con 1ℚᵘ) :+ :- s := con 1ℚᵘ) ≃-refl s))
... | inj₂ gt = small-fin 0<s (<-≤ gt) (small-d 0<s 0<1 (≤-refl {1ℚᵘ}))

module LogRat (lem : LEM₀) where

  E : ℚᵘ → Cut
  E p = expC lem (rc p)

  -- e^p ≤ s
  Le : ℚᵘ → ℚᵘ → Set
  Le p s = ∀ t → mem (E p) t → t < s

  E-mono : ∀ {p p′} → p ≤ p′ → E p ⊑ E p′
  E-mono le = expC-mono lem (rc-mono le)

  E-add : ∀ {p η} → 0ℚᵘ < p → 0ℚᵘ < η → E (p + η) ≋ E p ⊗ E η
  E-add {p} {η} 0<p 0<η = ≋-trans (expC-cong lem split) (Add.exp-add lem (rc p) (rc η))
    where
      split : rc (p + η) ≋ rc p ⊕ rc η
      split = ≋-trans (rc≋qC (+-pos 0<p 0<η)) (≋-trans (≋-sym (qC-add 0<p 0<η))
        (⊕-cong (≋-sym (rc≋qC 0<p)) (≋-sym (rc≋qC 0<η))))

  E-lo : ∀ {p} → 0ℚᵘ < p → ∀ t → t < 1ℚᵘ + p → mem (E p) t
  E-lo {p} 0<p t lt = ap (1+≤expC lem (rc p)) t
    (ap (⊕-mono {qC 1ℚᵘ 0<1} {oneC} (mk⊑ (λ _ m → m)) (proj₂ (rc≋qC 0<p))) t
      (ap (proj₂ (qC-add 0<1 0<p)) t lt))

  rc≤1 : ∀ {p} → p ≤ 1ℚᵘ → rc p ⊑ oneC
  rc≤1 le = mk⊑ (λ { t (inj₁ lt) → <-≤-trans lt le ; t (inj₂ lt) → <-trans lt 0<1 })

  E-hi : ∀ {p} → 0ℚᵘ < p → p ≤ 1ℚᵘ → ∀ t → mem (E p) t → t < 1ℚᵘ + (p + p * p)
  E-hi {p} 0<p le t m = ap (⊑-trans step (proj₁ (qC-add 0<1 (+-pos 0<p (*-pos 0<p 0<p))))) t
      (ap (expC≤quad lem (rc≤1 le)) t m)
    where
      rq = proj₁ (rc≋qC 0<p)
      sq : rc p ⊗ rc p ⊑ qC (p * p) (*-pos 0<p 0<p)
      sq = ⊑-trans (⊗-mono rq rq) (proj₁ (qC-mul 0<p 0<p))
      sm : rc p ⊕ rc p ⊗ rc p ⊑ qC (p + p * p) (+-pos 0<p (*-pos 0<p 0<p))
      sm = ⊑-trans (⊕-mono rq sq) (proj₁ (qC-add 0<p (*-pos 0<p 0<p)))
      step : oneC ⊕ (rc p ⊕ rc p ⊗ rc p) ⊑ qC 1ℚᵘ 0<1 ⊕ qC (p + p * p) (+-pos 0<p (*-pos 0<p 0<p))
      step = ⊕-mono (mk⊑ (λ _ m → m)) sm

  -- e^p ≤ s forces s > 0
  Le-pos : ∀ {p s} → 0ℚᵘ < p → Le p s → 0ℚᵘ < s
  Le-pos 0<p le = le 0ℚᵘ (E-lo 0<p 0ℚᵘ (+-pos 0<1 0<p))

  -- the elements of E (p + η) when e^p ≤ s
  E-prod : ∀ {p η s} → 0ℚᵘ < p → 0ℚᵘ < η → η ≤ 1ℚᵘ → 0ℚᵘ < s → Le p s →
    ∀ t → mem (E (p + η)) t → t < s * cst η
  E-prod {p} {η} {s} 0<p 0<η η≤1 0<s le t m = go (ap (proj₁ (E-add 0<p 0<η)) t m)
    where
      go : mem (E p ⊗ E η) t → t < s * cst η
      go (inj₁ lt) = <-trans lt (*-pos 0<s (0<cst 0<η))
      go (inj₂ (r , u , 0<r , 0<u , mr , mu , h)) =
        ≤-<-trans h (<-trans (*-mono-<-posʳ 0<u (le r mr)) (*-mono-<-pos 0<s (E-hi 0<η η≤1 u mu)))
