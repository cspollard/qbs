{-# OPTIONS --safe --without-K #-}

-- The positive part of the logarithm, `logP x = log (x ⊔ 1)` as a lower real (plan 03, "Signed layer", helper for
-- `SignedLog`):  q ∈ logP x  iff  q < 0, or some p > q and s ∈ x have e^p ≤ s (`Le p s`, from `LogRat`).
--   * `logP-mono`, `logP-cong`, `logP-le` (x ≤ 1 gives 0), `logP-bndQ` (bounded x gives bounded logP x), `Meas-logP`;
--   * `logP-ge` : e^{logP x} ≈ x for 1 ≤ x bounded by a rational.
--     ⊑ : for t ∈ e^{logP x} take t′ > t, a small ε with t (1 + (m + m²)) < t′ and, by `near-sup-bnd`, r ∈ logP x with
--     every element below r + ε; then logP x ⊑ rc (p₀ + m) for p₀ with e^{p₀} ≤ s₀ ∈ x, and `E-prod` gives
--     t′ < s₀ (1 + (m + m²)), so t < s₀.
--     ⊒ : for s ∈ x, s ≥ 1, take s₁ ∈ x above s; if no q ∈ logP x has s ∈ E q, then e^q ≤ s for all q ∈ logP x, and
--     the near-supremum r gives a point p = r′ + 2ε not in logP x although s₁ ∈ E (r′ + m) < s (1 + (m + m²)) < s₁.
--   * `log-exp` : logP (e^a) ≈ a for bounded a, from the strictness of e^p in p (`E-strict`, by negExp-expC-nat).
module QBS.Continuous.LogCore where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.LowerRealsNear using (BndQ; module Near)
open import Data.Nat.Base using (ℕ; zero; suc)
open import QBS.Analysis.ExpLower
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.LogRat
open import QBS.Classical using (LEM₀)

-- a rational bound can be taken positive
bnd-pos : ∀ {x : Cut} → BndQ x → Σ ℚᵘ (λ B → 0ℚᵘ < B × (∀ s → mem x s → s < B))
bnd-pos (M , bd) with pos-or-nonpos M
... | inj₁ 0<M = M , 0<M , bd
... | inj₂ M≤0 = 1ℚᵘ , 0<1 , λ s m → <-trans (<-≤-trans (bd s m) M≤0) 0<1

p<1+p : ∀ p → p < 1ℚᵘ + p
p<1+p p = ≃-<ˡ (+-identityˡ p) (+-mono-<-≤ 0<1 (≤-refl {p}))

module LogCore (lem : LEM₀) where
  open LogRat lem
  open Near lem using (near-sup-bnd)
  open NegExp lem using (negExp; negExp-expC-nat)
  open Exp (LowerRealsOmega lem) using (natE)

  logP : Cut → Cut
  logP x = record
    { mem = λ q → q < 0ℚᵘ ⊎ Σ ℚᵘ (λ p → q < p × Σ ℚᵘ (λ s → mem x s × Le p s))
    ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt) ; le (inj₂ (p , lt , w)) → inj₂ (p , ≤-<-trans le lt , w) }
    ; open′ = λ { (inj₁ lt) → let q′ , a , b = dense lt in q′ , a , inj₁ b
                ; (inj₂ (p , lt , w)) → let q′ , a , b = dense lt in q′ , a , inj₂ (p , b , w) }
    ; neg = inj₁ }

  logP-mono : ∀ {x y} → x ⊑ y → logP x ⊑ logP y
  logP-mono xy = mk⊑ (λ { q (inj₁ lt) → inj₁ lt ; q (inj₂ (p , lt , s , ms , le)) → inj₂ (p , lt , s , ap xy s ms , le) })

  logP-cong : ∀ {x y} → x ≋ y → logP x ≋ logP y
  logP-cong (a , b) = logP-mono a , logP-mono b

  logP-le : ∀ {x} → x ⊑ oneC → logP x ≋ zeroC
  logP-le {x} xo = mk⊑ f , mk⊑ (λ q lt → inj₁ lt)
    where
      f : ∀ q → mem (logP x) q → q < 0ℚᵘ
      f q (inj₁ lt) = lt
      f q (inj₂ (p , lt , s , ms , le)) with pos-or-nonpos p
      ... | inj₂ p≤0 = <-≤-trans lt p≤0
      ... | inj₁ 0<p = ⊥-elim (<-irrefl ≃-refl (le s (E-lo 0<p s (<-trans (ap xo s ms) (lt-add {1ℚᵘ} 0<p)))))

  -- a bound for logP x
  logP-bd : ∀ {x B} → 0ℚᵘ < B → (∀ s → mem x s → s < B) → ∀ q → mem (logP x) q → q < B
  logP-bd 0<B bd q (inj₁ lt) = <-trans lt 0<B
  logP-bd {x} {B} 0<B bd q (inj₂ (p , lt , s , ms , le)) with pos-or-nonpos p
  ... | inj₂ p≤0 = <-trans (<-≤-trans lt p≤0) 0<B
  ... | inj₁ 0<p with ≤-or-> (1ℚᵘ + p) s
  ...   | inj₁ le′ = <-trans lt (<-trans (p<1+p p) (≤-<-trans le′ (bd s ms)))
  ...   | inj₂ lt′ = ⊥-elim (<-irrefl ≃-refl (le s (E-lo 0<p s lt′)))

  logP-bndQ : ∀ {x} → BndQ x → BndQ (logP x)
  logP-bndQ {x} bx = let B , 0<B , bd = bnd-pos {x} bx in B , logP-bd 0<B bd

  -- elements of expC y when y is bounded by π
  up : ∀ {y π t} → (∀ q → mem y q → q < π) → mem (expC lem y) t → mem (E π) t
  up {y} f m = ap (expC-mono lem (rc-sub y f)) _ m

  rc-in : ∀ {y q} → mem y q → rc q ⊑ y
  rc-in {y} mq = mk⊑ (λ { u (inj₁ lt) → down y (<-≤ lt) mq ; u (inj₂ lt) → neg y lt })

  ε<m : ∀ {ε m} → 0ℚᵘ < ε → ε + ε < m → ε < m
  ε<m 0<ε lt = <-trans (lt-add {_} 0<ε) lt

  -- `t (1 + (m + m²)) < t′ < 1 + (m + m²)` forces t < 1
  fwdA : ∀ {y t t′ m ε r} → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m → t * cst m < t′ → mem (expC lem y) t′ →
    r < 0ℚᵘ → (∀ q → mem y q → q ≤ r + ε) → t < 1ℚᵘ
  fwdA {y} {t} {t′} {m} {ε} {r} 0<m m≤1 0<ε εε hc mt′ r<0 hr = *-cancel-<ʳ (0<cst 0<m)
    (≃-<ʳ (≃-sym (*-identityˡ (cst m))) (<-trans hc (E-hi 0<m m≤1 t′ (up {y} bd mt′))))
    where
      bd : ∀ q → mem y q → q < m
      bd q mq = ≤-<-trans (hr q mq) (<-trans (<-≤-trans (+-mono-<-≤ r<0 (≤-refl {ε})) (≤-≃ (+-identityˡ ε))) (ε<m 0<ε εε))

  -- `t (1 + (m + m²)) < t′`, e^{p₀} ≤ s₀ and r < p₀ give t < s₀
  fwdB : ∀ {y t t′ m ε r p₀ s₀} → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m → t * cst m < t′ → mem (expC lem y) t′ →
    0ℚᵘ < p₀ → r < p₀ → Le p₀ s₀ → (∀ q → mem y q → q ≤ r + ε) → t < s₀
  fwdB {y} {t} {t′} {m} {ε} {r} {p₀} {s₀} 0<m m≤1 0<ε εε hc mt′ 0<p₀ r<p₀ le₀ hr = *-cancel-<ʳ (0<cst 0<m)
    (<-trans hc (E-prod 0<p₀ 0<m m≤1 (Le-pos 0<p₀ le₀) le₀ t′ (up {y} bd mt′)))
    where
      bd : ∀ q → mem y q → q < p₀ + m
      bd q mq = ≤-<-trans (hr q mq) (<-trans (+-mono-<-≤ r<p₀ (≤-refl {ε})) (+-mono-≤-< (≤-refl {p₀}) (ε<m 0<ε εε)))

  -- the near-supremum r of logP x is negative, or lies below some p₀ with e^{p₀} ≤ s₀ ∈ x
  fwd-fin : ∀ {x t t′ m ε r} → oneC ⊑ x → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m → t * cst m < t′ →
    mem (expC lem (logP x)) t′ → mem (logP x) r → (∀ q → mem (logP x) q → q ≤ r + ε) → mem x t
  fwd-fin {x} {t} ox 0<m m≤1 0<ε εε hc mt′ mr hr with neg-or-nonneg _
  fwd-fin {x} {t} ox 0<m m≤1 0<ε εε hc mt′ mr hr | inj₁ r<0 = ap ox t (fwdA {logP x} 0<m m≤1 0<ε εε hc mt′ r<0 hr)
  fwd-fin {x} {t} ox 0<m m≤1 0<ε εε hc mt′ (inj₁ r<0) hr | inj₂ 0≤r = ⊥-elim (<-irrefl ≃-refl (<-≤-trans r<0 0≤r))
  fwd-fin {x} {t} ox 0<m m≤1 0<ε εε hc mt′ (inj₂ (p₀ , r<p₀ , s₀ , ms₀ , le₀)) hr | inj₂ 0≤r =
    down x (<-≤ (fwdB {logP x} 0<m m≤1 0<ε εε hc mt′ (≤-<-trans 0≤r r<p₀) r<p₀ le₀ hr)) ms₀

  fwd-step : ∀ {x t} → BndQ x → oneC ⊑ x → 0ℚᵘ < t → mem (expC lem (logP x)) t → mem x t
  fwd-step {x} {t} bx ox 0<t mt =
    let t′ , t<t′ , mt′ = open′ (expC lem (logP x)) mt
        m , 0<m , m≤1 , hc , ε , 0<ε , εε = small-ε 0<t t<t′
        B , 0<B , bd = bnd-pos {x} bx
        r , mr , hr = near-sup-bnd (logP x) B {ε} (logP-bd 0<B bd) 0<ε
    in fwd-fin {x} {t} {t′} ox 0<m m≤1 0<ε εε hc mt′ mr hr

  -- the upper half of the characterisation
  logP-ge-fwd : ∀ x → oneC ⊑ x → BndQ x → expC lem (logP x) ⊑ x
  logP-ge-fwd x ox bx = mk⊑ go
    where
      go : ∀ t → mem (expC lem (logP x)) t → mem x t
      go t mt with ≤-or-> 1ℚᵘ t
      ... | inj₂ t<1 = ap ox t t<1
      ... | inj₁ 1≤t = fwd-step bx ox (<-≤-trans 0<1 1≤t) mt

  -- if e^π ≤ s₁ fails then s₁ ∈ E π
  ¬Le⇒∈ : ∀ {π s₁} → (Le π s₁ → ⊥) → mem (E π) s₁
  ¬Le⇒∈ {π} {s₁} nl with lem (Σ ℚᵘ (λ t → mem (E π) t × s₁ ≤ t))
  ... | inj₁ (t , mt , le) = down (E π) le mt
  ... | inj₂ none = ⊥-elim (nl (λ t mt → go t mt (≤-or-> s₁ t)))
    where
      go : ∀ t → mem (E π) t → s₁ ≤ t ⊎ t < s₁ → t < s₁
      go t mt (inj₁ le) = ⊥-elim (none (t , mt , le))
      go t mt (inj₂ lt) = lt

  -- the data of the lower half: s ≤ ... , tolerance ε, near-supremum r
  bwdP : ∀ {x s s₁ m ε r r′} → mem x s₁ → 0ℚᵘ < s → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m → s * cst m < s₁ →
    (∀ q → mem (logP x) q → Le q s) → (∀ q → mem (logP x) q → q ≤ r + ε) → r < r′ → mem (logP x) r′ → 0ℚᵘ < r′ → ⊥
  bwdP {x} {s} {s₁} {m} {ε} {r} {r′} ms₁ 0<s 0<m m≤1 0<ε εε hs noLe hr r<r′ mr′ 0<r′ =
    <-irrefl ≃-refl (<-trans hs (E-prod 0<r′ 0<m m≤1 0<s (noLe r′ mr′) s₁ (¬Le⇒∈ nl)))
    where
      p = r′ + (ε + ε)
      nl : Le (r′ + m) s₁ → ⊥
      nl le = <-irrefl ≃-refl (≤-<-trans (hr p (inj₂ (r′ + m , +-mono-≤-< (≤-refl {r′}) εε , s₁ , ms₁ , le)))
        (<-≤-trans (+-mono-<-≤ r<r′ (≤-refl {ε})) (+-mono-≤ (≤-refl {r′}) (<-≤ (lt-add {ε} 0<ε)))))

  bwdN : ∀ {x s s₁ m ε r r′} → mem x s₁ → 1ℚᵘ ≤ s → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m → s * cst m < s₁ →
    (∀ q → mem (logP x) q → q ≤ r + ε) → r < r′ → r′ ≤ 0ℚᵘ → ⊥
  bwdN {x} {s} {s₁} {m} {ε} {r} {r′} ms₁ 1≤s 0<m m≤1 0<ε εε hs hr r<r′ r′≤0 =
    <-irrefl ≃-refl (<-≤-trans (<-trans hs (E-hi 0<m m≤1 s₁ (¬Le⇒∈ nl)))
      (≤-trans (≤-≃ (≃-sym (*-identityˡ (cst m)))) (*-mono-≤-nnʳ (<-≤ (0<cst 0<m)) 1≤s)))
    where
      nl : Le m s₁ → ⊥
      nl le = <-irrefl ≃-refl (≤-<-trans (hr (ε + ε) (inj₂ (m , εε , s₁ , ms₁ , le)))
        (<-trans (<-≤-trans (+-mono-<-≤ r<r′ (≤-refl {ε})) (≤-trans (+-mono-≤ r′≤0 (≤-refl {ε})) (≤-≃ (+-identityˡ ε))))
          (lt-add {ε} 0<ε)))

  -- no q ∈ logP x with s ∈ E q gives e^q ≤ s for all q ∈ logP x
  no⇒Le : ∀ {x s} → ((Σ ℚᵘ (λ q → mem (logP x) q × mem (E q) s)) → ⊥) → ∀ q → mem (logP x) q → Le q s
  no⇒Le {x} {s} no q mq t mt with ≤-or-> s t
  ... | inj₁ s≤t = ⊥-elim (no (q , mq , down (E q) s≤t mt))
  ... | inj₂ t<s = t<s

  bwd-contra : ∀ {x s} → BndQ x → 1ℚᵘ ≤ s → mem x s → (∀ q → mem (logP x) q → Le q s) → ⊥
  bwd-contra {x} {s} bx 1≤s ms noLe =
    let 0<s = <-≤-trans 0<1 1≤s
        s₁ , s<s₁ , ms₁ = open′ x ms
        m , 0<m , m≤1 , hs , ε , 0<ε , εε = small-ε 0<s s<s₁
        B , 0<B , bd = bnd-pos {x} bx
        r , mr , hr = near-sup-bnd (logP x) B {ε} (logP-bd 0<B bd) 0<ε
        r′ , r<r′ , mr′ = open′ (logP x) mr
    in cases ms₁ 0<s 1≤s 0<m m≤1 0<ε εε hs noLe hr r<r′ mr′ (pos-or-nonpos r′)
    where
      cases : ∀ {s₁ m ε r r′} → mem x s₁ → 0ℚᵘ < s → 1ℚᵘ ≤ s → 0ℚᵘ < m → m ≤ 1ℚᵘ → 0ℚᵘ < ε → ε + ε < m →
        s * cst m < s₁ → (∀ q → mem (logP x) q → Le q s) → (∀ q → mem (logP x) q → q ≤ r + ε) → r < r′ →
        mem (logP x) r′ → 0ℚᵘ < r′ ⊎ r′ ≤ 0ℚᵘ → ⊥
      cases ms₁ 0<s 1≤s 0<m m≤1 0<ε εε hs noLe hr r<r′ mr′ (inj₁ 0<r′) = bwdP ms₁ 0<s 0<m m≤1 0<ε εε hs noLe hr r<r′ mr′ 0<r′
      cases ms₁ 0<s 1≤s 0<m m≤1 0<ε εε hs noLe hr r<r′ mr′ (inj₂ r′≤0) = bwdN {x} ms₁ 1≤s 0<m m≤1 0<ε εε hs hr r<r′ r′≤0

  -- the lower half of the characterisation
  logP-ge-bwd : ∀ x → BndQ x → x ⊑ expC lem (logP x)
  logP-ge-bwd x bx = mk⊑ go
    where
      go : ∀ s → mem x s → mem (expC lem (logP x)) s
      go s ms with ≤-or-> 1ℚᵘ s
      ... | inj₂ s<1 = ap (⊑-trans (⊕-inl oneC (logP x)) (1+≤expC lem (logP x))) s s<1
      ... | inj₁ 1≤s with lem (Σ ℚᵘ (λ q → mem (logP x) q × mem (E q) s))
      ...   | inj₁ (q , mq , mE) = ap (expC-mono lem (rc-in mq)) s mE
      ...   | inj₂ no = ⊥-elim (bwd-contra bx 1≤s ms (no⇒Le {x} no))

  logP-ge : ∀ x → oneC ⊑ x → BndQ x → expC lem (logP x) ≋ x
  logP-ge x ox bx = logP-ge-fwd x ox bx , logP-ge-bwd x bx

  ----------------------------------------------------------------------------
  -- strictness of e^p in p, and log (e^a) = a

  rc-nat : ∀ p → Σ ℕ (λ N → rc p ⊑ natE N)
  rc-nat p = suc k , mk⊑ (λ t m → ap (proj₂ (natE≋ lem k)) t (f t m))
    where
      k = proj₁ (nat-bound p)
      f : ∀ t → mem (rc p) t → t < nat (suc k)
      f t (inj₁ lt) = <-≤-trans lt (≤-trans (proj₂ (nat-bound p)) (<-≤ (≃-<ʳ (≃-sym (nat-suc k)) (lt-add {nat k} 0<1))))
      f t (inj₂ lt) = <-trans lt (0<nat k)

  -- E δ ⊑ 1 if E (p + δ) ⊑ E p
  strict-⊥ : ∀ {p₁ p₂} → 0ℚᵘ < p₁ → p₁ < p₂ → E p₂ ⊑ E p₁ → ⊥
  strict-⊥ {p₁} {p₂} 0<p₁ lt h = <-irrefl ≃-refl (<-trans (proj₁ (proj₂ bb)) (ap Eδ≤1 _ (E-lo 0<δ _ (proj₂ (proj₂ bb)))))
    where
      δ = p₂ + - p₁
      0<δ = pos-diff lt
      bb = dense (lt-add {1ℚᵘ} 0<δ)
      h′ : E p₁ ⊗ E δ ⊑ E p₁
      h′ = ⊑-trans (proj₂ (E-add 0<p₁ 0<δ)) (⊑-trans (E-mono (≤-≃ (add-sub p₁ p₂))) h)
      hN = negExp-expC-nat (rc p₁) (proj₁ (rc-nat p₁)) (proj₂ (rc-nat p₁))
      Eδ≤1 : E δ ⊑ oneC
      Eδ≤1 = ⊑-trans (proj₂ (⊗-identityˡ (E δ))) (⊑-trans (proj₁ (⊗-cong (≋-sym hN) (≋-refl {E δ})))
        (⊑-trans (proj₁ (⊗-assoc (negExp (rc p₁)) (E p₁) (E δ))) (⊑-trans (⊗-mono (⊑-refl {negExp (rc p₁)}) h′) (proj₁ hN))))

  E-strict : ∀ {p₁ p₂} → 0ℚᵘ < p₁ → p₁ < p₂ → Σ ℚᵘ (λ s → mem (E p₂) s × Le p₁ s)
  E-strict {p₁} {p₂} 0<p₁ lt with lem (Σ ℚᵘ (λ s → mem (E p₂) s × Le p₁ s))
  ... | inj₁ w = w
  ... | inj₂ none = ⊥-elim (strict-⊥ 0<p₁ lt (mk⊑ (λ s ms → ¬Le⇒∈ (λ le → none (s , ms , le)))))

  logP-exp-fwd : ∀ a → logP (expC lem a) ⊑ a
  logP-exp-fwd a = mk⊑ go
    where
      mem-p : ∀ {p s} → mem (expC lem a) s → Le p s → mem a p
      mem-p {p} {s} ms le with lem (mem a p)
      ... | inj₁ mp = mp
      ... | inj₂ np = ⊥-elim (let s′ , s<s′ , ms′ = open′ (E p) (ap (expC-mono lem (rc-sub a lt)) s ms)
                               in <-irrefl ≃-refl (<-trans s<s′ (le s′ ms′)))
        where
          lt : ∀ u → mem a u → u < p
          lt u mu with ≤-or-> p u
          ... | inj₁ p≤u = ⊥-elim (np (down a p≤u mu))
          ... | inj₂ u<p = u<p
      go : ∀ q → mem (logP (expC lem a)) q → mem a q
      go q (inj₁ lt) = neg a lt
      go q (inj₂ (p , lt , s , ms , le)) = down a (<-≤ lt) (mem-p ms le)

  logP-exp-bwd : ∀ a → a ⊑ logP (expC lem a)
  logP-exp-bwd a = mk⊑ go
    where
      go : ∀ q → mem a q → mem (logP (expC lem a)) q
      go q mq with neg-or-nonneg q
      ... | inj₁ q<0 = inj₁ q<0
      ... | inj₂ 0≤q =
        let p₁ , q<p₁ , mp₁ = open′ a mq
            p₂ , p₁<p₂ , mp₂ = open′ a mp₁
            s , ms , le = E-strict (≤-<-trans 0≤q q<p₁) p₁<p₂
        in inj₂ (p₁ , q<p₁ , s , ap (expC-mono lem (rc-in mp₂)) s ms , le)

  log-exp-P : ∀ a → logP (expC lem a) ≋ a
  log-exp-P a = logP-exp-fwd a , logP-exp-bwd a
