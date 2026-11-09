{-# OPTIONS --safe --without-K #-}

-- `e^{−x}` on the lower reals [0, ∞], as a cut defined directly (there is no negation or division):
--   q ∈ negExp x  iff  ∃ p > q, ∀ s ∈ expC x, p · s < 1,
-- i.e. `q · e^x < 1` with room to spare.  Stating it with a witness `p > q` rather than as
-- "`q · s < 1` for all `s ∈ expC x`" makes openness immediate; down-closure is trivial, and every
-- `q < 0` is in the cut with `p = 0`.  For `x = ∞` the cut is `zeroC`.
-- Proved: `negExp-anti`, `negExp-zero : negExp 0 ≋ 1`, `negExp≤1`, `negExp-expC≤1 : e^{−x} e^x ≤ 1`, and
-- for `expC x` bounded by a rational (`∀ s ∈ expC x, s < B`) the reverse `1 ≤ e^{−x} e^x`
-- (`oneC≤negExp-expC`, `negExp-expC`; by LEM, via a near-maximal element of `expC x`), for `x ≤ N` with
-- no side condition (`negExp-expC-nat`, from the bound `exp x ≤ 3ᴺ` of `ExpLower`), and
-- (`Meas-negExp`) `r ↦ e^{−h r}` is threshold-measurable when `h` is, via `Meas-expC` (`expC` is the
-- supremum of measurable partial sums).
module QBS.Analysis.NegExp where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Base using (tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Analysis.RationalLemmas
open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Classical using (LEM₀)

module NegExp (lem : LEM₀) where
  private
    A = LowerRealsOmega lem
  open Exp A using (pw; natE)
  open Series A using (psum)
  open Meas lem
  open LevelSets lem using (Lvl; borel-prop)

  negExp : Cut → Cut
  negExp x = record
    { mem = λ q → Σ ℚᵘ (λ p → q < p × (∀ s → mem (expC lem x) s → p * s < 1ℚᵘ))
    ; down = λ le (p , lt , f) → p , ≤-<-trans le lt , f
    ; open′ = λ (p , lt , f) → let q′ , q<q′ , q′<p = dense lt in q′ , q<q′ , p , q′<p , f
    ; neg = λ {q} lt → 0ℚᵘ , lt , λ s _ → ≃-<ˡ (≃-sym (*-zeroˡ s)) 0<1 }

  negExp-anti : ∀ {x y} → x ⊑ y → negExp y ⊑ negExp x
  negExp-anti xy = mk⊑ (λ q (p , lt , f) → p , lt , λ s m → f s (ap (expC-mono lem xy) s m))

  negExp-cong : ∀ {x y} → x ≋ y → negExp x ≋ negExp y
  negExp-cong e = negExp-anti (proj₂ e) , negExp-anti (proj₁ e)

  -- if `p s < 1` for all `s < 1` then `p ≤ 1`
  bound1 : ∀ {p} → (∀ s → s < 1ℚᵘ → p * s < 1ℚᵘ) → p ≤ 1ℚᵘ
  bound1 {p} f with ≤-or-> p 1ℚᵘ
  ... | inj₁ le = le
  ... | inj₂ 1<p = ⊥-elim (<-irrefl ≃-refl (≤-<-trans (≤-≃ (≃-sym ht))
        (<-trans (*-mono-<-posʳ 0<p t<s) (≃-<ˡ (*-comm p s) (f s s<1)))))
    where
      0<p = <-trans 0<1 1<p
      t = proj₁ (inv 0<p)
      ht = proj₂ (inv 0<p)
      t<1 : t < 1ℚᵘ
      t<1 with ≤-or-> 1ℚᵘ t
      ... | inj₂ lt = lt
      ... | inj₁ 1≤t = ⊥-elim (<-irrefl ≃-refl
            (<-≤-trans 1<p (≤-trans (≤-≃ (≃-sym (*-identityˡ p))) (≤-trans (*-mono-≤-nnʳ (<-≤ 0<p) 1≤t) (≤-≃ ht)))))
      st = dense t<1
      s = proj₁ st
      t<s = proj₁ (proj₂ st)
      s<1 = proj₂ (proj₂ st)

  negExp-zero : negExp zeroC ≋ oneC
  negExp-zero = mk⊑ fwd , mk⊑ bwd
    where
      fwd : ∀ q → mem (negExp zeroC) q → q < 1ℚᵘ
      fwd q (p , lt , f) = <-≤-trans lt (bound1 (λ s s<1 → f s (ap (proj₂ (expC-zero lem)) s s<1)))
      bwd : ∀ q → q < 1ℚᵘ → mem (negExp zeroC) q
      bwd q lt = 1ℚᵘ , lt , λ s m → ≤-<-trans (≤-≃ (*-identityˡ s))
        (proj₁ (expC-zero lem) .ap s m)
        where open _⊑_

  negExp≤1 : ∀ x → negExp x ⊑ oneC
  negExp≤1 x = ⊑-trans (negExp-anti (mk⊑ (λ q lt → neg x lt))) (proj₁ negExp-zero)

  -- `e^{−x} · e^x ≤ 1`
  negExp-expC≤1 : ∀ x → negExp x ⊗ expC lem x ⊑ oneC
  negExp-expC≤1 x = mk⊑ λ { q (inj₁ lt) → <-trans lt 0<1
    ; q (inj₂ (r , s , 0<r , 0<s , (p , r<p , f) , ms , h)) →
        ≤-<-trans h (<-trans (*-mono-<-posʳ 0<s r<p) (f s ms)) }

  ----------------------------------------------------------------------------
  -- the reverse inequality, for `expC x` bounded
  --
  -- Idea: for `0 < ρ < 1` some `s ∈ expC x` has `ρ s′ < s` for every `s′ ∈ expC x` (otherwise
  -- `s₀ + n (1 − ρ) s₀ ≤ s` for some `s ∈ expC x`, for every `n`, against the bound).  With
  -- `t = 1/s` the point `ρ t` witnesses `r ∈ negExp x` for `r` just above `q t`.

  -- `0 < s ≤ ρ s′` with `0 < ρ` forces `0 < s′`
  pos-step : ∀ {ρ s s′} → 0ℚᵘ < ρ → 0ℚᵘ < s → s ≤ ρ * s′ → 0ℚᵘ < s′
  pos-step {ρ} {s} {s′} 0<ρ 0<s hs with pos-or-nonpos s′
  ... | inj₁ p = p
  ... | inj₂ np = ⊥-elim (<-irrefl ≃-refl (<-≤-trans 0<s (≤-trans hs
        (≤-trans (*-mono-≤-nn (<-≤ 0<ρ) np) (≤-≃ (≃-trans (*-comm ρ 0ℚᵘ) (*-zeroˡ ρ)))))))

  -- from `a s′ < s` and `t s ≃ 1` get `(a t) s′ < 1`
  scale-lt : ∀ {a t s s′} → 0ℚᵘ < t → t * s ≃ 1ℚᵘ → a * s′ < s → (a * t) * s′ < 1ℚᵘ
  scale-lt {a} {t} {s} {s′} 0<t ht lt = ≃-<ʳ ht (≃-<ˡ (≃-sym (solve 3 (λ a t s → (a :* t) :* s := t :* (a :* s)) ≃-refl a t s′))
    (*-mono-<-pos 0<t lt))

  -- the chain stays above its start
  chain-base : ∀ {s₀ c s} n → 0ℚᵘ < c → s₀ + nat n * c ≤ s → s₀ ≤ s
  chain-base {s₀} {c} n 0<c h = ≤-trans (≤-trans (≤-≃ (≃-sym (+-identityʳ s₀))) (+-mono-≤ (≤-refl {s₀})
    (≤-trans (≤-≃ (≃-sym (*-zeroˡ c))) (*-mono-≤-nnʳ (<-≤ 0<c) (nat-nonneg n))))) h

  -- one step: from `s₀ ≤ s ≤ ρ s′` get `s + (1 − ρ) s₀ ≤ s′`
  climb : ∀ {ρ s₀ s s′} → 0ℚᵘ < ρ → ρ < 1ℚᵘ → 0ℚᵘ < s₀ → s₀ ≤ s → s ≤ ρ * s′ → s + (1ℚᵘ + - ρ) * s₀ ≤ s′
  climb {ρ} {s₀} {s} {s′} 0<ρ ρ<1 0<s₀ s₀≤s hs =
    ≤-trans (+-mono-≤ hs (*-mono-≤-nn (<-≤ (pos-diff ρ<1)) (≤-trans s₀≤s (<-≤ s<s′)))) (≤-≃ (≃-sym split))
    where
      0<s′ = pos-step 0<ρ (<-≤-trans 0<s₀ s₀≤s) hs
      s<s′ : s < s′
      s<s′ = ≤-<-trans hs (≃-<ʳ (*-identityˡ s′) (*-mono-<-posʳ 0<s′ ρ<1))
      split : s′ ≃ ρ * s′ + (1ℚᵘ + - ρ) * s′
      split = solve 2 (λ r s → s := r :* s :+ (con 1ℚᵘ :+ :- r) :* s) ≃-refl ρ s′

  -- a step of the chain
  bump : ∀ {ρ s₀ s s′} n → 0ℚᵘ < ρ → ρ < 1ℚᵘ → 0ℚᵘ < s₀ → s₀ + nat n * ((1ℚᵘ + - ρ) * s₀) ≤ s → s ≤ ρ * s′ →
         s₀ + nat (suc n) * ((1ℚᵘ + - ρ) * s₀) ≤ s′
  bump {ρ} {s₀} n 0<ρ ρ<1 0<s₀ h hs = ≤-trans (≤-≃ reassoc)
    (≤-trans (+-mono-≤ h ≤-refl) (climb 0<ρ ρ<1 0<s₀ (chain-base n (*-pos (pos-diff ρ<1) 0<s₀) h) hs))
    where
      c = (1ℚᵘ + - ρ) * s₀
      reassoc : s₀ + nat (suc n) * c ≃ (s₀ + nat n * c) + c
      reassoc = ≃-trans (+-cong (≃-refl {s₀}) (nat-suc* n c)) (≃-sym (+-assoc s₀ (nat n * c) c))

  -- under LEM: a near-maximal element
  near-max : ∀ x B → (∀ s → mem (expC lem x) s → s < B) → ∀ ρ → 0ℚᵘ < ρ → ρ < 1ℚᵘ →
             Σ ℚᵘ (λ s → mem (expC lem x) s × 0ℚᵘ < s × (∀ s′ → mem (expC lem x) s′ → ρ * s′ < s))
  near-max x B bd ρ 0<ρ ρ<1 with lem (Σ ℚᵘ (λ s → mem (expC lem x) s × 0ℚᵘ < s × (∀ s′ → mem (expC lem x) s′ → ρ * s′ < s)))
  ... | inj₁ w = w
  ... | inj₂ no = ⊥-elim (<-irrefl ≃-refl (≤-<-trans (≤-trans arch-le (≤-trans (≤-≃ (≃-sym (+-identityˡ (nat k * c))))
        (≤-trans (+-mono-≤ (<-≤ 0<s₀) (≤-refl {nat k * c})) lo))) (bd s₁ ms₁)))
    where
      S = expC lem x
      step : ∀ s → mem S s → 0ℚᵘ < s → Σ ℚᵘ (λ s′ → mem S s′ × s ≤ ρ * s′)
      step s ms 0<s with lem (Σ ℚᵘ (λ s′ → mem S s′ × s ≤ ρ * s′))
      ... | inj₁ w = w
      ... | inj₂ none = ⊥-elim (no (s , ms , 0<s , λ s′ ms′ → not-≤⇒< (λ le → none (s′ , ms′ , le))))
      -- some positive element of `expC x`, from `1 + x ≤ expC x`
      da = dense (0<1)
      a = proj₁ da
      0<a = proj₁ (proj₂ da)
      a<1 = proj₂ (proj₂ da)
      db = dense 0<a
      s₀ = proj₁ db
      0<s₀ = proj₁ (proj₂ db)
      s₀<a = proj₂ (proj₂ db)
      m₀ : mem S s₀
      m₀ = ap (1+≤expC lem x) s₀ (a , s₀ + - a , a<1 , neg x (neg-diff s₀<a) , ≤-≃ (≃-sym (add-sub a s₀)))
      c = (1ℚᵘ + - ρ) * s₀
      0<c = *-pos (pos-diff ρ<1) 0<s₀
      chain : ∀ n → Σ ℚᵘ (λ s → mem S s × s₀ + nat n * c ≤ s)
      chain zero = s₀ , m₀ , ≤-≃ (≃-trans (+-cong (≃-refl {s₀}) (*-zeroˡ c)) (+-identityʳ s₀))
      chain (suc n) with chain n
      ... | s , ms , h with step s ms (<-≤-trans 0<s₀ (chain-base n 0<c h))
      ... | s′ , ms′ , hs = s′ , ms′ , bump n 0<ρ ρ<1 0<s₀ h hs
      k = proj₁ (arch B 0<c)
      arch-le = proj₂ (arch B 0<c)
      s₁ = proj₁ (chain k)
      ms₁ = proj₁ (proj₂ (chain k))
      lo = proj₂ (proj₂ (chain k))

  -- the product is reached once a near-maximal `s` for `q′ > q ≥ 0` is known
  reach : ∀ x {q q′ s} → 0ℚᵘ ≤ q → q < q′ → 0ℚᵘ < s → mem (expC lem x) s →
          (∀ s′ → mem (expC lem x) s′ → q′ * s′ < s) → mem (negExp x ⊗ expC lem x) q
  reach x {q} {q′} {s} 0≤q q<q′ 0<s ms hs =
    inj₂ (r , s , 0<r , 0<s , (q′ * t , r<p , λ s′ ms′ → scale-lt 0<t ht (hs s′ ms′)) , ms
         , ≤-trans (≤-≃ (≃-sym qts)) (<-≤ (*-mono-<-posʳ 0<s qt<r)))
    where
      t = proj₁ (inv 0<s)
      ht = proj₂ (inv 0<s)
      0<t = pos-inv 0<s ht
      rr = dense (*-mono-<-posʳ 0<t q<q′)
      r = proj₁ rr
      qt<r = proj₁ (proj₂ rr)
      r<p = proj₂ (proj₂ rr)
      0≤qt : 0ℚᵘ ≤ q * t
      0≤qt = ≤-trans (≤-≃ (≃-sym (*-zeroˡ t))) (*-mono-≤-nnʳ (<-≤ 0<t) 0≤q)
      0<r = ≤-<-trans 0≤qt qt<r
      qts : (q * t) * s ≃ q
      qts = ≃-trans (*-assoc q t s) (≃-trans (*-cong (≃-refl {q}) ht) (P-id q))

  oneC≤negExp-expC : ∀ x B → (∀ s → mem (expC lem x) s → s < B) → oneC ⊑ negExp x ⊗ expC lem x
  oneC≤negExp-expC x B bd = mk⊑ go
    where
      go : ∀ q → q < 1ℚᵘ → mem (negExp x ⊗ expC lem x) q
      go q lt with neg-or-nonneg q
      ... | inj₁ q<0 = inj₁ q<0
      ... | inj₂ 0≤q with dense lt
      ... | q′ , q<q′ , q′<1 with near-max x B bd q′ (≤-<-trans 0≤q q<q′) q′<1
      ... | s , ms , 0<s , hs = reach x 0≤q q<q′ 0<s ms hs

  negExp-expC : ∀ x B → (∀ s → mem (expC lem x) s → s < B) → negExp x ⊗ expC lem x ≋ oneC
  negExp-expC x B bd = negExp-expC≤1 x , oneC≤negExp-expC x B bd

  -- for finite `x` (`x ≤ N`) the bound is automatic (`expC-bound`)
  negExp-expC-nat : ∀ x N → x ⊑ natE N → negExp x ⊗ expC lem x ≋ oneC
  negExp-expC-nat x N h = negExp-expC x (pow3 lem N) (expC-bound lem x N h)

  ----------------------------------------------------------------------------
  -- measurability

  Meas-pw : ∀ {h} → Meas h → ∀ k → Meas (λ r → pw (h r) k)
  Meas-pw mh zero = Meas-const oneC
  Meas-pw {h} mh (suc k) = Meas-⊗ {h} {λ r → pw (h r) k} mh (Meas-pw mh k)

  Meas-psum : ∀ (a : ℕ → R₁ → Cut) → (∀ n → Meas (a n)) → ∀ N → Meas (λ x → psum (λ n → a n x) N)
  Meas-psum a ma zero = Meas-const zeroC
  Meas-psum a ma (suc N) = Meas-⊕ {λ x → psum (λ n → a n x) N} {a N} (Meas-psum a ma N) (ma N)

  Meas-expC : ∀ {h} → Meas h → Meas (λ r → expC lem (h r))
  Meas-expC {h} mh = Meas-⨆ {λ r → expC lem (h r)} (λ N r → psum (λ n → term lem (h r) n) N)
    (Meas-psum (λ n r → term lem (h r) n) (λ n → Meas-⊗ {λ _ → ι lem n} {λ r → pw (h r) n} (Meas-const (ι lem n)) (Meas-pw mh n)))
    (λ r → ≋-refl)

  -- a Borel set implying a proposition
  borel-imp : ∀ {E : Pred} (B : Set) → Borel E → Borel (λ c → E c → B)
  borel-imp B bE with lem B
  ... | inj₁ b = resp (λ c → (λ _ _ → b) , (λ _ → tt)) ⊤-borel
  ... | inj₂ nb = resp (λ c → (λ f e → ⊥-elim (f e)) , (λ g e → nb (g e))) (compl bE)

  Meas-negExp : ∀ {h} → Meas h → Meas (λ r → negExp (h r))
  Meas-negExp {h} mh q = ex-enum (λ p c → q < p × (∀ s → Lvl (λ r → expC lem (h r)) s c → p * s < 1ℚᵘ))
    (λ p → inter₂ (borel-prop (q < p)) (all-enum (λ s c → Lvl (λ r → expC lem (h r)) s c → p * s < 1ℚᵘ)
      (λ s → borel-imp (p * s < 1ℚᵘ) (Meas-expC mh s))))
