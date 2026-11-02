{-# OPTIONS --safe --without-K #-}

-- `e^{−x}` on the lower reals [0, ∞], as a cut defined directly (there is no negation or division):
--   q ∈ negExp x  iff  ∃ p > q, ∀ s ∈ expC x, p · s < 1,
-- i.e. `q · e^x < 1` with room to spare.  Stating it with a witness `p > q` rather than as
-- "`q · s < 1` for all `s ∈ expC x`" makes openness immediate; down-closure is trivial, and every
-- `q < 0` is in the cut with `p = 0`.  For `x = ∞` the cut is `zeroC`.
-- Proved: `negExp-anti`, `negExp-zero : negExp 0 ≋ 1`, `negExp≤1`, `negExp-expC≤1 : e^{−x} e^x ≤ 1`, and
-- (`Meas-negExp`) `r ↦ e^{−h r}` is threshold-measurable when `h` is, via `Meas-expC` (`expC` is the
-- supremum of measurable partial sums).
module QBS.Analysis.NegExp where

open import Level using (lift; lower)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)

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
  open Exp A using (pw)
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
