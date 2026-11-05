{-# OPTIONS --safe --without-K #-}

-- The difference of two lower cuts, for the translation of Lebesgue measure (`LebesgueShift`).  For cuts t ⊑ b with t
-- bounded by a rational, `diffC t b` is the cut of q such that q′ + s ∈ b for some q′ > q and all s ∈ t, and
--   * `diff-sum`: `t ⊕ diffC t b ≋ b`;
--   * `diff-⇐`: `b ⊑ x ⊕ t` gives `diffC t b ⊑ x`, for every x (also x = ∞), without cancellation;
--   * `top-sub`: if x ⊕ t contains every rational then so does x.
module QBS.Continuous.LebesgueShiftCut where

open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.Sum.Base using ([_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _<_; -_)

open import QBS.Classical using (LEM₀)
open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut using (mem; down; open′; neg)
open _⊑_ using (ap)
open import QBS.Analysis.LowerInverse using (module InvClassical)
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; :-_; _:=_)

module LebesgueShiftCut (lem : LEM₀) where
  open InvClassical lem using (near-sup′)

  diffC : ∀ t b → t ⊑ b → Cut
  diffC t b tb = record
    { mem = λ q → Σ ℚᵘ (λ q′ → q < q′ × (∀ s → mem t s → mem b (q′ + s)))
    ; down = λ le (q′ , lt , h) → q′ , ≤-<-trans le lt , h
    ; open′ = λ {q} (q′ , lt , h) → let q″ , a , c = dense lt in q″ , a , q′ , c , h
    ; neg = λ {p} p<0 → 0ℚᵘ , p<0 , (λ s ms → down b (≤-≃ (+-identityˡ s)) (ap tb s ms)) }

  -- t ⊕ diffC ⊑ b
  diff-⊑ : ∀ t b tb → t ⊕ diffC t b tb ⊑ b
  diff-⊑ t b tb = mk⊑ (λ q (r , s , mr , (s′ , lt , h) , le) →
    down b (≤-trans le (≤-trans (+-mono-≤ (≤-refl {r}) (<-≤ lt)) (≤-≃ (+-comm r s′)))) (h r mr))

  -- b ⊑ t ⊕ diffC, for t bounded
  diff-⊒ : ∀ t b tb M → (∀ r → mem t r → r < M) → b ⊑ t ⊕ diffC t b tb
  diff-⊒ t b tb M bd = mk⊑ (λ q mq →
    let q₁ , q<q₁ , m₁ = open′ b mq
        q₂ , q₁<q₂ , m₂ = open′ b m₁
        ε = q₂ + - q₁
        r , mr , hr = near-sup′ t M bd (pos-diff q₁<q₂)
        s = q + - r
        s′ = q₁ + - r
        s<s′ : s < s′
        s<s′ = +-mono-<-≤ q<q₁ (≤-refl {(- r)})
        ok : ∀ u → mem t u → mem b (s′ + u)
        ok u mu = down b (≤-trans (+-mono-≤ (≤-refl {s′}) (hr u mu))
          (≤-≃ (solve 3 (λ q₁ r q₂ → (q₁ :+ :- r) :+ (r :+ (q₂ :+ :- q₁)) := q₂) ≃-refl q₁ r q₂))) m₂
    in r , s , mr , (s′ , s<s′ , ok) , ≤-≃ (≃-sym (add-sub r q)))

  diff-sum : ∀ t b tb M → (∀ r → mem t r → r < M) → t ⊕ diffC t b tb ≋ b
  diff-sum t b tb M bd = diff-⊑ t b tb , diff-⊒ t b tb M bd

  -- b ⊑ x ⊕ t gives diffC ⊑ x
  diff-⇐ : ∀ t b tb M → (∀ r → mem t r → r < M) → ∀ x → b ⊑ x ⊕ t → diffC t b tb ⊑ x
  diff-⇐ t b tb M bd x f = mk⊑ (λ q (q′ , lt , h) →
    [ (λ y → y) , (λ n → ⊥-elim (contra q q′ lt h n)) ]′ (lem (mem x q)))
    where
      contra : ∀ q q′ → q < q′ → (∀ s → mem t s → mem b (q′ + s)) → (mem x q → ⊥) → ⊥
      contra q q′ lt h n =
        let u , mu , hu = near-sup′ t M bd (pos-diff lt)
            r , s , mr , ms , le = ap f (q′ + u) (h u mu)
            r<q : r < q
            r<q = [ (λ q≤r → ⊥-elim (n (down x q≤r mr))) , (λ r<q → r<q) ]′ (≤-or-> q r)
            chain : (q′ + u) < (q′ + u)
            chain = <-≤-trans (≤-<-trans le (+-mono-<-≤ r<q (≤-refl {s})))
              (≤-trans (+-mono-≤ (≤-refl {q}) (hu s ms))
                (≤-≃ (solve 3 (λ q u q′ → q :+ (u :+ (q′ :+ :- q)) := q′ :+ u) ≃-refl q u q′)))
        in <-irrefl ≃-refl chain

  -- ⊤ ⊕ t: if every rational lies in x ⊕ t then in x
  top-sub : ∀ t M → (∀ r → mem t r → r < M) → ∀ x → (∀ q → mem (x ⊕ t) q) → ∀ q → mem x q
  top-sub t M bd x all q =
    let r , s , mr , ms , le = all (q + M)
    in [ (λ q≤r → down x q≤r mr)
       , (λ r<q → ⊥-elim (<-irrefl ≃-refl (≤-<-trans le (+-mono-< r<q (bd s ms))))) ]′ (≤-or-> q r)
