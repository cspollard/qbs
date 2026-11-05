{-# OPTIONS --safe --without-K #-}

-- Infima of sequences of lower cuts, and lim inf / lim sup of sequences (plan 03, "Dominated convergence").
--   * `interC c`: the interior of the intersection, mem q ⟺ ∃ q′ > q with q′ ∈ c n for every n (rounded, so a cut);
--     `inter-lb`, `inter-glb`, `inter-mono`; `union-mono` for `LowerReals.unionC`;
--   * `liminfC c = ⋃ₙ ⋂ₖ c (n + k)` and `limsupC c = ⋂ₙ ⋃ₖ c (n + k)`, with `liminf-limsup : liminf ⊑ limsup`
--     and monotonicity.
-- Route: `neg` for q < 0 takes q′ = q / 2 (or any rational strictly between q and 0); `liminf-limsup` compares the
-- n-th lower term with the m-th upper term through the common index n + m.
module QBS.Analysis.LowerRealsInf where

open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using () renaming (+-comm to +ℕ-comm)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Rational.Unnormalised.Base using (ℚᵘ; _<_)
open import QBS.Analysis.RationalLemmas

open import QBS.Analysis.LowerReals
open Cut
open _⊑_

-- ⋂ₙ c n
interC : (ℕ → Cut) → Cut
interC c = record
  { mem = λ q → Σ ℚᵘ (λ q′ → q < q′ × (∀ n → mem (c n) q′))
  ; down = λ le (q′ , lt , h) → q′ , ≤-<-trans le lt , h
  ; open′ = λ (q′ , lt , h) → let r , q<r , r<q′ = dense lt in r , q<r , q′ , r<q′ , h
  ; neg = λ lt → let r , q<r , r<0 = dense lt in r , q<r , (λ n → neg (c n) r<0) }

inter-lb : ∀ c n → interC c ⊑ c n
inter-lb c n = mk⊑ (λ q (q′ , lt , h) → down (c n) (<-≤ lt) (h n))

inter-glb : ∀ c {b} → (∀ n → b ⊑ c n) → b ⊑ interC c
inter-glb c {b} le = mk⊑ (λ q m →
  let q′ , lt , m′ = open′ b m in q′ , lt , (λ n → ap (le n) q′ m′))

inter-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → interC c ⊑ interC d
inter-mono le = inter-glb _ (λ n → ⊑-trans (inter-lb _ n) (le n))

union-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → unionC c ⊑ unionC d
union-mono {d = d} le = union-lub _ (λ n → ⊑-trans (le n) (union-ub d n))

-- lim inf and lim sup
liminfC limsupC : (ℕ → Cut) → Cut
liminfC c = unionC (λ n → interC (λ k → c (n +ℕ k)))
limsupC c = interC (λ n → unionC (λ k → c (n +ℕ k)))

liminf-limsup : ∀ c → liminfC c ⊑ limsupC c
liminf-limsup c = inter-glb _ (λ m → union-lub _ (λ n →
  ⊑-trans (inter-lb _ m) (mk⊑ (λ q h → n , subst (λ i → mem (c i) q) (+ℕ-comm n m) h))))

liminf-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → liminfC c ⊑ liminfC d
liminf-mono le = union-mono (λ n → inter-mono (λ k → le (n +ℕ k)))

limsup-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → limsupC c ⊑ limsupC d
limsup-mono le = inter-mono (λ n → union-mono (λ k → le (n +ℕ k)))
