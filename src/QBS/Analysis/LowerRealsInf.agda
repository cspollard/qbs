{-# OPTIONS --safe --without-K #-}

-- Infima of sequences of lower cuts, and lim inf / lim sup of sequences (plan 03, "Dominated convergence").
--   * `interC c`: the interior of the intersection, mem q ⟺ ∃ q′ > q with q′ ∈ c n for every n (rounded, so a cut);
--     `inter-lb`, `inter-glb`, `inter-mono`; `union-mono` for `LowerReals.unionC`;
--   * `liminfC c = ⋃ₙ ⋂ₖ c (n + k)` and `limsupC c = ⋂ₙ ⋃ₖ c (n + k)`, with `liminf-limsup : liminf ⊑ limsup`
--     and monotonicity.
-- Route: `neg` for q < 0 takes q′ = q / 2 (or any rational strictly between q and 0); `liminf-limsup` compares the
-- n-th lower term with the m-th upper term through the common index n + m.
--   Skeleton: holes first.
module QBS.Analysis.LowerRealsInf where

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)

open import QBS.Analysis.LowerReals

-- ⋂ₙ c n
interC : (ℕ → Cut) → Cut
interC = ?

inter-lb : ∀ c n → interC c ⊑ c n
inter-lb = ?

inter-glb : ∀ c {b} → (∀ n → b ⊑ c n) → b ⊑ interC c
inter-glb = ?

inter-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → interC c ⊑ interC d
inter-mono = ?

union-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → unionC c ⊑ unionC d
union-mono = ?

-- lim inf and lim sup
liminfC limsupC : (ℕ → Cut) → Cut
liminfC c = unionC (λ n → interC (λ k → c (n +ℕ k)))
limsupC c = interC (λ n → unionC (λ k → c (n +ℕ k)))

liminf-limsup : ∀ c → liminfC c ⊑ limsupC c
liminf-limsup = ?

liminf-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → liminfC c ⊑ liminfC d
liminf-mono = ?

limsup-mono : ∀ {c d} → (∀ n → c n ⊑ d n) → limsupC c ⊑ limsupC d
limsup-mono = ?
