{-# OPTIONS --safe --without-K #-}

-- Convergence with explicit tolerances, and convergence of differences (plan 03, "Signed dominated convergence").
--   * `EConv a l`: for every k, eventually a n ≤ l + ½ᵏ and l ≤ a n + ½ᵏ;  `conv-econv`/`econv-conv`: for finite l
--     this is `Dominated.Conv` (lim inf ≈ lim sup ≈ l);
--   * `SConv a b u v`: "a n − b n → u − v" without subtraction: for every k, eventually a n + v ≤ u + b n + ½ᵏ and
--     u + b n ≤ a n + v + ½ᵏ;  `sconv-pair`: if a → u and b → v then a − b → u − v;  `sconv-shift`: adding the same
--     sequence to both sides of a difference (c n + d n with d → 0) keeps the limit.
-- Route: `econv-conv` with `LowerRealsNear.inter-add` and `Fatou.approx`; `conv-econv` needs, for a decreasing
-- sequence of tail suprema whose infimum is ≤ l, one tail ≤ l + ½ᵏ: by excluded middle, otherwise a rational strictly
-- above l lies in every tail, hence in the infimum (`LowerRealsNear.near-sup-bnd` gives a rational near l).
-- `sconv-pair` with ½ᵏ⁺¹ + ½ᵏ⁺¹ ≈ ½ᵏ (`Half`).
--   Skeleton: holes first.
module QBS.Continuous.ConvEps where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (Σ; _×_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Dominated using (module Dominated)

module ConvEps (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _+_; 0#) renaming (Carrier to ∣A∣; _≤_ to _≤ᴬ_)
  open Bounded A using (Bnd)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open Dominated lem₁ using (Conv)

  -- a n → l, with tolerance ½ᵏ from some index on
  EConv : (ℕ → ∣A∣) → ∣A∣ → Set₁
  EConv a l = ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → (a n ≤ᴬ l + hp k) × (l ≤ᴬ a n + hp k))

  conv-econv : ∀ a l → Bnd l → Conv a l → EConv a l
  conv-econv = ?

  econv-conv : ∀ a l → EConv a l → Conv a l
  econv-conv = ?

  -- a n − b n → u − v
  SConv : (ℕ → ∣A∣) → (ℕ → ∣A∣) → ∣A∣ → ∣A∣ → Set₁
  SConv a b u v = ∀ k → Σ ℕ (λ N → ∀ n → N ≤ n → (a n + v ≤ᴬ u + b n + hp k) × (u + b n ≤ᴬ a n + v + hp k))

  sconv-pair : ∀ a b u v → EConv a u → EConv b v → SConv a b u v
  sconv-pair = ?

  -- (a n + d n) − (b n + e n) → u − v when a − b → u − v and d, e → 0
  sconv-shift : ∀ a b d e u v → SConv a b u v → EConv d 0# → EConv e 0# →
    SConv (λ n → a n + d n) (λ n → b n + e n) u v
  sconv-shift = ?
