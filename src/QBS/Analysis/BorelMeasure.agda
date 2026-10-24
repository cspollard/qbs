{-# OPTIONS --safe --without-K #-}

-- Borel probability measures on Cantor space as σ-additive set functions, valued in the lower-cut
-- reals: the set-function side of the Riesz–Daniell correspondence.  `coinBM` is the fair coin;
-- `Analysis/Functional.agda` turns any `BorelMeasure` into a Daniell functional.
module QBS.Analysis.BorelMeasure where

import Level as L
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Data.Bool.Base using (false)

open import QBS.Borel.Core
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda using (cylTop)
open import QBS.Analysis.Omega
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Clopen using (leaf)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.CoinSets using (module CoinSets)

module BM (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  A : OmegaSemiring (L.suc L.zero)
  A = LowerRealsOmega lem
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Series A

  -- a σ-additive probability measure on the Borel sets
  record BorelMeasure : Set₂ where
    field
      μ : ∀ {U} → Borel U → ∣A∣
      μ-resp : ∀ {U V} (bU : Borel U) (bV : Borel V) → U ≐ V → μ bU ≈ μ bV
      μ-⋃ : ∀ {U : ℕ → Pred} (bs : ∀ n → Borel (U n)) (dj : Disjoint U) →
        μ (⋃ bs) ≈ ∑ᶠ (λ n → μ (bs n))
      μ-⊤ : μ ⊤-borel ≈ 1#
      μ-⊥ : μ ⊥-borel ≈ 0#

  -- the fair coin
  coinBM : BorelMeasure
  coinBM = record
    { μ = CS.μ ; μ-resp = CS.μ-resp ; μ-⋃ = CS.μ-⋃
    ; μ-⊤ = CS.μ-cyl cylTop ⊤-borel
    ; μ-⊥ = CS.μ-unique ⊥-borel (CS.meas-resp {CS.Pt (leaf false)} {λ _ → ⊥} e (CS.meas-clopen (leaf false)))
    }
    where
      module CS = CoinSets lem
      e : CS.Pt (leaf false) ≐ (λ _ → ⊥)
      e x = (λ ()) , (λ ())
