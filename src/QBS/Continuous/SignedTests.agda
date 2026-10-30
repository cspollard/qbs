{-# OPTIONS --safe --without-K #-}

-- Bounded signed test functions on a QBS, and their pull-back along a random element to the ring of bounded signed random
-- variables (`Analysis/BoundedRing`).  See `plans/03-bayesian-frequentist.md`, "3c in detail".
--
--   * `CutQ`: the QBS of lower cuts (values in [0,∞]) whose random elements are the measurable functions `Meas`.  Unlike the
--     bounded signed values `Sg`, it has no boundedness requirement, so gluing is unproblematic.
--   * `STest X`: a signed test on `X`, a pair of maps `X ⇒ CutQ` with a common natural bound; it stands for `pos − neg`.
--   * `pullback g α pm`: the signed random variable `g ∘ α` on a probability space, for a random element `α`.
--
-- SKELETON: the declarations are in place; the proofs marked by holes are the plan's next steps.
module QBS.Continuous.SignedTests where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Borel.Source using (R₁; cantorSource)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Continuous.Sample using (S)

module SignedTests (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open Lebesgue lem using (A; J)
  open Meas lem using (Meas; Meas-ext; Meas-const; Meas-pre; Meas-glue)
  open Integration A using (Measure; IsProb)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ) using (_≤_)
  open Bounded A using (nat; Bnd)
  open SignedIntegral lem using (SF)
  open BoundedRing lem using (BSF)

  ----------------------------------------------------------------------------
  -- the QBS of lower cuts

  CutQ : QBS S
  CutQ = record
    { Carrier = Aˢ
    ; Random = Meas
    ; random-resp = λ e m → ?   -- `Meas-ext`
    ; const-random = λ c → ?    -- `Meas-const`
    ; pre-random = λ m mf → ?   -- `Meas-pre`
    ; glue-random = λ pj α m → ?  -- `Meas-glue`
    }

  ----------------------------------------------------------------------------
  -- bounded signed tests

  -- a signed test `pos − neg` on X, both parts bounded by the natural number `bound`
  record STest (X : QBS S) : Set₁ where
    field
      pos neg : Hom S X CutQ
      bound : ℕ
      pos-bdd : ∀ x → (Hom.map pos ⟨$⟩ x) ≤ nat bound
      neg-bdd : ∀ x → (Hom.map neg ⟨$⟩ x) ≤ nat bound

  -- a bounded measurable function has a bounded integral against a probability measure
  J-bounded : ∀ {m} → IsProb m → ∀ {h} (mh : Meas h) (N : ℕ) → (∀ x → h x ≤ nat N) → Bnd (J m h mh)
  J-bounded pm mh N b = ?   -- monotonicity of `J` and `J-const`: J h ≤ J (const N) = N

  -- the signed random variable g ∘ α, on a probability space, for a random element α
  pullback : ∀ {X : QBS S} (g : STest X) {α : R₁ → QBS.∣ X ∣} → QBS.Random X α →
    ∀ (m : Measure) (pm : IsProb m) → BSF m pm
  pullback g r m pm = ?   -- f⁺ = pos ∘ α, f⁻ = neg ∘ α (measurable by `map-random`), integrals bounded by `J-bounded`
