{-# OPTIONS --safe --without-K #-}

-- Bounded signed test functions on a QBS, and their pull-back along a random element to the ring of bounded signed random
-- variables (`Analysis/BoundedRing`).  See `plans/03-bayesian-frequentist.md`, "3c in detail".
--
--   * `CutQ`: the QBS of lower cuts (values in [0,∞]) whose random elements are the measurable functions `Meas`.  Unlike the
--     bounded signed values `Sg`, it has no boundedness requirement, so gluing is unproblematic.
--   * `STest X`: a signed test on `X`, a pair of maps `X ⇒ CutQ` with a common natural bound; it stands for `pos − neg`.
--   * `pullback g α pm`: the signed random variable `g ∘ α` on a probability space, for a random element `α`.
module QBS.Continuous.SignedTests where

open import Data.Empty using (⊥)
open import Level using (lower)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
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
  open Lebesgue lem using (A; J; J-mono)
  open Meas lem using (Meas; Meas-ext; Meas-const; Meas-pre; Meas-glue)
  open Integration A using (Measure; IsProb)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ) using (_≤_; ≤-trans; ≤-reflexive)
  open Bounded A using (nat; Bnd)
  open SignedIntegral lem using (SF; J-const)
  open BoundedRing lem using (BSF)

  ----------------------------------------------------------------------------
  -- the QBS of lower cuts

  CutQ : QBS S
  CutQ = record
    { Carrier = Aˢ
    ; Random = Meas
    ; random-resp = λ e m → Meas-ext e m
    ; random-cong = λ m e → Meas-resp m (lower e)
    ; const-random = λ c → Meas-const c
    ; pre-random = λ m mf → Meas-pre m mf
    ; glue-random = λ pj α m → Meas-glue pj m
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
  J-bounded {m} pm {h} mh N b = N , ≤-trans (J-mono m mh (Meas-const (nat N)) b) (≤-reflexive (J-const pm (nat N)))

  -- the signed random variable g ∘ α, on a probability space, for a random element α
  pullback : ∀ {X : QBS S} (g : STest X) {α : R₁ → QBS.∣ X ∣} → QBS.Random X α →
    ∀ (m : Measure) (pm : IsProb m) → BSF m pm
  pullback g {α} r m pm = sf , STest.bound g , λ x → STest.pos-bdd g (α x) , STest.neg-bdd g (α x)
    where
    mp = Hom.map-random (STest.pos g) r
    mn = Hom.map-random (STest.neg g) r
    sf : SF m
    sf = record
      { f⁺ = λ x → Hom.map (STest.pos g) ⟨$⟩ α x
      ; f⁻ = λ x → Hom.map (STest.neg g) ⟨$⟩ α x
      ; f⁺-meas = mp
      ; f⁻-meas = mn
      ; f⁺-int = J-bounded pm mp (STest.bound g) (λ x → STest.pos-bdd g (α x))
      ; f⁻-int = J-bounded pm mn (STest.bound g) (λ x → STest.neg-bdd g (α x))
      }
