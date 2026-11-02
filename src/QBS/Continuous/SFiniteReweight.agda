{-# OPTIONS --safe --without-K #-}

-- Reweighting an s-finite measure by a density: `reweightPre d p` multiplies the weight of every sample of
-- `p : Pre (XW X)` by `d x`, where `d : X ⇒ WQ`.  Its integral is `∫ᴹ (reweightPre d p) f ≈ ∫ᴹ p (d · f)`
-- (`∫ᴹ-reweight`), with `d · f = mulW ∘ ⟨d, f⟩` the pointwise product (`mulH`).  Generalises `scalePre`
-- (constant `d`) and is the density of a measure as a morphism of `Pre`s (cf. `Analysis/Density` for `Measure`s).

module QBS.Continuous.SFiniteReweight where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₂ₛ)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; pairQ)
open import QBS.Analysis.Omega
open import QBS.Analysis.Measure
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Classical using (LEM₀)

module SFiniteReweight (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Weights lem using (WQ; mulW)
  open OmegaSemiring A using (_≈_; _*_; *-cong; *-assoc)
  open Integration A
  open SFinite lem
  open C using (Pre; mk)
  open C.Pre
  open QBS
  open Hom

  -- the pointwise product of two weight-valued tests
  mulH : ∀ {X : QBS S} → Hom S X WQ → Hom S X WQ → Hom S X WQ
  mulH {X} d f = _∘H_ S {X} {_×Q_ S WQ WQ} {WQ} mulW (pairQ S {X} {WQ} {WQ} d f)

  -- multiply the weight of each sample by the density at its point
  reweightPre : ∀ {X : QBS S} → Hom S X WQ → Pre (XW X) → Pre (XW X)
  reweightPre {X} d p = mk (rwₛ ∘ₛ α p)
    (Meas-⊗ {λ r → proj₁ (α p ⟨$⟩ r)} {λ r → map d ⟨$⟩ proj₂ (α p ⟨$⟩ r)}
       (proj₁ (α-random p)) (map-random d {proj₂ₛ ∘ₛ α p} (proj₂ (α-random p))) , proj₂ (α-random p))
    (m p) (ok p)
    where
      rwₛ : Func (Carrier (XW X)) (Carrier (XW X))
      rwₛ = record { to = λ (w , x) → w * (map d ⟨$⟩ x) , x
                   ; cong = λ { (e₁ , e₂) → *-cong e₁ (Func.cong (map d) e₂) , e₂ } }

  ∫ᴹ-reweight : ∀ {X : QBS S} (d : Hom S X WQ) (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} (reweightPre {X} d p) f ≈ ∫ᴹ {X} p (mulH {X} d f)
  ∫ᴹ-reweight {X} d p f = J-cong (m p) {ψ {X} (reweightPre {X} d p) f} {ψ {X} p (mulH {X} d f)}
    (mψ {X} (reweightPre {X} d p) f) (mψ {X} p (mulH {X} d f))
    (λ r → *-assoc (proj₁ (α p ⟨$⟩ r)) (map d ⟨$⟩ proj₂ (α p ⟨$⟩ r)) (map f ⟨$⟩ proj₂ (α p ⟨$⟩ r)))
