{-# OPTIONS --safe --without-K #-}

-- Pointwise suprema, infima, lim inf and lim sup of sequences of tests on any X, and monotone convergence for `∫ᴹ`
-- (plan 03, "Dominated convergence").
--   * `supH h` and `infH h` (x ↦ ⋃ₙ h n x and x ↦ ⋂ₙ h n x) are tests: random elements go to measurable functions by
--     `Meas.Meas-⨆` and `Meas-inter`; `supH-pt`, `infH-pt` hold by `≋-refl`;
--   * `liminfH h`, `limsupH h`, with `liminfH-pt`, `limsupH-pt` against `LowerRealsInf.liminfC`/`limsupC`;
--   * `∫ᴹ-monoX`: monotonicity of `∫ᴹ` on any X; `∫ᴹ-sup`: monotone convergence for increasing sequences.
-- Route: `Meas-inter`: Lvl (⋂ hs) q = ⋃_{q′ > q} ⋂ₙ Lvl (hs n) q′, a countable union over rationals (enumerate as in
-- `Meas.Meas-⊕`) of countable intersections (`Borel.⋂`).  `∫ᴹ-monoX` and `∫ᴹ-sup` unfold `∫ᴹ p f = J (m p) (ψ p f)`
-- and use `J-mono` and `J-⨆` (`Analysis/Lebesgue`); ψ p (supH h) r is the weight times the union, so `⊗-union`.
module QBS.Continuous.SupTest where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Level using (lift)
open import Data.Rational.Unnormalised.Base using (_<_)
open import QBS.Borel.Core using (⋂; inter₂)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.LowerReals using (module Cut; Cut; unionC; _≋_; ≋-refl; ≋-trans; ⊑-refl; ⊗-mono; ⊗-union; ⊗-cong)
open import QBS.Analysis.LowerRealsInf using (interC; liminfC; limsupC; union-mono; inter-mono)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)

-- the union and the interior of the intersection respect `≋`
union-cong : ∀ {c d} → (∀ n → c n ≋ d n) → unionC c ≋ unionC d
union-cong e = union-mono (λ n → proj₁ (e n)) , union-mono (λ n → proj₂ (e n))

inter-cong : ∀ {c d} → (∀ n → c n ≋ d n) → interC c ≋ interC d
inter-cong e = inter-mono (λ n → proj₁ (e n)) , inter-mono (λ n → proj₂ (e n))

open Cut using (mem)

module SupTest (lem : LEM₀) where
  open Lebesgue lem using (A; J-mono; J-⨆)
  open OmegaSemiring A using (_≈_; _≤_)
  open Meas lem using (Meas; Meas-⨆; ex-enum)
  open LevelSets lem using (borel-prop)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; ψ; mψ; module C)
  open C.Pre using (m; α)
  open QBS
  open Hom

  Meas-inter : ∀ (hs : ℕ → R₁ → Cut) → (∀ n → Meas (hs n)) → Meas (λ r → interC (λ n → hs n r))
  Meas-inter hs ms q = ex-enum (λ ρ c → (q < ρ) × (∀ n → mem (hs n (lift c)) ρ))
    (λ ρ → inter₂ (borel-prop (q < ρ)) (⋂ (λ n → ms n ρ)))

  module _ {X : QBS S} where

    -- x ↦ ⋃ₙ h n x and x ↦ ⋂ₙ h n x
    supH infH : (ℕ → Hom S X WQ) → Hom S X WQ
    supH h = record
      { map = record { to = λ x → unionC (λ n → map (h n) ⟨$⟩ x); cong = λ e → union-cong (λ n → Func.cong (map (h n)) e) }
      ; map-random = λ {γ} m → Meas-⨆ {λ r → unionC (λ n → map (h n) ⟨$⟩ (γ ⟨$⟩ r))}
          (λ n r → map (h n) ⟨$⟩ (γ ⟨$⟩ r)) (λ n → map-random (h n) {γ} m) (λ r → ≋-refl) }
    infH h = record
      { map = record { to = λ x → interC (λ n → map (h n) ⟨$⟩ x); cong = λ e → inter-cong (λ n → Func.cong (map (h n)) e) }
      ; map-random = λ {γ} m → Meas-inter (λ n r → map (h n) ⟨$⟩ (γ ⟨$⟩ r)) (λ n → map-random (h n) {γ} m) }

    supH-pt : ∀ h x → map (supH h) ⟨$⟩ x ≈ unionC (λ n → map (h n) ⟨$⟩ x)
    supH-pt h x = ≋-refl

    infH-pt : ∀ h x → map (infH h) ⟨$⟩ x ≈ interC (λ n → map (h n) ⟨$⟩ x)
    infH-pt h x = ≋-refl

    liminfH limsupH : (ℕ → Hom S X WQ) → Hom S X WQ
    liminfH h = supH (λ n → infH (λ k → h (n +ℕ k)))
    limsupH h = infH (λ n → supH (λ k → h (n +ℕ k)))

    liminfH-pt : ∀ h x → map (liminfH h) ⟨$⟩ x ≈ liminfC (λ n → map (h n) ⟨$⟩ x)
    liminfH-pt h x = ≋-refl

    limsupH-pt : ∀ h x → map (limsupH h) ⟨$⟩ x ≈ limsupC (λ n → map (h n) ⟨$⟩ x)
    limsupH-pt h x = ≋-refl

    -- monotonicity and monotone convergence
    ∫ᴹ-monoX : ∀ (p : C.Pre (XW X)) {f g : Hom S X WQ} → (∀ x → map f ⟨$⟩ x ≤ map g ⟨$⟩ x) → ∫ᴹ {X} p f ≤ ∫ᴹ {X} p g
    ∫ᴹ-monoX p {f} {g} le =
      J-mono (m p) {ψ {X} p f} {ψ {X} p g} (mψ {X} p f) (mψ {X} p g) (λ r → ⊗-mono ⊑-refl (le _))

    ∫ᴹ-sup : ∀ (p : C.Pre (XW X)) (h : ℕ → Hom S X WQ) → (∀ n x → map (h n) ⟨$⟩ x ≤ map (h (suc n)) ⟨$⟩ x) →
      ∫ᴹ {X} p (supH h) ≈ unionC (λ n → ∫ᴹ {X} p (h n))
    ∫ᴹ-sup p h inc =
      J-⨆ (m p) {ψ {X} p (supH h)} (λ n → ψ {X} p (h n)) (λ n → mψ {X} p (h n))
        (λ r n → ⊗-mono ⊑-refl (inc n _)) (mψ {X} p (supH h))
        (λ r → ≋-trans (⊗-cong ≋-refl (supH-pt h _)) (⊗-union _ _))
