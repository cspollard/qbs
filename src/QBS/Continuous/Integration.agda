{-# OPTIONS --safe --without-K #-}

-- The continuous measures on Cantor space are an `Integration` (`QBS.Integration`).  A `Measure` is already an
-- integration functional on the measurable functions, so `∫` is the evaluation `I`; its naturality is the
-- definition of `push`.  Test functions are the measurable functions `Σ h, Fun h` (equal when pointwise equal),
-- acted on by precomposition with measurable maps; measures are the admissible `Σ m, Ok m` (equal when all
-- integrals agree), acted on by `push`.  Both actions respect `≈` of Cantor space because measurable functions do
-- (`Fun-resp`, which uses excluded middle).
module QBS.Continuous.Integration where

import Level as L
open import Level using (lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.SubCategory using (SubCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.NaturalTransformation using (ntHelper)

open import QBS.Core using (RandomSource)
open import QBS.Integration using (Integration; RawIntegration; fromRaw)
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Classical using (LEM₀)

module ContinuousIntegration (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) (K : Integration.MeasureClass A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open QBS.Analysis.Measure.Integration A
  open MeasureClass K
  open RandomSource cantorSource using (subcat)

  -- the one-object category of measurable maps of Cantor space
  𝕄 = SubCategory (Setoids (L.suc L.zero) (L.suc L.zero)) subcat

  -- measurable test functions, equal when pointwise equal
  TestS : Setoid (L.suc L.zero) (L.suc L.zero)
  TestS = record
    { Carrier = Σ (R₁ → ∣A∣) Fun
    ; _≈_ = λ (h , _) (h′ , _) → ∀ x → h x ≈ h′ x
    ; isEquivalence = record
        { refl = λ _ → refl
        ; sym = λ e x → sym (e x)
        ; trans = λ e e′ x → trans (e x) (e′ x)
        }
    }

  -- test functions are a presheaf: precomposition with a measurable map
  Test : Presheaf 𝕄 (Setoids (L.suc L.zero) (L.suc L.zero))
  Test = record
    { F₀ = λ _ → TestS
    ; F₁ = λ f → record
        { to = λ (h , fh) → (λ x → h (proj₁ f ⟨$⟩ x)) , Fun-pre fh (proj₂ f)
        ; cong = λ e x → e _
        }
    ; identity = λ _ → refl
    ; homomorphism = λ _ → refl
    ; F-resp-≈ = λ e {(_ , fh)} x → Fun-resp lem fh (lower e)
    }

  -- admissible measures, pushed forward, integrated by `I`; the projection formula is the definition of `push`
  continuousRaw : RawIntegration Test Aˢ
  continuousRaw = record
    { Raw = λ _ → Σ Measure Ok
    ; push = λ f (m , ok) → push (proj₂ f) m , ok-push (proj₂ f) ok
    ; ⟦_⟧ = λ (m , _) → record
        { to = λ (h , fh) → I m h fh
        ; cong = λ {(h , fh)} {(h′ , fh′)} e → I-cong m e fh fh′
        }
    ; ⟦⟧-push = λ _ _ → refl
    }

  continuousIntegration : Integration Test Aˢ
  continuousIntegration = fromRaw Test Aˢ continuousRaw
