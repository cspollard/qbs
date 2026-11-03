{-# OPTIONS --safe --without-K #-}

-- Monotone functions are tests (plan 03, "Tests and the real line").
-- For F : [0,∞] → [0,∞] respecting ≈ and increasing (or decreasing), `F ∘ α` is threshold-measurable whenever α is,
-- so F is a morphism `monoH F : WQ ⇒ WQ` (`antiH F` for decreasing F) with no measurability proof from the user.
-- Route: the threshold set U = {x | q ∈ F x} is an up-set (a down-set).  With excluded middle it is the union of the
-- countably many {x | d ≤ x} over the rationals d ∈ U (`Intervals.ge-borel`), plus possibly the single point inf U,
-- which is Borel as {x | inf U ≤ x} minus the union of the {q ∈ x} for rationals q ∉ inf U.
module QBS.Continuous.MonoTest where

open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.MonoTestAlg using (module MonoAlg)
open import Level using (lift)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import QBS.Borel.Core using (compl; resp)
open import Data.Sum.Base using (inj₁; inj₂)
open import QBS.Analysis.LowerReals using (module Cut; _⊑_)
open Cut using (mem)
open _⊑_ using (ap)

module MonoTest (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_) renaming (Carrier to ∣A∣)
  open Meas (lemOf lem₁) using (Meas)
  open Weights (lemOf lem₁) using (WQ)
  open MonoAlg lem₁ using (up-borel)
  open QBS
  open Hom

  module _ (F : ∣A∣ → ∣A∣) (cF : ∀ {x y} → x ≈ y → F x ≈ F y) where

    -- increasing functions
    Meas-mono : (∀ {x y} → x ≤ y → F x ≤ F y) → ∀ {α} → Meas α → Meas (λ r → F (α r))
    Meas-mono mF {α} m q = up-borel (λ x → mem (F x) q) (λ e → ap (proj₁ (cF e)) q) (λ le → ap (mF le) q) m

    monoH : (∀ {x y} → x ≤ y → F x ≤ F y) → Hom S WQ WQ
    monoH mF = record { map = record { to = F ; cong = cF } ; map-random = λ {γ} m → Meas-mono mF {γ ⟨$⟩_} m }

    -- decreasing functions
    Meas-anti : (∀ {x y} → x ≤ y → F y ≤ F x) → ∀ {α} → Meas α → Meas (λ r → F (α r))
    Meas-anti aF {α} m q = resp (λ c → dne , (λ u nn → nn u)) (compl (up-borel V Vc Vu m))
      where
        V : ∣A∣ → Set
        V x = mem (F x) q → ⊥
        Vc : ∀ {x y} → x ≈ y → V x → V y
        Vc e n u = n (ap (proj₂ (cF e)) q u)
        Vu : ∀ {x y} → x ≤ y → V x → V y
        Vu le n u = n (ap (aF le) q u)
        dne : ∀ {c} → ((mem (F (α (lift c))) q → ⊥) → ⊥) → mem (F (α (lift c))) q
        dne {c} nn = case lemOf lem₁ (mem (F (α (lift c))) q) of λ { (inj₁ u) → u ; (inj₂ n) → ⊥-elim (nn n) }

    antiH : (∀ {x y} → x ≤ y → F y ≤ F x) → Hom S WQ WQ
    antiH aF = record { map = record { to = F ; cong = cF } ; map-random = λ {γ} m → Meas-anti aF {γ ⟨$⟩_} m }
