{-# OPTIONS --safe --without-K #-}

-- Auxiliary tests and lemmas for downward monotone convergence (`Continuous/Fatou`, plan 03).
--   * `imp-borel`: for Borel U and V, the set `U → V` is Borel (excluded middle);
--   * `Meas-monus2`: x ∸ t is threshold-measurable for measurable x and t, when every t r is rationally bounded
--     (`Monus.monus` unfolds to q < 0 or a countable quantification over the rationals);
--   * `monusH f g`: the test x ↦ f x ∸ g x on any X, for g pointwise bounded;
--   * `addX`, `∫ᴹ-addX`: the pointwise sum of tests on any X, and additivity of `∫ᴹ` (`J-add`).
module QBS.Continuous.FatouAux where

open import Level using (lift)
open import Function.Base using (case_of_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_<_) renaming (_+_ to _+q_)
open import QBS.Analysis.RationalLemmas using (ℚᵘ; 0ℚᵘ)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.LowerReals using (Cut; module Cut)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Borel.Core using (Borel; Pred; _≐_; compl; resp; union₂; inter₂)
open import QBS.Borel.Source using (R₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Monus using (module Monus)
open Cut using (mem)

module FatouAux (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-add; J-cong)
  open OmegaSemiring A using (_≈_; _+_; +-cong; distribˡ; refl; trans)
  open Meas (lemOf lem₁) using (Meas; Meas-⊕; ex-enum; all-enum)
  open LevelSets (lemOf lem₁) using (borel-prop)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ψ; mψ; module C)
  open C.Pre using (m)
  open Monus lem₁ using (monus; monus-cong; BndQ)
  open QBS
  open Hom

  imp-borel : ∀ {U V : Pred} → Borel U → Borel V → Borel (λ c → U c → V c)
  imp-borel {U} {V} bu bv = resp e (union₂ (compl bu) bv)
    where
      e : (λ c → (U c → ⊥) ⊎ V c) ≐ (λ c → U c → V c)
      e c = (λ { (inj₁ nu) u → ⊥-elim (nu u) ; (inj₂ v) _ → v })
          , (λ f → case lemOf lem₁ (U c) of λ { (inj₁ u) → inj₂ (f u) ; (inj₂ nu) → inj₁ nu })

  Meas-monus2 : ∀ (x t : R₁ → Cut) → Meas x → Meas t → (∀ r → BndQ (t r)) → Meas (λ r → monus (x r) (t r))
  Meas-monus2 x t mx mt bd q = resp e (union₂ (borel-prop (q < 0ℚᵘ)) (ex-enum P bP))
    where
      P : ℚᵘ → Pred
      P q′ c = (q < q′) × (∀ s → mem (t (lift c)) s → mem (x (lift c)) (q′ +q s))
      bP : ∀ q′ → Borel (P q′)
      bP q′ = inter₂ (borel-prop (q < q′)) (all-enum (λ s c → mem (t (lift c)) s → mem (x (lift c)) (q′ +q s))
                (λ s → imp-borel (mt s) (mx (q′ +q s))))
      e : _ ≐ _
      e c = (λ { (inj₁ l) → inj₁ l ; (inj₂ w) → inj₂ (bd (lift c) , w) })
          , (λ { (inj₁ l) → inj₁ l ; (inj₂ (_ , w)) → inj₂ w })

  -- the test x ↦ f x ∸ g x, for g pointwise bounded
  monusH : ∀ {X : QBS S} (f g : Hom S X WQ) → (∀ x → BndQ (map g ⟨$⟩ x)) → Hom S X WQ
  monusH f g bd = record
    { map = record { to = λ x → monus (map f ⟨$⟩ x) (map g ⟨$⟩ x)
                   ; cong = λ e → monus-cong (Func.cong (map f) e) (Func.cong (map g) e) }
    ; map-random = λ {γ} mγ → Meas-monus2 (λ r → map f ⟨$⟩ (γ ⟨$⟩ r)) (λ r → map g ⟨$⟩ (γ ⟨$⟩ r))
        (map-random f {γ} mγ) (map-random g {γ} mγ) (λ r → bd (γ ⟨$⟩ r)) }

  -- the pointwise sum of tests, and additivity of the integral
  addX : ∀ {X : QBS S} → Hom S X WQ → Hom S X WQ → Hom S X WQ
  addX f g = record
    { map = record { to = λ x → (map f ⟨$⟩ x) + (map g ⟨$⟩ x)
                   ; cong = λ e → +-cong (Func.cong (map f) e) (Func.cong (map g) e) }
    ; map-random = λ {γ} mγ → Meas-⊕ {λ r → map f ⟨$⟩ (γ ⟨$⟩ r)} {λ r → map g ⟨$⟩ (γ ⟨$⟩ r)}
        (map-random f {γ} mγ) (map-random g {γ} mγ) }

  ∫ᴹ-addX : ∀ {X : QBS S} (p : C.Pre (XW X)) (f g : Hom S X WQ) → ∫ᴹ {X} p (addX f g) ≈ ∫ᴹ {X} p f + ∫ᴹ {X} p g
  ∫ᴹ-addX {X} p f g = trans (J-cong (m p) {ψ {X} p (addX f g)} {λ r → ψ {X} p f r + ψ {X} p g r}
    (mψ {X} p (addX f g)) (Meas-⊕ {ψ {X} p f} {ψ {X} p g} (mψ {X} p f) (mψ {X} p g))
    (λ r → distribˡ _ _ _)) (J-add (m p) {ψ {X} p f} {ψ {X} p g} (mψ {X} p f) (mψ {X} p g))
