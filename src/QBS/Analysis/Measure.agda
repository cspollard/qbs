{-# OPTIONS --safe --without-K #-}

-- Sub-probability measures on Cantor space as Daniell-style integration functionals on the
-- measurable functions: monotone, additive, homogeneous, continuous along increasing sequences,
-- of total mass at most 1 (`IsProb`: exactly 1).  (By the Riesz–Daniell correspondence these are exactly the Borel probability
-- measures; we use the functional form because the Giry-monad operations are then plain
-- composition: no extension theorem is needed to build Dirac, push-forward or bind.)
module QBS.Analysis.Measure where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
import Level
open import Data.Unit.Polymorphic.Base using (tt) renaming (⊤ to ⊤ᵖ)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun

module Integration (A : OmegaSemiring (suc zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  private R = R₁

  record Measure : Set₁ where
    field
      I : ∀ h → Fun h → ∣A∣
      I-cong : ∀ {h h′} (e : ∀ x → h x ≈ h′ x) (f : Fun h) (f′ : Fun h′) → I h f ≈ I h′ f′
      I-mono : ∀ {h h′} (f : Fun h) (f′ : Fun h′) → (∀ x → h x ≤ h′ x) → I h f ≤ I h′ f′
      I-add : ∀ {h h₁ h₂} (f : Fun h) (f₁ : Fun h₁) (f₂ : Fun h₂) →
        (∀ x → h x ≈ h₁ x + h₂ x) → I h f ≈ I h₁ f₁ + I h₂ f₂
      I-scale : ∀ {h h′} c (f : Fun h) (f′ : Fun h′) → (∀ x → h′ x ≈ c * h x) →
        I h′ f′ ≈ c * I h f
      I-sup : ∀ {h} (hs : ℕ → R → ∣A∣) (fs : ∀ n → Fun (hs n))
        (inc : ∀ x → Increasing (λ n → hs n x)) (f : Fun h) →
        (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
        I h f ≈ ⨆ (λ n → I (hs n) (fs n)) (λ n → I-mono (fs n) (fs (ℕ.suc n)) (λ x → inc x n))
      I-sub : ∀ (f : Fun (const 1#)) → I (const 1#) f ≤ 1#

  open Measure public

  -- total mass
  mass : Measure → ∣A∣
  mass m = I m (const 1#) (Fun-const 1# ≤-refl)

  -- probability measures: total mass exactly 1
  IsProb : Measure → Set₁
  IsProb m = I m (const 1#) (Fun-const 1# ≤-refl) ≈ 1#

  ----------------------------------------------------------------------------
  -- Dirac measures, push-forward and bind are plain composition of functionals

  dirac : R → Measure
  dirac r₀ = record
    { I = λ h _ → h r₀
    ; I-cong = λ e _ _ → e r₀
    ; I-mono = λ _ _ le → le r₀
    ; I-add = λ _ _ _ e → e r₀
    ; I-scale = λ c _ _ e → e r₀
    ; I-sup = λ hs fs inc f e → trans (e r₀) (⨆-cong (inc r₀) (λ n → inc r₀ n) (λ n → refl))
    ; I-sub = λ _ → ≤-refl
    }

  IsProb-dirac : ∀ r₀ → IsProb (dirac r₀)
  IsProb-dirac r₀ = refl

  push : ∀ {f} → Measurable (down f) → Measure → Measure
  push {f} mf m = record
    { I = λ h fh → I m (h ∘ f) (Fun-pre fh mf)
    ; I-cong = λ e fh fh′ → I-cong m (λ x → e (f x)) _ _
    ; I-mono = λ fh fh′ le → I-mono m _ _ (λ x → le (f x))
    ; I-add = λ fh f₁ f₂ e → I-add m _ _ _ (λ x → e (f x))
    ; I-scale = λ c fh fh′ e → I-scale m c _ _ (λ x → e (f x))
    ; I-sup = λ hs fs inc fh e →
        I-sup m (λ n → hs n ∘ f) (λ n → Fun-pre (fs n) mf) (λ x → inc (f x)) _ (λ x → e (f x))
    ; I-sub = λ fh → I-sub m _
    }

  IsProb-push : ∀ {f} (mf : Measurable (down f)) {m} → IsProb m → IsProb (push {f} mf m)
  IsProb-push {f} mf {m} pm = trans (I-cong m (λ x → refl) _ (Fun-const 1# ≤-refl)) pm

  -- a kernel is a family of measures whose integrals are measurable in the parameter
  KernelOk : (R → Measure) → Set₁
  KernelOk g = ∀ {h} (fh : Fun h) → Fun (λ r → I (g r) h fh)

  bind : (m : Measure) (g : R → Measure) → KernelOk g → Measure
  bind m g kg = record
    { I = λ h fh → I m (λ r → I (g r) h fh) (kg fh)
    ; I-cong = λ e fh fh′ → I-cong m (λ r → I-cong (g r) e fh fh′) _ _
    ; I-mono = λ fh fh′ le → I-mono m _ _ (λ r → I-mono (g r) fh fh′ le)
    ; I-add = λ fh f₁ f₂ e → I-add m _ _ _ (λ r → I-add (g r) fh f₁ f₂ e)
    ; I-scale = λ c fh fh′ e → I-scale m c _ _ (λ r → I-scale (g r) c fh fh′ e)
    ; I-sup = λ {h} hs fs inc fh e →
        let incH : ∀ r → Increasing (λ n → I (g r) (hs n) (fs n))
            incH r n = I-mono (g r) (fs n) (fs (ℕ.suc n)) (λ x → inc x n)
            supFun : Fun (λ r → ⨆ (λ n → I (g r) (hs n) (fs n)) (incH r))
            supFun = supF (λ n r → I (g r) (hs n) (fs n)) (λ n → kg (fs n)) incH (λ r → refl)
        in trans (I-cong m (λ r → I-sup (g r) hs fs inc fh e) (kg fh) supFun)
                 (I-sup m (λ n r → I (g r) (hs n) (fs n)) (λ n → kg (fs n)) incH supFun (λ r → refl))
    ; I-sub = λ fh → ≤-trans (I-mono m (kg fh) (Fun-const 1# ≤-refl) (λ r → I-sub (g r) fh)) (I-sub m (Fun-const 1# ≤-refl))
    }

  IsProb-bind : ∀ {m g} {kg : KernelOk g} → IsProb m → (∀ r → IsProb (g r)) → IsProb (bind m g kg)
  IsProb-bind {m} {g} {kg} pm pg =
    trans (I-cong m (λ r → pg r) (kg (Fun-const 1# ≤-refl)) (Fun-const 1# ≤-refl)) pm

  ----------------------------------------------------------------------------
  -- classes of admissible measures (probability, or sub-probability), closed under the operations

  record MeasureClass : Set₂ where
    field
      Ok : Measure → Set₁
      ok-dirac : ∀ r₀ → Ok (dirac r₀)
      ok-push : ∀ {f} (mf : Measurable (down f)) {m} → Ok m → Ok (push {f} mf m)
      ok-bind : ∀ {m g} {kg : KernelOk g} → Ok m → (∀ r → Ok (g r)) → Ok (bind m g kg)

  probClass : MeasureClass
  probClass = record
    { Ok = IsProb ; ok-dirac = IsProb-dirac ; ok-push = λ {f} mf {m} pm → IsProb-push {f} mf {m} pm ; ok-bind = λ {m} {g} {kg} pm pg → IsProb-bind {m} {g} {kg} pm pg }

  -- every measure is a sub-probability measure
  subClass : MeasureClass
  subClass = record
    { Ok = λ _ → ⊤ᵖ {Level.suc Level.zero} ; ok-dirac = λ _ → tt ; ok-push = λ _ _ → tt ; ok-bind = λ _ _ → tt }
