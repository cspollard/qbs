{-# OPTIONS --safe --without-K #-}

-- Hard rejection in the continuous model: restricting a measure to a Borel set U,
-- `I (restrictM U m) h f = I m (χ U · h)`.  This is the measure behind conditioning on an event;
-- its mass is the measure of the event, and restricting to U and to its complement splits any
-- measure (total expectation).
module QBS.Analysis.Restrict where

open import Level using (zero; suc; lower)
open import Function.Base using (const)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Measure

module Restrict (A : OmegaSemiring (suc zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Indicators A lem using (case; χ; χ-in; χ-out; χ-≤1; χ-compl; Fun-χ)
  private R = R₁

  -- χ U x is 1 inside U and 0 outside
  dichotomy : ∀ U (x : R) → (U (lower x) × χ U x ≈ 1#) ⊎ ((U (lower x) → ⊥) × χ U x ≈ 0#)
  dichotomy U x = case (λ u → inj₁ (u , χ-in U x u)) (λ n → inj₂ (n , χ-out U x n))

  private
    χ*≤1 : ∀ U {h : R → ∣A∣} → (∀ x → h x ≤ 1#) → ∀ x → χ U x * h x ≤ 1#
    χ*≤1 U b x = ≤-trans (*-mono (χ U x) (b x)) (≤-trans (≤-reflexive (*-identityʳ _)) (χ-≤1 U x))

  private
    -- the pieces of `Fun-χ·`, one per way of building a function
    χ·-out : ∀ {U V : Cantor → Set} {h : R → ∣A∣} → (∀ x → (V (lower x) → ⊥) → h x ≈ 0#) →
      ∀ x → (U (lower x) × V (lower x) → ⊥) → χ U x * h x ≈ 0#
    χ·-out {U} {V} {h} e₁ x n with dichotomy U x
    ... | inj₂ (nu , z) = trans (*-cong z refl) (zeroˡ _)
    ... | inj₁ (u , o) = trans (*-cong o refl) (trans (*-identityˡ _) (e₁ x (λ v → n (u , v))))

    χ·-compl-bnd : ∀ {U} {h′ : R → ∣A∣} → (∀ x → h′ x ≤ 1#) → ∀ x → χ (λ y → U y → ⊥) x + χ U x * h′ x ≤ 1#
    χ·-compl-bnd {U} b x with dichotomy U x
    ... | inj₁ (u , o) = ≤-resp (sym eq) refl (b x)
      where eq = trans (+-cong (χ-out (λ y → U y → ⊥) x (λ nu → nu u)) (*-cong o refl))
                       (trans (+-cong refl (*-identityˡ _)) (+-identityˡ _))
    ... | inj₂ (n , z) = ≤-reflexive
      (trans (+-cong (χ-in (λ y → U y → ⊥) x n) (*-cong z refl))
             (trans (+-cong refl (zeroˡ _)) (+-identityʳ 1#)))

    χ·-compl-pw : ∀ {U} {h h′ : R → ∣A∣} → (∀ x → h x + h′ x ≈ 1#) →
      ∀ x → χ U x * h x + (χ (λ y → U y → ⊥) x + χ U x * h′ x) ≈ 1#
    χ·-compl-pw {U} q x with dichotomy U x
    ... | inj₁ (u , o) =
      trans (+-cong (*-cong o refl) (+-cong (χ-out (λ y → U y → ⊥) x (λ nu → nu u)) (*-cong o refl)))
        (trans (+-cong (*-identityˡ _) (trans (+-identityˡ _) (*-identityˡ _))) (q x))
    ... | inj₂ (n , z) =
      trans (+-cong (*-cong z refl) (+-cong (χ-in (λ y → U y → ⊥) x n) (*-cong z refl)))
        (trans (+-cong (zeroˡ _) (+-cong refl (zeroˡ _))) (trans (+-identityˡ _) (+-identityʳ 1#)))

  -- measurable functions are closed under multiplication by an indicator
  Fun-χ· : ∀ {U h} → Borel U → Fun h → Fun (λ x → χ U x * h x)
  Fun-χ· {U} bU (ind {V} {h} c c≤1 bV e₀ e₁ b) =
    ind c c≤1 (inter₂ bU bV)
      (λ x (u , v) → trans (*-cong (χ-in U x u) (e₀ x v)) (*-identityˡ c))
      (χ·-out {U} {V} {h} e₁)
      (χ*≤1 U b)
  Fun-χ· {U} bU (sumF {h} {h₁} {h₂} f₁ f₂ q b) =
    sumF (Fun-χ· bU f₁) (Fun-χ· bU f₂) (λ x → trans (*-cong refl (q x)) (distribˡ _ _ _)) (χ*≤1 U b)
  Fun-χ· {U} bU (supF {h} hs fs inc q) =
    supF (λ n x → χ U x * hs n x) (λ n → Fun-χ· bU (fs n)) (λ x n → *-mono (χ U x) (inc x n))
      (λ x → trans (*-cong refl (q x)) (*-⨆ (χ U x) _ (inc x) (λ n → *-mono (χ U x) (inc x n))))
  Fun-χ· {U} bU (complF {h} {h′} f q) =
    complF {h′ = λ x → χ (λ y → U y → ⊥) x + χ U x * h′ x}
      (sumF (Fun-χ (compl bU)) (Fun-χ· bU f) (λ x → refl) (χ·-compl-bnd {U} (Fun-≤1 f)))
      (χ·-compl-pw {U} {h} {h′} q)

  private
    χ-mono : ∀ U {h h′ : R → ∣A∣} → (∀ x → h x ≤ h′ x) → ∀ x → χ U x * h x ≤ χ U x * h′ x
    χ-mono U le x = *-mono (χ U x) (le x)

  restrictM : ∀ {U} → Borel U → Measure → Measure
  restrictM {U} bU m = record
    { I = λ h f → I m (λ x → χ U x * h x) (Fun-χ· bU f)
    ; I-mono = λ f f′ le → I-mono m (Fun-χ· bU f) (Fun-χ· bU f′) (χ-mono U le)
    ; I-add = λ f f₁ f₂ e → I-add m (Fun-χ· bU f) (Fun-χ· bU f₁) (Fun-χ· bU f₂)
        (λ x → trans (*-cong refl (e x)) (distribˡ _ _ _))
    ; I-scale = λ c f f′ e → I-scale m c (Fun-χ· bU f) (Fun-χ· bU f′)
        (λ x → trans (*-cong refl (e x))
                 (trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _))))
    ; I-sup = λ hs fs inc f e → I-sup m (λ n x → χ U x * hs n x) (λ n → Fun-χ· bU (fs n))
        (λ x n → *-mono (χ U x) (inc x n)) (Fun-χ· bU f)
        (λ x → trans (*-cong refl (e x)) (*-⨆ (χ U x) _ (inc x) (λ n → *-mono (χ U x) (inc x n))))
    ; I-sub = λ f → ≤-trans (I-mono m (Fun-χ· bU f) (Fun-const 1# ≤-refl)
          (λ x → ≤-trans (≤-reflexive (*-identityʳ _)) (χ-≤1 U x)))
        (I-sub m (Fun-const 1# ≤-refl))
    }

  -- the mass of the restriction is the measure of the set
  mass-restrict : ∀ {U} (bU : Borel U) (m : Measure) →
    mass (restrictM bU m) ≈ I m (χ U) (Fun-χ bU)
  mass-restrict {U} bU m = I-cong m (λ x → *-identityʳ _) (Fun-χ· bU (Fun-const 1# ≤-refl)) (Fun-χ bU)

  -- total expectation: restricting to U and to its complement splits a measure
  restrict-split : ∀ {U} (bU : Borel U) (m : Measure) h (f : Fun h) →
    I m h f ≈ I (restrictM bU m) h f + I (restrictM (compl bU) m) h f
  restrict-split {U} bU m h f = I-add m f (Fun-χ· bU f) (Fun-χ· (compl bU) f)
    (λ x → trans (sym (*-identityˡ (h x)))
             (trans (*-cong (sym (χ-compl U x)) refl)
                    (trans (distribʳ _ _ _) (+-comm _ _))))
