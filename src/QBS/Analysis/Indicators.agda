{-# OPTIONS --safe --without-K #-}

-- Indicator functions of Borel sets (classically decided), and the measure of a disjoint union
-- as the supremum of the partial sums.
module QBS.Analysis.Indicators where

open import Level using (zero; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
import Data.Sum.Base
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁; down; downℕ)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Series using (module Series)
open import QBS.Classical using (LEM₀)

module Indicators (A : OmegaSemiring (suc zero)) (lem : LEM₀) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Measurable A
  open Integration A
  open Series A using (psum; psum-inc)
  open SetoidReasoning setoid
  private R = R₁

  -- case analysis on membership without abstracting over the goal
  case : ∀ {P : Set} {Q : Set₁} → (P → Q) → ((P → ⊥) → Q) → Q
  case {P} k₁ k₂ = Data.Sum.Base.[ k₁ , k₂ ]′ (lem P)

  χ : Pred → R → ∣A∣
  χ V x with lem (V (lower x))
  ... | inj₁ _ = 1#
  ... | inj₂ _ = 0#

  χ-in : ∀ V x → V (lower x) → χ V x ≈ 1#
  χ-in V x v with lem (V (lower x))
  ... | inj₁ _ = refl
  ... | inj₂ nv = ⊥-elim (nv v)

  χ-out : ∀ V x → (V (lower x) → ⊥) → χ V x ≈ 0#
  χ-out V x nv with lem (V (lower x))
  ... | inj₁ v = ⊥-elim (nv v)
  ... | inj₂ _ = refl

  χ-≤1 : ∀ V x → χ V x ≤ 1#
  χ-≤1 V x with lem (V (lower x))
  ... | inj₁ _ = ≤-refl
  ... | inj₂ _ = 0-least

  Fun-χ : ∀ {V} → Borel V → Fun (χ V)
  Fun-χ bV = ind 1# ≤-refl bV (χ-in _) (χ-out _) (χ-≤1 _)

  -- χ respects equivalence of sets
  χ-cong : ∀ {V W} → V ≐ W → ∀ x → χ V x ≈ χ W x
  χ-cong {V} {W} e x with lem (V (lower x))
  ... | inj₁ v = sym (χ-in W x (proj₁ (e (lower x)) v))
  ... | inj₂ nv = sym (χ-out W x (λ w → nv (proj₂ (e (lower x)) w)))

  χ-⊥ : ∀ x → χ (λ _ → ⊥) x ≈ 0#
  χ-⊥ x = χ-out (λ _ → ⊥) x (λ b → b)

  χ-⊤ : ∀ x → χ (λ _ → ⊤) x ≈ 1#
  χ-⊤ x = χ-in (λ _ → ⊤) x tt

  -- χ of the complement
  χ-compl : ∀ V x → χ (λ y → V y → ⊥) x + χ V x ≈ 1#
  χ-compl V x with lem (V (lower x))
  ... | inj₁ v = trans (+-cong (χ-out (λ y → V y → ⊥) x (λ nv → nv v)) refl) (+-identityˡ 1#)
  ... | inj₂ nv = trans (+-cong (χ-in (λ y → V y → ⊥) x nv) refl) (+-identityʳ 1#)

  ----------------------------------------------------------------------------
  -- integrals of constants and indicators

  I-≤1 : ∀ (m : Measure) {h} (f : Fun h) → I m h f ≤ 1#
  I-≤1 m {h} f = ≤-trans (I-mono m f (Fun-const 1# ≤-refl) (Fun-≤1 f)) (I-sub m (Fun-const 1# ≤-refl))

  -- a constant integrates to the constant times the mass
  I-const-mass : ∀ (m : Measure) c (c≤1 : c ≤ 1#) → I m (const c) (Fun-const c c≤1) ≈ c * mass m
  I-const-mass m c c≤1 = I-scale m c (Fun-const 1# ≤-refl) (Fun-const c c≤1) (λ x → sym (*-identityʳ c))

  I-const : ∀ (m : Measure) → IsProb m → ∀ c (c≤1 : c ≤ 1#) → I m (const c) (Fun-const c c≤1) ≈ c
  I-const m pm c c≤1 = trans (I-const-mass m c c≤1) (trans (*-cong refl pm) (*-identityʳ c))

  I-χ-compl : ∀ (m : Measure) {W} (bW : Borel W) →
    I m (χ (λ y → W y → ⊥)) (Fun-χ (compl bW)) + I m (χ W) (Fun-χ bW) ≈ mass m
  I-χ-compl m {W} bW = sym (I-add m (Fun-const 1# ≤-refl) (Fun-χ (compl bW)) (Fun-χ bW)
                                    (λ x → sym (χ-compl W x)))

  I-χ-⊥ : ∀ (m : Measure) (b : Borel (λ (_ : Cantor) → ⊥)) → I m (χ (λ _ → ⊥)) (Fun-χ b) ≈ 0#
  I-χ-⊥ m b = trans (I-cong m χ-⊥ (Fun-χ b) (Fun-const 0# 0-least))
                (trans (I-const-mass m 0# 0-least) (zeroˡ (mass m)))

  ----------------------------------------------------------------------------
  -- partial sums

  -- partial sums of indicators of a family of sets
  PS : (ℕ → Pred) → ℕ → R → ∣A∣
  PS V ℕ.zero x = 0#
  PS V (ℕ.suc N) x = PS V N x + χ (V N) x

  PS-null : ∀ V x N → (∀ k → k ℕ.< N → V k (lower x) → ⊥) → PS V N x ≈ 0#
  PS-null V x ℕ.zero h = refl
  PS-null V x (ℕ.suc N) h =
    trans (+-cong (PS-null V x N (λ k k<N → h k (Data.Nat.Properties.<-trans k<N (Data.Nat.Properties.n<1+n N))))
                  (χ-out (V N) x (h N (Data.Nat.Properties.n<1+n N))))
          (+-identityˡ 0#)

  PS-after : ∀ V → Disjoint V → ∀ x n₀ → V n₀ (lower x) → ∀ N → n₀ ℕ.< N → PS V N x ≈ 1#
  PS-after V dj x n₀ v ℕ.zero ()
  PS-after V dj x n₀ v (ℕ.suc N) (ℕ.s≤s n₀≤N) with Data.Nat.Properties.m≤n⇒m<n∨m≡n n₀≤N
  ... | inj₁ n₀<N =
        trans (+-cong (PS-after V dj x n₀ v N n₀<N)
                      (χ-out (V N) x (λ vN → Data.Nat.Properties.<⇒≢ n₀<N (dj (lower x) n₀ N v vN))))
              (+-identityʳ 1#)
  ... | inj₂ ≡.refl =
        trans (+-cong (PS-null V x n₀ (λ k k<n₀ vk → Data.Nat.Properties.<⇒≢ k<n₀ (dj (lower x) k n₀ vk v)))
                      (χ-in (V n₀) x v))
              (+-identityˡ 1#)

  PS-≤1 : ∀ V → Disjoint V → ∀ x N → PS V N x ≤ 1#
  PS-≤1 V dj x ℕ.zero = 0-least
  PS-≤1 V dj x (ℕ.suc N) = case {V N (lower x)}
    (λ v → ≤-resp (sym (trans (+-cong (PS-null V x N (λ k k<N vk → Data.Nat.Properties.<⇒≢ k<N (dj (lower x) k N vk v)))
                                    (χ-in (V N) x v))
                               (+-identityˡ 1#))) refl ≤-refl)
    (λ nv → ≤-resp (sym (trans (+-cong refl (χ-out (V N) x nv)) (+-identityʳ _))) refl (PS-≤1 V dj x N))

  Fun-PS : ∀ {V : ℕ → Pred} → (∀ n → Borel (V n)) → Disjoint V → ∀ N → Fun (PS V N)
  Fun-PS bs dj ℕ.zero = Fun-const 0# 0-least
  Fun-PS {V} bs dj (ℕ.suc N) = sumF (Fun-PS bs dj N) (Fun-χ (bs N)) (λ x → refl) (λ x → PS-≤1 V dj x (ℕ.suc N))

  PS-inc : ∀ V x → Increasing (λ N → PS V N x)
  PS-inc V x N = ≤-+ʳ

  PS-sup : ∀ V → Disjoint V → ∀ x →
    χ (λ y → Σ ℕ (λ n → V n y)) x ≈ ⨆ (λ N → PS V N x) (PS-inc V x)
  PS-sup V dj x = case {Σ ℕ (λ n → V n (lower x))}
    (λ { (n₀ , v) → trans (χ-in _ x (n₀ , v))
           (sym (⨆-const-from (λ N → PS V N x) (PS-inc V x) (ℕ.suc n₀)
                  (λ N h → PS-after V dj x n₀ v N (Data.Nat.Properties.≤′⇒≤ h)))) })
    (λ nu → trans (χ-out _ x nu)
           (sym (⨆-const-from (λ N → PS V N x) (PS-inc V x) 0
                  (λ N _ → PS-null V x N (λ k _ vk → nu (k , vk))))))

  I-PS : ∀ (m : Measure) {V : ℕ → Pred} (bs : ∀ n → Borel (V n)) (dj : Disjoint V) N →
    I m (PS V N) (Fun-PS bs dj N) ≈ psum (λ n → I m (χ (V n)) (Fun-χ (bs n))) N
  I-PS m bs dj ℕ.zero = trans (I-cong m (λ x → refl) (Fun-const 0# 0-least) (Fun-const 0# 0-least))
                          (trans (I-const-mass m 0# 0-least) (zeroˡ (mass m)))
  I-PS m {V} bs dj (ℕ.suc N) =
    trans (I-add m (Fun-PS bs dj (ℕ.suc N)) (Fun-PS bs dj N) (Fun-χ (bs N)) (λ x → refl))
          (+-cong (I-PS m bs dj N) refl)

  -- the measure of a disjoint union is the supremum of the partial sums
  I-⋃ : ∀ (m : Measure) {V : ℕ → Pred} (bs : ∀ n → Borel (V n)) (dj : Disjoint V) →
    I m (χ (λ y → Σ ℕ (λ n → V n y))) (Fun-χ (⋃ bs))
      ≈ ⨆ (λ N → psum (λ n → I m (χ (V n)) (Fun-χ (bs n))) N) (psum-inc _)
  I-⋃ m {V} bs dj = trans
    (I-sup m (PS V) (Fun-PS bs dj) (PS-inc V) (Fun-χ (⋃ bs)) (PS-sup V dj))
    (⨆-cong _ _ (I-PS m bs dj))

  -- finite sums of measurable functions, given a bound
  Fun-psum : ∀ (φ : ℕ → R → ∣A∣) → (∀ n → Fun (φ n)) →
    (∀ N x → psum (λ n → φ n x) N ≤ 1#) → ∀ N → Fun (λ x → psum (λ n → φ n x) N)
  Fun-psum φ fs b ℕ.zero = Fun-const 0# 0-least
  Fun-psum φ fs b (ℕ.suc N) = sumF (Fun-psum φ fs b N) (fs N) (λ x → refl) (λ x → b (ℕ.suc N) x)
