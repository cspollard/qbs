{-# OPTIONS --safe --without-K #-}

-- The integral of signed functions against a measure, with values in the signed ring of `Analysis/Signed`.
--
-- A signed integrable function `f` is a pair `(f⁺, f⁻)` of threshold-measurable `[0,∞]`-valued functions with
-- integrals bounded by naturals, standing for `f⁺ − f⁻`; `E f = J f⁺ − J f⁻` (a signed value).  Two such pairs are
-- equal when `f⁺ + g⁻ = g⁺ + f⁻` pointwise, and `E` respects this.  Linearity: `E (f + g) = E f + E g`,
-- `E (c · f) = c · E f` for a signed constant `c`, `E (−f) = −E f`, and (against a probability measure)
-- `E` of a constant is that constant.
module QBS.Analysis.SignedIntegral where

open import Level using (suc; zero)
open import Data.Product.Base using (Σ; _,_)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)
open import Function.Base using (_$_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Signed
open import QBS.Analysis.SignedOmega using (module Bounded)

module SignedIntegral (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open Lebesgue lem
  open Meas lem
  open Integration A using (Measure; IsProb; I)
  open Measurable A using (Fun-const)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; *-identityʳ; ≤-refl)
  open Bounded A
  open Sg
  open LevelSets lem using (LS)

  ----------------------------------------------------------------------------
  -- signed integrable functions

  record SF (m : Measure) : Set₁ where
    field
      f⁺ f⁻ : R₁ → Cut
      f⁺-meas : Meas f⁺
      f⁻-meas : Meas f⁻
      f⁺-int : Bnd (J m f⁺ f⁺-meas)
      f⁻-int : Bnd (J m f⁻ f⁻-meas)
  open SF

  -- the signed integral
  E : ∀ {m} → SF m → Sg
  E {m} f = J m (f⁺ f) (f⁺-meas f) − J m (f⁻ f) (f⁻-meas f) [ f⁺-int f , f⁻-int f ]

  -- equality of signed functions: f⁺ + g⁻ = g⁺ + f⁻ pointwise
  _≈SF_ : ∀ {m} → SF m → SF m → Set₁
  f ≈SF g = ∀ x → f⁺ f x + f⁻ g x ≈ f⁺ g x + f⁻ f x

  -- the integral of the cross sums
  cross : ∀ {m} (f g : SF m) → f ≈SF g → J m (f⁺ f) (f⁺-meas f) + J m (f⁻ g) (f⁻-meas g) ≈ J m (f⁺ g) (f⁺-meas g) + J
      m (f⁻ f) (f⁻-meas f)
  cross {m} f g e = begin
    J m (f⁺ f) (f⁺-meas f) + J m (f⁻ g) (f⁻-meas g)                      ≈⟨ sym (J-add m (f⁺-meas f) (f⁻-meas g)) ⟩
    J m (λ x → f⁺ f x + f⁻ g x) (Meas-⊕ {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g))
      ≈⟨ J-cong m (Meas-⊕ {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g)) (Meas-⊕ {f⁺ g} {f⁻ f} (f⁺-meas g) (f⁻-meas f)) e ⟩
    J m (λ x → f⁺ g x + f⁻ f x) (Meas-⊕ {f⁺ g} {f⁻ f} (f⁺-meas g) (f⁻-meas f))
      ≈⟨ J-add m (f⁺-meas g) (f⁻-meas f) ⟩
    J m (f⁺ g) (f⁺-meas g) + J m (f⁻ f) (f⁻-meas f) ∎
    where open SetoidReasoning (OmegaSemiring.setoid A)

  E-cong : ∀ {m} {f g : SF m} → f ≈SF g → E f ≃ E g
  E-cong {m} {f} {g} e = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-0 (J m (f⁺ f) (f⁺-meas f) + J m (f⁻ g) (f⁻-meas g)) (J m (f⁺ g) (f⁺-meas g) + J m (f⁻ f) (f⁻-meas f)) (cross f g e))
    where
      +-0 : ∀ a b → a ≈ b → a + 0# ≈ b + 0#
      +-0 a b h = +-cong {a} {b} {0#} {0#} h refl

  ----------------------------------------------------------------------------
  -- linearity

  private
    bnd-resp : ∀ {a b} → a ≈ b → Bnd a → Bnd b
    bnd-resp = SubSemiring.Is-resp finite
    bnd-+ : ∀ {a b} → Bnd a → Bnd b → Bnd (a + b)
    bnd-+ = SubSemiring.Is-+ finite
    bnd-* : ∀ {a b} → Bnd a → Bnd b → Bnd (a * b)
    bnd-* = SubSemiring.Is-* finite

    -- both sides of `a + b + 0`
    +-+0 : ∀ a a′ b b′ → a ≈ a′ → b ≈ b′ → a + b + 0# ≈ a′ + b′ + 0#
    +-+0 a a′ b b′ ea eb = +-cong {a + b} {a′ + b′} {0#} {0#} (+-cong {a} {a′} {b} {b′} ea eb) refl

    -- J of a signed combination `a·φ + b·ψ`
    J-lin : ∀ m (a b : Cut) {φ ψ} (p : Meas φ) (q : Meas ψ) →
      J m (λ x → a * φ x + b * ψ x)
          (Meas-⊕ {λ x → a * φ x} {λ x → b * ψ x} (Meas-⊗ {λ _ → a} {φ} (Meas-const a) p) (Meas-⊗ {λ _ → b} {ψ} (Meas-const b) q))
        ≈ a * J m φ p + b * J m ψ q
    J-lin m a b {φ} {ψ} p q =
      OmegaSemiring.trans A
        (J-add m {λ x → a * φ x} {λ x → b * ψ x} (Meas-⊗ {λ _ → a} {φ} (Meas-const a) p) (Meas-⊗ {λ _ → b} {ψ} (Meas-const b) q))
        (+-cong {J m (λ x → a * φ x) (Meas-⊗ {λ _ → a} {φ} (Meas-const a) p)} {a * J m φ p}
                {J m (λ x → b * ψ x) (Meas-⊗ {λ _ → b} {ψ} (Meas-const b) q)} {b * J m ψ q}
                (J-scale m a {φ} p) (J-scale m b {ψ} q))

  -- sum
  _+SF_ : ∀ {m} → SF m → SF m → SF m
  _+SF_ {m} f g = record
    { f⁺ = λ x → f⁺ f x + f⁺ g x
    ; f⁻ = λ x → f⁻ f x + f⁻ g x
    ; f⁺-meas = Meas-⊕ {f⁺ f} {f⁺ g} (f⁺-meas f) (f⁺-meas g)
    ; f⁻-meas = Meas-⊕ {f⁻ f} {f⁻ g} (f⁻-meas f) (f⁻-meas g)
    ; f⁺-int = bnd-resp (OmegaSemiring.sym A (J-add m (f⁺-meas f) (f⁺-meas g))) (bnd-+ (f⁺-int f) (f⁺-int g))
    ; f⁻-int = bnd-resp (OmegaSemiring.sym A (J-add m (f⁻-meas f) (f⁻-meas g))) (bnd-+ (f⁻-int f) (f⁻-int g))
    }

  E-+ : ∀ {m} (f g : SF m) → E (f +SF g) ≃ E f +S E g
  E-+ {m} f g = mk≃ 0# (SubSemiring.Is-0 finite) (OmegaSemiring.trans A
    (+-+0 (J m _ (f⁺-meas (f +SF g))) (J m (f⁺ f) (f⁺-meas f) + J m (f⁺ g) (f⁺-meas g))
          (J m (f⁻ f) (f⁻-meas f) + J m (f⁻ g) (f⁻-meas g)) (J m (f⁻ f) (f⁻-meas f) + J m (f⁻ g) (f⁻-meas g))
          (J-add m (f⁺-meas f) (f⁺-meas g)) (OmegaSemiring.refl A))
    (+-+0 (J m (f⁺ f) (f⁺-meas f) + J m (f⁺ g) (f⁺-meas g)) (J m (f⁺ f) (f⁺-meas f) + J m (f⁺ g) (f⁺-meas g))
          (J m (f⁻ f) (f⁻-meas f) + J m (f⁻ g) (f⁻-meas g)) (J m _ (f⁻-meas (f +SF g)))
          (OmegaSemiring.refl A) (OmegaSemiring.sym A (J-add m (f⁻-meas f) (f⁻-meas g)))))

  -- negation swaps the parts
  -SF_ : ∀ {m} → SF m → SF m
  -SF f = record { f⁺ = f⁻ f ; f⁻ = f⁺ f ; f⁺-meas = f⁻-meas f ; f⁻-meas = f⁺-meas f ; f⁺-int = f⁻-int f ; f⁻-int = f⁺-int f }

  E-neg : ∀ {m} (f : SF m) → E (-SF f) ≃ -S (E f)
  E-neg f = ≃-refl

  -- scaling by a signed constant
  scaleSF : ∀ {m} → Sg → SF m → SF m
  scaleSF {m} c f = record
    { f⁺ = λ x → pos c * f⁺ f x + neg c * f⁻ f x
    ; f⁻ = λ x → pos c * f⁻ f x + neg c * f⁺ f x
    ; f⁺-meas = Meas-⊕ {λ x → pos c * f⁺ f x} {λ x → neg c * f⁻ f x}
        (Meas-⊗ {λ _ → pos c} {f⁺ f} (Meas-const (pos c)) (f⁺-meas f))
            (Meas-⊗ {λ _ → neg c} {f⁻ f} (Meas-const (neg c)) (f⁻-meas f))
    ; f⁻-meas = Meas-⊕ {λ x → pos c * f⁻ f x} {λ x → neg c * f⁺ f x}
        (Meas-⊗ {λ _ → pos c} {f⁻ f} (Meas-const (pos c)) (f⁻-meas f))
            (Meas-⊗ {λ _ → neg c} {f⁺ f} (Meas-const (neg c)) (f⁺-meas f))
    ; f⁺-int = bnd-resp (OmegaSemiring.sym A (J-lin m (pos c) (neg c) (f⁺-meas f) (f⁻-meas f)))
        (bnd-+ (bnd-* (pos-fin c) (f⁺-int f)) (bnd-* (neg-fin c) (f⁻-int f)))
    ; f⁻-int = bnd-resp (OmegaSemiring.sym A (J-lin m (pos c) (neg c) (f⁻-meas f) (f⁺-meas f)))
        (bnd-+ (bnd-* (pos-fin c) (f⁻-int f)) (bnd-* (neg-fin c) (f⁺-int f)))
    }

  E-scale : ∀ {m} (c : Sg) (f : SF m) → E (scaleSF c f) ≃ c *S E f
  E-scale {m} c f = mk≃ 0# (SubSemiring.Is-0 finite) (OmegaSemiring.trans A
    (+-+0 (J m _ (f⁺-meas (scaleSF c f))) (pos c * J m (f⁺ f) (f⁺-meas f) + neg c * J m (f⁻ f) (f⁻-meas f))
          (pos c * J m (f⁻ f) (f⁻-meas f) + neg c * J m (f⁺ f) (f⁺-meas f))
              (pos c * J m (f⁻ f) (f⁻-meas f) + neg c * J m (f⁺ f) (f⁺-meas f))
          (J-lin m (pos c) (neg c) (f⁺-meas f) (f⁻-meas f)) (OmegaSemiring.refl A))
    (+-+0 (pos c * J m (f⁺ f) (f⁺-meas f) + neg c * J m (f⁻ f) (f⁻-meas f))
        (pos c * J m (f⁺ f) (f⁺-meas f) + neg c * J m (f⁻ f) (f⁻-meas f))
          (pos c * J m (f⁻ f) (f⁻-meas f) + neg c * J m (f⁺ f) (f⁺-meas f)) (J m _ (f⁻-meas (scaleSF c f)))
          (OmegaSemiring.refl A) (OmegaSemiring.sym A (J-lin m (pos c) (neg c) (f⁻-meas f) (f⁺-meas f)))))

  ----------------------------------------------------------------------------
  -- constants (against a probability measure)

  J-const : ∀ {m} → IsProb m → ∀ a → J m (λ _ → a) (Meas-const a) ≈ a
  J-const {m} pm a = OmegaSemiring.trans A
    (J-cong m (Meas-const a) (Meas-⊗ {λ _ → a} {λ _ → 1#} (Meas-const a) (Meas-const 1#))
        (λ x → OmegaSemiring.sym A (*-identityʳ a)))
    (OmegaSemiring.trans A (J-scale m a {λ _ → 1#} (Meas-const 1#))
      (OmegaSemiring.trans A (*-cong {a} {a} {J m (λ _ → 1#) (Meas-const 1#)} {1#} (OmegaSemiring.refl A)
         (OmegaSemiring.trans A (J-irrel m (Meas-const 1#) (LS (Fun-const 1# ≤-refl)))
           (OmegaSemiring.trans A (J-fun m (Fun-const 1# ≤-refl)) pm))) (*-identityʳ a)))

  constSF : ∀ {m} → IsProb m → Sg → SF m
  constSF {m} pm a = record
    { f⁺ = λ _ → pos a ; f⁻ = λ _ → neg a
    ; f⁺-meas = Meas-const (pos a) ; f⁻-meas = Meas-const (neg a)
    ; f⁺-int = bnd-resp (OmegaSemiring.sym A (J-const pm (pos a))) (pos-fin a)
    ; f⁻-int = bnd-resp (OmegaSemiring.sym A (J-const pm (neg a))) (neg-fin a)
    }

  E-const : ∀ {m} (pm : IsProb m) (a : Sg) → E (constSF pm a) ≃ a
  E-const {m} pm a = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-+0 (J m (λ _ → pos a) (Meas-const (pos a))) (pos a) (neg a) (J m (λ _ → neg a) (Meas-const (neg a)))
          (J-const pm (pos a)) (OmegaSemiring.sym A (J-const pm (neg a))))
