{-# OPTIONS --safe --without-K #-}

-- Setoid-map helpers shared by the core: composition, constants, discrete ℕ and gluing along an index map.
--   * `_∘ₛ_`, `constₛ` (with `constₛ-isConstant`), `⇑` (a function out of a ≡-setoid is a setoid map);
--   * `ℕˢ`, `⇑ℕ`: discrete ℕ at any level, and index functions into it;
--   * `glueₛ j α`, `r ↦ α (j r) r`, with `glueₛ-∘` and `glueₛ-pre`; `_≈ₛ_` is pointwise equality of setoid maps.
-- Route: everything is a one-line record or `Setoid.refl`; the module exists so that `MeasurableMaps`, `Probes` and
-- `RandomSource` can use the helpers without importing `QBS.Core`.
module QBS.SetoidMaps where

open import Level using (_⊔_; Lift; lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Composition as Comp
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Bundles using (Setoid)
open import Categories.Category.Instance.Setoids using (Setoids)
import Categories.Morphism.Constant as Const
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

-- Setoid maps: composition, constants, discrete ℕ, and gluing a family along an index map.
infixr 9 _∘ₛ_
_∘ₛ_ : ∀ {a b c d e f} {A : Setoid a b} {B : Setoid c d} {C : Setoid e f} → Func B C → Func A B → Func A C
g ∘ₛ f = Comp.function f g

constₛ : ∀ {a b c d} {A : Setoid a b} {B : Setoid c d} → Setoid.Carrier B → Func A B
constₛ {B = B} b = record { to = λ _ → b ; cong = λ _ → Setoid.refl B }

-- every function out of a ≡-setoid is a setoid map
⇑ : ∀ {a c d} {A : Set a} {B : Setoid c d} → (A → Setoid.Carrier B) → Func (setoid A) B
⇑ {B = B} f = record { to = f ; cong = λ e → Setoid.reflexive B (≡.cong f e) }

-- `constₛ b` is a constant morphism of `Setoids` (`Categories.Morphism.Constant`)
constₛ-isConstant : ∀ {a b} {A B : Setoid a b} (x : Setoid.Carrier B) →
  Const.IsConstant (Setoids a b) {A} {B} (constₛ x)
constₛ-isConstant {B = B} x f g {_} = Setoid.refl B

-- discrete ℕ, lifted to any level
ℕˢ : ∀ {ℓ} → Setoid ℓ ℓ
ℕˢ {ℓ} = setoid (Lift ℓ ℕ)

-- ... in particular an index function into ℕ
⇑ℕ : ∀ {a ℓ} {A : Set a} → (A → ℕ) → Func (setoid A) (ℕˢ {ℓ})
⇑ℕ f = ⇑ (λ r → lift (f r))

-- r ↦ α (j r) r
glueₛ : ∀ {a b c d ℓ} {A : Setoid a b} {B : Setoid c d} → Func A (ℕˢ {ℓ}) → (ℕ → Func A B) → Func A B
glueₛ {B = B} j α = record
  { to = λ r → α (lower (j ⟨$⟩ r)) ⟨$⟩ r
  ; cong = λ {r} {r′} e → Setoid.trans B (Func.cong (α (lower (j ⟨$⟩ r))) e)
      (Setoid.reflexive B (≡.cong (λ n → α (lower n) ⟨$⟩ r′) (Func.cong j e)))
  }

-- equality of setoid maps: pointwise
infix 4 _≈ₛ_
_≈ₛ_ : ∀ {a b c d} {A : Setoid a b} {B : Setoid c d} → Func A B → Func A B → Set (a ⊔ d)
_≈ₛ_ {B = B} f g = ∀ r → Setoid._≈_ B (f ⟨$⟩ r) (g ⟨$⟩ r)

-- gluing under a map g: glue (g ∘ αₙ) is g ∘ (glue α)
glueₛ-∘ : ∀ {a b c d e f ℓ} {A : Setoid a b} {B : Setoid c d} {C : Setoid e f} {j : Func A (ℕˢ {ℓ})}
  (g : Func B C) (α : ℕ → Func A B) → glueₛ j (λ n → g ∘ₛ α n) ≈ₛ (g ∘ₛ glueₛ j α)
glueₛ-∘ {C = C} _ _ _ = Setoid.refl C

-- gluing then precomposing: (glue j f) ∘ γ is the glue of the f n ∘ γ along j ∘ γ
glueₛ-pre : ∀ {a b a′ b′ c d ℓ} {A : Setoid a b} {A′ : Setoid a′ b′} {B : Setoid c d} {j : Func A (ℕˢ {ℓ})}
  (f : ℕ → Func A B) (γ : Func A′ A) → glueₛ (j ∘ₛ γ) (λ n → f n ∘ₛ γ) ≈ₛ (glueₛ j f ∘ₛ γ)
glueₛ-pre {B = B} _ _ _ = Setoid.refl B
