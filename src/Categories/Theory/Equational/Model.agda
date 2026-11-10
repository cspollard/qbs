{-# OPTIONS --safe --without-K #-}

-- Models of an equational theory `T` in a category `C`: an object `X` whose hom-sets `Z ⇒ X` carry the operations of `T`,
-- naturally in `Z` (precomposition), and satisfy the equations.  By Yoneda this is a model `Xⁿ → X` in the Lawvere sense,
-- without needing the powers `Xⁿ` to exist.
--   `Operations X`           the operations on the hom-sets `Z ⇒ X`, with `eval` of a term
--   `IsModel X`              `Operations` satisfying the equations
--   `Model.Adjoint`          for `L ⊣ R`, a model `X` of `D` gives a model `R X` of `C`
--   `Model.Exponential`      in particular, a model `X` gives a model `X ^ A`
open import Categories.Category.Core using (Category)
open import Categories.Theory.Equational using (Theory)

module Categories.Theory.Equational.Model {o h e} (C : Category o h e) (T : Theory) where

open import Level using (_⊔_)
open import Data.Fin.Base using (Fin)

open import Categories.Theory.Equational using (Term; var; app)

open Category C hiding (op)
open Theory T

record Operations (X : Obj) : Set (o ⊔ h ⊔ e) where
  field
    op : ∀ (φ : Op) {Z} → (Fin (arity φ) → Z ⇒ X) → Z ⇒ X
    op-cong : ∀ (φ : Op) {Z} {gs hs : Fin (arity φ) → Z ⇒ X} → (∀ i → gs i ≈ hs i) → op φ gs ≈ op φ hs
    -- a change of context is linear
    op-resp-∘ : ∀ (φ : Op) {Z W} (gs : Fin (arity φ) → Z ⇒ X) (g : W ⇒ Z) → op φ gs ∘ g ≈ op φ (λ i → gs i ∘ g)

  -- the value of a term under an assignment of its variables
  eval : ∀ {n Z} → Tm n → (Fin n → Z ⇒ X) → Z ⇒ X
  eval (var i) ρ = ρ i
  eval (app φ ts) ρ = op φ (λ i → eval (ts i) ρ)

record IsModel (X : Obj) : Set (o ⊔ h ⊔ e) where
  field
    operations : Operations X
  open Operations operations public

  field
    laws : ∀ (q : Eqn) {Z} (ρ : Fin (vars q) → Z ⇒ X) → eval (lhs q) ρ ≈ eval (rhs q) ρ
