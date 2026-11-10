{-# OPTIONS --safe --without-K #-}

-- Scalars of a commutative monad `M`: the kernels `Z ⇒ M ⊤` (measures on the one-point space depending on a context `Z`).
-- The product `f ⋆ g` runs `f`, then `g` in the same context (the strength of `M`); its unit is the Dirac mass `𝟙`.
-- `ScalarAlgebra T AL`: for a monad that supports a theory `T` (`Monad.Algebraic`) the scalars form a commutative monoid
-- under `⋆` whose multiplication is linear for the operations of `T`.  For commutative monoids (`Monad.Additive`) this is
-- the semiring of scalars; for abelian groups, a ring.  The laws are stated at every context `Z`, which by Yoneda is the
-- same as making `M ⊤` an internal monoid.
open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
open import QBS.Monad.CommMonad using (CartCommMonad)

module Categories.Monad.Algebraic.Scalars
  {o h e} {C : Category o h e} {CC : Canonical.CartesianClosed C}
  (cm : CartCommMonad CC)
  where

open import Level using (_⊔_)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)

import Categories.Monad.Notation as Notation
import Categories.NaturalTransformation as NT
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Strong using (StrongMonad; Strength)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational using (Theory)

open Category C hiding (op)
open Canonical.CartesianClosed CC using (⊤; !; π₁; ⟨_,_⟩)

private
  module M = Notation (CommutativeMonad.M cm)
  module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))

infixr 7 _⋆_
_⋆_ : ∀ {Z} → Z ⇒ M.₀ ⊤ → Z ⇒ M.₀ ⊤ → Z ⇒ M.₀ ⊤
_⋆_ {Z} f g = M.μ ⊤ ∘ M.₁ (g ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , f ⟩

𝟙 : ∀ {Z} → Z ⇒ M.₀ ⊤
𝟙 = M.η ⊤ ∘ !

record ScalarAlgebra (T : Theory) (AL : IsAlgebraic T (CommutativeMonad.M cm)) : Set (o ⊔ h ⊔ e) where
  open Theory T
  open IsAlgebraic AL
  field
    ⋆-cong : ∀ {Z} {f f′ g g′ : Z ⇒ M.₀ ⊤} → f ≈ f′ → g ≈ g′ → f ⋆ g ≈ f′ ⋆ g′
    ⋆-assoc : ∀ {Z} (f g k : Z ⇒ M.₀ ⊤) → (f ⋆ g) ⋆ k ≈ f ⋆ (g ⋆ k)
    ⋆-comm : ∀ {Z} (f g : Z ⇒ M.₀ ⊤) → f ⋆ g ≈ g ⋆ f
    ⋆-identityˡ : ∀ {Z} (f : Z ⇒ M.₀ ⊤) → 𝟙 ⋆ f ≈ f
    -- linear in each argument (the second by `⋆-comm`)
    ⋆-op : ∀ (φ : Op) {Z} (gs : Fin (arity φ) → Z ⇒ M.₀ ⊤) (k : Z ⇒ M.₀ ⊤)
      → op φ gs ⋆ k ≈ op φ (λ i → gs i ⋆ k)

-- holds for every theory: the laws are those of the strength of `M` and `op-resp-∘`
scalar-algebra : ∀ (T : Theory) (AL : IsAlgebraic T (CommutativeMonad.M cm)) → ScalarAlgebra T AL
scalar-algebra T AL = {!!}
