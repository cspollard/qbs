{-# OPTIONS --safe --without-K #-}

-- Algebraic monads: a monad `M` that supports the operations of an equational theory `T` (Plotkin–Power's algebraic
-- operations).  Each operation acts on every kernel set `K [ X , Y ]` of the Kleisli category `K` of `M`, satisfying the
-- equations of `T`, and composition (bind) commutes with it in every argument.  For the theory of commutative monoids
-- this is additive monads (`⊕`, `𝟘`); for the theory of abelian groups, signed measures.
--   `Operations T M`   `op` on every kernel set, with `op-cong` and `op-resp-∘` (bind is linear); `eval` of a term
--   `IsAlgebraic T M`  `Operations` satisfying the equations of `T` (`laws`)
--   `Algebraic T`      a monad with `IsAlgebraic`
-- Morphisms: `Monad.Algebraic.Morphism`; the category for fixed `T`: `Category.Instance.Monads.Algebraic`.
open import Categories.Category.Core using (Category)

module Categories.Monad.Algebraic {o h e} {C : Category o h e} where

open import Level using (_⊔_)
open import Data.Fin.Base using (Fin)

open import Categories.Category using (_[_,_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Categories.Monad using (Monad)
open import Categories.Theory.Equational

-- the operations of `T` on the kernel sets of `M`, natural for bind, and the value `eval` of a term
record Operations (T : Theory) (M : Monad C) : Set (o ⊔ h ⊔ e) where
  private
    K = Kleisli M
    module K = Category K
  open Theory T

  field
    op : ∀ (f : Op) {X Y} → (Fin (arity f) → K [ X , Y ]) → K [ X , Y ]
    op-cong : ∀ (f : Op) {X Y} {gs hs : Fin (arity f) → K [ X , Y ]}
      → (∀ i → gs i K.≈ hs i) → op f gs K.≈ op f hs
    -- bind is linear in the kernel run before, the kernels combined, and the continuation
    op-resp-∘ : ∀ (f : Op) {A B D E} (k : K [ D , E ]) (gs : Fin (arity f) → K [ B , D ]) (h : K [ A , B ])
      → k K.∘ op f gs K.∘ h K.≈ op f (λ i → k K.∘ gs i K.∘ h)

  -- the value of a term under an assignment of its variables
  eval : ∀ {n X Y} → Tm n → (Fin n → K [ X , Y ]) → K [ X , Y ]
  eval (var i) ρ = ρ i
  eval (app f ts) ρ = op f (λ i → eval (ts i) ρ)

-- `M` supports `T`: the operations satisfy the equations of `T`
record IsAlgebraic (T : Theory) (M : Monad C) : Set (o ⊔ h ⊔ e) where
  private
    K = Kleisli M
    module K = Category K
  open Theory T

  field
    operations : Operations T M
  open Operations operations public

  field
    laws : ∀ (q : Eqn) {X Y} (ρ : Fin (vars q) → K [ X , Y ]) → eval (lhs q) ρ K.≈ eval (rhs q) ρ

-- an algebraic monad for `T`: a monad with `IsAlgebraic`
record Algebraic (T : Theory) : Set (o ⊔ h ⊔ e) where
  field
    M : Monad C
    isAlgebraic : IsAlgebraic T M
  open IsAlgebraic isAlgebraic public
