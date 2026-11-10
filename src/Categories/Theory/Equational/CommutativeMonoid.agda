{-# OPTIONS --safe --without-K #-}

-- The equational theory of commutative monoids: a constant `unit` and a binary `plus` with associativity, commutativity
-- and the left unit law.  Its algebraic monads are the additive monads.
module Categories.Theory.Equational.CommutativeMonoid where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (zero; suc)

open import Categories.Theory.Equational

data CMOp : Set where
  unit plus : CMOp

cm-arity : CMOp → ℕ
cm-arity unit = 0
cm-arity plus = 2

data CMEqn : Set where
  assoc comm identity : CMEqn

cm-vars : CMEqn → ℕ
cm-vars assoc = 3
cm-vars comm = 2
cm-vars identity = 1

private
  Tm : ℕ → Set
  Tm = Term CMOp cm-arity

  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Tm n → Tm n → Tm n
  a ⊞ b = app plus λ { zero → a ; (suc zero) → b }

  𝟎 : ∀ {n} → Tm n
  𝟎 = app unit λ ()

cm-lhs : (q : CMEqn) → Tm (cm-vars q)
cm-lhs assoc = (var zero ⊞ var (suc zero)) ⊞ var (suc (suc zero))
cm-lhs comm = var zero ⊞ var (suc zero)
cm-lhs identity = 𝟎 ⊞ var zero

cm-rhs : (q : CMEqn) → Tm (cm-vars q)
cm-rhs assoc = var zero ⊞ (var (suc zero) ⊞ var (suc (suc zero)))
cm-rhs comm = var (suc zero) ⊞ var zero
cm-rhs identity = var zero

CommMonoid : Theory
CommMonoid = record
  { Op = CMOp ; arity = cm-arity ; Eqn = CMEqn ; vars = cm-vars ; lhs = cm-lhs ; rhs = cm-rhs }
