{-# OPTIONS --safe --without-K #-}

-- Finitary equational theories: a signature of operation symbols with arities and a set of equations between terms.
-- A model of a theory is a set with an operation for each symbol satisfying the equations; here the theories are the data
-- of `Monad.Algebraic`, where the models are the hom-sets of a Kleisli category.  (Not the `Theory.Lawvere` of
-- agda-categories: no categorical structure is needed, only the presentation.)
--   `Term Op arity n`   terms over `n` variables
--   `Theory`            operation symbols, equations `lhs ≈ rhs` over `vars` variables
module Categories.Theory.Equational where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

-- terms over `n` variables: a variable, or an operation applied to one term per argument
data Term (Op : Set) (arity : Op → ℕ) (n : ℕ) : Set where
  var : Fin n → Term Op arity n
  app : (f : Op) → (Fin (arity f) → Term Op arity n) → Term Op arity n

record Theory : Set₁ where
  field
    Op : Set
    arity : Op → ℕ
    Eqn : Set
    vars : Eqn → ℕ
    lhs rhs : (q : Eqn) → Term Op arity (vars q)

  Tm : ℕ → Set
  Tm = Term Op arity
