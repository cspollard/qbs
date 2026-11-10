{-# OPTIONS --safe --without-K #-}

-- The equational theory of commutative semirings: constants `zro`, `one` and binary `add`, `mul`, with `(add, zro)` and
-- `(mul, one)` commutative monoids, `mul` distributing over `add`, and `zro` absorbing.  A model in `C` is an internal
-- commutative semiring; `Monad.Algebraic.Scalars` shows that the scalars `M ⊤` of a commutative additive monad are one.
module Categories.Theory.Equational.CommutativeSemiring where

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Fin.Base using (Fin; zero; suc)

open import Categories.Theory.Equational
import Categories.Theory.Equational.CommutativeMonoid as CM

data CSOp : Set where
  zro one add mul : CSOp

cs-arity : CSOp → ℕ
cs-arity zro = 0
cs-arity one = 0
cs-arity add = 2
cs-arity mul = 2

data CSEqn : Set where
  add-assoc add-comm add-identity : CSEqn
  mul-assoc mul-comm mul-identity : CSEqn
  distrib annihilate : CSEqn

cs-vars : CSEqn → ℕ
cs-vars add-assoc = 3
cs-vars add-comm = 2
cs-vars add-identity = 1
cs-vars mul-assoc = 3
cs-vars mul-comm = 2
cs-vars mul-identity = 1
cs-vars distrib = 3
cs-vars annihilate = 1

private
  Tm : ℕ → Set
  Tm = Term CSOp cs-arity

  infixl 6 _⊞_
  infixl 7 _⊠_
  _⊞_ _⊠_ : ∀ {n} → Tm n → Tm n → Tm n
  a ⊞ b = app add λ { zero → a ; (suc zero) → b }
  a ⊠ b = app mul λ { zero → a ; (suc zero) → b }

  𝟎 𝟏 : ∀ {n} → Tm n
  𝟎 = app zro λ ()
  𝟏 = app one λ ()

  -- the first three variables
  v₀ : ∀ {n} → Tm (ℕ.suc n)
  v₀ = var zero
  v₁ : ∀ {n} → Tm (ℕ.suc (ℕ.suc n))
  v₁ = var (suc zero)
  v₂ : ∀ {n} → Tm (ℕ.suc (ℕ.suc (ℕ.suc n)))
  v₂ = var (suc (suc zero))

-- the additive and the multiplicative structure are two copies of the commutative monoid theory: translate its terms
add-embed mul-embed : ∀ {n} → Term CM.CMOp CM.cm-arity n → Term CSOp cs-arity n
add-embed (var i) = var i
add-embed (app CM.unit ts) = app zro (λ i → add-embed (ts i))
add-embed (app CM.plus ts) = app add (λ i → add-embed (ts i))
mul-embed (var i) = var i
mul-embed (app CM.unit ts) = app one (λ i → mul-embed (ts i))
mul-embed (app CM.plus ts) = app mul (λ i → mul-embed (ts i))

cs-lhs : (q : CSEqn) → Tm (cs-vars q)
cs-lhs add-assoc = add-embed (CM.cm-lhs CM.assoc)
cs-lhs add-comm = add-embed (CM.cm-lhs CM.comm)
cs-lhs add-identity = add-embed (CM.cm-lhs CM.identity)
cs-lhs mul-assoc = mul-embed (CM.cm-lhs CM.assoc)
cs-lhs mul-comm = mul-embed (CM.cm-lhs CM.comm)
cs-lhs mul-identity = mul-embed (CM.cm-lhs CM.identity)
cs-lhs distrib = v₀ ⊠ (v₁ ⊞ v₂)
cs-lhs annihilate = 𝟎 ⊠ v₀

cs-rhs : (q : CSEqn) → Tm (cs-vars q)
cs-rhs add-assoc = add-embed (CM.cm-rhs CM.assoc)
cs-rhs add-comm = add-embed (CM.cm-rhs CM.comm)
cs-rhs add-identity = add-embed (CM.cm-rhs CM.identity)
cs-rhs mul-assoc = mul-embed (CM.cm-rhs CM.assoc)
cs-rhs mul-comm = mul-embed (CM.cm-rhs CM.comm)
cs-rhs mul-identity = mul-embed (CM.cm-rhs CM.identity)
cs-rhs distrib = v₀ ⊠ v₁ ⊞ v₀ ⊠ v₂
cs-rhs annihilate = 𝟎

CommSemiring : Theory
CommSemiring = record
  { Op = CSOp ; arity = cs-arity ; Eqn = CSEqn ; vars = cs-vars ; lhs = cs-lhs ; rhs = cs-rhs }
