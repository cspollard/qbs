{-# OPTIONS --safe --without-K #-}

-- The free additive monad on a semiring of scalars: the universal arrow of the scalars functor `Scalars X`
-- (`X = ⊤` for the scalars), i.e. an initial object of the comma category `W ↓ Scalars X`.  It is an additive monad `T`
-- with a semiring homomorphism `W → kleisli-semiring X` (in `T`'s Kleisli category) such that every additive monad `M` with a
-- homomorphism `W → kleisli-semiring X` receives a unique additive monad morphism `T ⇒ M` over `W`.  For the finite-support
-- (multiset) monad of a commutative semiring `W` this is Lemma 27 of Coumans–Jacobs (`M ⊣ E`), with `X = ⊤`.
-- No instance is constructed here: the free monad is a hypothesis, to be inhabited by a concrete model.
open import Algebra.Bundles using (Semiring)

open import Categories.Category.Core using (Category)

module Categories.Monad.Additive.Free {o h e} {C : Category o h e} (X : Category.Obj C) (W : Semiring h e) where

open import Categories.Category.Construction.Comma using (_↓_)
open import Categories.Functor.Construction.Constant using (const!)
open import Categories.Object.Initial using (Initial)

open import Categories.Category.Instance.Semirings h e using (Semirings)
open import Categories.Functor.Instance.Scalars C X using (Scalars)

-- `T` is the free additive monad on `W`
FreeAdditiveMonad : Set _
FreeAdditiveMonad = Initial (const! W ↓ Scalars)
