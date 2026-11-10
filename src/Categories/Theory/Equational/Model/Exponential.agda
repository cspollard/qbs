{-# OPTIONS --safe --without-K #-}

-- In a cartesian closed category, a model `X` of `T` gives the model `[ A , X ]₀` (the exponential `X ^ A`): the
-- transfer along `(− × A) ⊣ [ A , − ]` of `Model.Adjoint`.
open import Categories.Category.Core using (Category)
open import Categories.Theory.Equational using (Theory)
import Categories.Category.CartesianClosed as CartesianClosed

module Categories.Theory.Equational.Model.Exponential
  {o h e} {C : Category o h e} (CCC : CartesianClosed.CartesianClosed C) (T : Theory)
  where

import Categories.Theory.Equational.Model C T as M
open CartesianClosed.CartesianMonoidalClosed C CCC using (adjoint; [_,_]₀)

module _ A where
  open import Categories.Theory.Equational.Model.Adjoint T (adjoint {A}) using (transfer)

  exponential : ∀ {X} → M.IsModel X → M.IsModel [ A , X ]₀
  exponential = transfer
