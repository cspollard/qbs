{-# OPTIONS --safe --without-K #-}

-- Flat names for the parts of a monad `T`, to avoid projection chains such as `T.F.F₁`, `T.η.η`, `T.μ.η`.  Use it as a
-- module alias, `module M = Notation T`, so that two monads in scope keep distinct names:
--   `M.₀ X`  the object `T X`        `M.₁ f`  the arrow `T f`
--   `M.η X`  the unit `X ⇒ T X`      `M.μ X`  the multiplication `T (T X) ⇒ T X`
-- and the laws that proofs use: `M.homomorphism`, `M.identity`, `M.₁-resp-≈` (functoriality), and the naturality of
-- the unit and multiplication, `M.η-commute`, `M.η-sym-commute`, `M.μ-commute`, `M.μ-sym-commute`.
open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)

module Categories.Monad.Notation {o ℓ e} {C : Category o ℓ e} (T : Monad C) where

open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)

private module T = Monad T

open Functor T.F public using (homomorphism; identity) renaming (F₀ to ₀; F₁ to ₁; F-resp-≈ to ₁-resp-≈)
open NaturalTransformation T.η public using (η) renaming (commute to η-commute; sym-commute to η-sym-commute)
open NaturalTransformation T.μ public using () renaming (η to μ; commute to μ-commute; sym-commute to μ-sym-commute)
