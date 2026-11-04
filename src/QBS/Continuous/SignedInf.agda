{-# OPTIONS --safe --without-K #-}

-- Signed values in (−∞, ∞] (plan 03, "Signed layer"; decided 2026-11-04).
--   * `Sg∞`: a pair p − n with n finite (`Bnd`) and p any element of [0, ∞]; `x ≃∞ y` when p + n′ + c ≈ p′ + n + c for
--     a finite c.  Addition is total (there is no −∞, so no ∞ − ∞), and the witness cannot collapse the type since
--     n, n′ and c are finite.  Negation is not total.
--   * `_+∞_`, `scale∞` (a finite nonnegative constant), `ι∞ : Sg → Sg∞`, `fromPos` (a value in [0, ∞]), `top∞` (+∞),
--     the order `_≤∞_` (cross-added, finite witness), and their laws;
--   * `fin∞`: a value whose positive part is finite comes from `Sg`.
-- Route: as `Analysis/Signed`, except transitivity of `≃∞` and `≤∞`: the old witness c + d + p′ + n′ is not finite when
-- p′ = ∞.  By excluded middle either p′ is finite (the old proof), or not, and then p and p″ are not finite either
-- (x + a ≈ y with a finite: `MonusAlg.cut-total`, `BoundedCancel.cancel-bnd`), so all three are ∞ (`not-bnd-top`) and
-- the cross-added equalities hold with witness 0.
--   Skeleton: holes first.
module QBS.Continuous.SignedInf where

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Empty using (⊥)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (infC)
open import QBS.Analysis.Signed using (SubSemiring)

module SignedInf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; Sg; _≃_; _+S_; 0S; _−_[_,_]; finite)
  open Sg

  -- +∞
  ∞ᶜ : ∣A∣
  ∞ᶜ = infC

  not-bnd-top : ∀ a → (Bnd a → ⊥) → a ≈ ∞ᶜ
  not-bnd-top = ?

  record Sg∞ : Set₁ where
    constructor _−∞_[_]
    field
      pos∞ neg∞ : ∣A∣
      neg∞-fin : Bnd neg∞
  open Sg∞

  infix 4 _≃∞_ _≤∞_
  record _≃∞_ (x y : Sg∞) : Set₁ where
    constructor mk≃∞
    field
      k : ∣A∣
      k-fin : Bnd k
      eq : pos∞ x + neg∞ y + k ≈ pos∞ y + neg∞ x + k

  record _≤∞_ (x y : Sg∞) : Set₁ where
    constructor mk≤∞
    field
      k : ∣A∣
      k-fin : Bnd k
      le : pos∞ x + neg∞ y + k ≤ pos∞ y + neg∞ x + k

  ≃∞-refl : ∀ {x} → x ≃∞ x
  ≃∞-refl = ?

  ≃∞-sym : ∀ {x y} → x ≃∞ y → y ≃∞ x
  ≃∞-sym = ?

  ≃∞-trans : ∀ {x y z} → x ≃∞ y → y ≃∞ z → x ≃∞ z
  ≃∞-trans = ?

  ≤∞-refl : ∀ {x y} → x ≃∞ y → x ≤∞ y
  ≤∞-refl = ?

  ≤∞-trans : ∀ {x y z} → x ≤∞ y → y ≤∞ z → x ≤∞ z
  ≤∞-trans = ?

  ≤∞-antisym : ∀ {x y} → x ≤∞ y → y ≤∞ x → x ≃∞ y
  ≤∞-antisym = ?

  -- embeddings and constants
  ι∞ : Sg → Sg∞
  ι∞ x = pos x −∞ neg x [ neg-fin x ]

  fromPos : ∣A∣ → Sg∞
  fromPos a = a −∞ 0# [ SubSemiring.Is-0 finite ]

  top∞ : Sg∞
  top∞ = fromPos ∞ᶜ

  infixl 6 _+∞_
  _+∞_ : Sg∞ → Sg∞ → Sg∞
  x +∞ y = (pos∞ x + pos∞ y) −∞ (neg∞ x + neg∞ y) [ SubSemiring.Is-+ finite (neg∞-fin x) (neg∞-fin y) ]

  -- scaling by a finite nonnegative constant
  scale∞ : ∀ {c} → Bnd c → Sg∞ → Sg∞
  scale∞ = ?

  -- laws
  ι∞-cong : ∀ {x y} → x ≃ y → ι∞ x ≃∞ ι∞ y
  ι∞-cong = ?

  ι∞-+ : ∀ x y → ι∞ (x +S y) ≃∞ ι∞ x +∞ ι∞ y
  ι∞-+ = ?

  ι∞-reflect : ∀ {x y} → ι∞ x ≃∞ ι∞ y → x ≃ y
  ι∞-reflect = ?

  +∞-cong : ∀ {x x′ y y′} → x ≃∞ x′ → y ≃∞ y′ → x +∞ y ≃∞ x′ +∞ y′
  +∞-cong = ?

  +∞-comm : ∀ x y → x +∞ y ≃∞ y +∞ x
  +∞-comm = ?

  +∞-assoc : ∀ x y z → (x +∞ y) +∞ z ≃∞ x +∞ (y +∞ z)
  +∞-assoc = ?

  +∞-identityˡ : ∀ x → ι∞ 0S +∞ x ≃∞ x
  +∞-identityˡ = ?

  +∞-mono : ∀ {x x′ y y′} → x ≤∞ x′ → y ≤∞ y′ → x +∞ y ≤∞ x′ +∞ y′
  +∞-mono = ?

  +∞-top : ∀ x → x +∞ top∞ ≃∞ top∞
  +∞-top = ?

  ≤∞-top : ∀ x → x ≤∞ top∞
  ≤∞-top = ?

  fromPos-mono : ∀ {a b} → a ≤ b → fromPos a ≤∞ fromPos b
  fromPos-mono = ?

  fromPos-+ : ∀ a b → fromPos (a + b) ≃∞ fromPos a +∞ fromPos b
  fromPos-+ = ?

  scale∞-+ : ∀ {c} (bc : Bnd c) x y → scale∞ bc (x +∞ y) ≃∞ scale∞ bc x +∞ scale∞ bc y
  scale∞-+ = ?

  -- finite values come from `Sg`
  fin∞ : ∀ x → Bnd (pos∞ x) → Σ Sg (λ y → ι∞ y ≃∞ x)
  fin∞ = ?
