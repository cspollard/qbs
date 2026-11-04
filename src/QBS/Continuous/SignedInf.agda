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
-- the cross-added equalities hold with witness 0.  The ∞ facts are in `InfAlg`; `≤∞-antisym` adds the two witnesses.
module QBS.Continuous.SignedInf where

open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (case_of_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerReals using (infC)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.InfAlg using (module InfAlg)

module SignedInf (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; Sg; _≃_; _+S_; 0S; _−_[_,_]; finite)
  open Sg
  open Bounded A using (mk≃)
  open OmegaSemiring A using (refl; sym; trans; +-cong; +-comm; ≤-trans; ≤-reflexive; ≤-antisym; +-mono; commutativeSemiring)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open import Relation.Binary.Reasoning.Setoid (OmegaSemiring.setoid A)
  open SubSemiring finite using (Is-+; Is-*; Is-0)
  open InfAlg lem₁ using (top-sum; top-ge; top-left; top-right-le; top-⊑)

  -- +∞
  ∞ᶜ : ∣A∣
  ∞ᶜ = infC

  not-bnd-top : ∀ a → (Bnd a → ⊥) → a ≈ ∞ᶜ
  not-bnd-top = InfAlg.not-bnd-top lem₁

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

  -- finite case of transitivity (the witness of `Analysis/Signed`)
  trans-fin : ∀ px nx py ny pz nz k₁ k₂ → px + ny + k₁ ≈ py + nx + k₁ → py + nz + k₂ ≈ pz + ny + k₂ →
    px + nz + (k₁ + k₂ + py + ny) ≈ pz + nx + (k₁ + k₂ + py + ny)
  trans-fin px nx py ny pz nz k₁ k₂ e₁ e₂ = begin
    px + nz + (k₁ + k₂ + py + ny)
      ≈⟨ solve 6 (λ px nz k1 k2 py ny → px :+ nz :+ (k1 :+ k2 :+ py :+ ny) := (px :+ ny :+ k1) :+ (py :+ nz :+ k2))
           refl px nz k₁ k₂ py ny ⟩
    (px + ny + k₁) + (py + nz + k₂) ≈⟨ +-cong e₁ e₂ ⟩
    (py + nx + k₁) + (pz + ny + k₂)
      ≈⟨ solve 6 (λ py nx k1 pz ny k2 → (py :+ nx :+ k1) :+ (pz :+ ny :+ k2) := pz :+ nx :+ (k1 :+ k2 :+ py :+ ny))
           refl py nx k₁ pz ny k₂ ⟩
    pz + nx + (k₁ + k₂ + py + ny) ∎

  -- infinite case: all three positive parts are ∞, so both sides are ∞ (witness 0)
  trans-top : ∀ {px nx py ny pz nz k₁ k₂} → Bnd ny → Bnd k₁ → Bnd k₂ → py ≈ ∞ᶜ → px + ny + k₁ ≈ py + nx + k₁ →
    py + nz + k₂ ≈ pz + ny + k₂ → px + nz + 0# ≈ pz + nx + 0#
  trans-top {px} {nx} {ny = ny} {pz} {nz} bn b₁ b₂ h e₁ e₂ =
    trans (top-sum (top-sum (top-left {px} bn b₁ h e₁) nz) 0#)
      (sym (top-sum (top-sum (top-left {pz} {n′ = ny} bn b₂ h (sym e₂)) nx) 0#))

  -- the same for `≤`
  trans-fin-le : ∀ px nx py ny pz nz k₁ k₂ → px + ny + k₁ ≤ py + nx + k₁ → py + nz + k₂ ≤ pz + ny + k₂ →
    px + nz + (k₁ + k₂ + py + ny) ≤ pz + nx + (k₁ + k₂ + py + ny)
  trans-fin-le px nx py ny pz nz k₁ k₂ e₁ e₂ = ≤-trans (≤-reflexive (solve 6
    (λ px nz k1 k2 py ny → px :+ nz :+ (k1 :+ k2 :+ py :+ ny) := (px :+ ny :+ k1) :+ (py :+ nz :+ k2)) refl px nz k₁ k₂ py ny))
    (≤-trans (+-mono e₁ e₂) (≤-reflexive (solve 6
    (λ py nx k1 pz ny k2 → (py :+ nx :+ k1) :+ (pz :+ ny :+ k2) := pz :+ nx :+ (k1 :+ k2 :+ py :+ ny)) refl py nx k₁ pz ny k₂)))

  trans-top-le : ∀ {px nx py ny pz nz k₂} → Bnd ny → Bnd k₂ → py ≈ ∞ᶜ →
    py + nz + k₂ ≤ pz + ny + k₂ → px + nz + 0# ≤ pz + nx + 0#
  trans-top-le {nx = nx} {ny = ny} {pz = pz} bn b₂ h e₂ =
    top-ge (top-sum (top-sum (top-right-le bn b₂ h e₂) nx) 0#) _

  -- adding a further witness
  ext-le : ∀ a b k₁ k₂ → a + k₁ ≤ b + k₁ → a + (k₁ + k₂) ≤ b + (k₁ + k₂)
  ext-le a b k₁ k₂ h = ≤-trans (≤-reflexive (solve 3 (λ a k₁ k₂ → a :+ (k₁ :+ k₂) := (a :+ k₁) :+ k₂) refl a k₁ k₂))
    (≤-trans (+-mono h (≤-reflexive refl)) (≤-reflexive (solve 3 (λ b k₁ k₂ → (b :+ k₁) :+ k₂ := b :+ (k₁ :+ k₂)) refl b k₁ k₂)))

  ext-le′ : ∀ a b k₁ k₂ → a + k₂ ≤ b + k₂ → a + (k₁ + k₂) ≤ b + (k₁ + k₂)
  ext-le′ a b k₁ k₂ h = ≤-trans (≤-reflexive (solve 3 (λ a k₁ k₂ → a :+ (k₁ :+ k₂) := a :+ (k₂ :+ k₁)) refl a k₁ k₂))
    (≤-trans (ext-le a b k₂ k₁ h) (≤-reflexive (solve 3 (λ b k₁ k₂ → b :+ (k₂ :+ k₁) := b :+ (k₁ :+ k₂)) refl b k₁ k₂)))

  ≃∞-refl : ∀ {x} → x ≃∞ x
  ≃∞-refl = mk≃∞ 0# Is-0 refl

  ≃∞-sym : ∀ {x y} → x ≃∞ y → y ≃∞ x
  ≃∞-sym (mk≃∞ k fk e) = mk≃∞ k fk (sym e)

  ≃∞-trans : ∀ {x y z} → x ≃∞ y → y ≃∞ z → x ≃∞ z
  ≃∞-trans {x} {y} {z} (mk≃∞ k₁ f₁ e₁) (mk≃∞ k₂ f₂ e₂) = case lem₁ (Bnd (pos∞ y)) of λ
    { (inj₁ by) → mk≃∞ (k₁ + k₂ + pos∞ y + neg∞ y) (Is-+ (Is-+ (Is-+ f₁ f₂) by) (neg∞-fin y))
        (trans-fin (pos∞ x) (neg∞ x) (pos∞ y) (neg∞ y) (pos∞ z) (neg∞ z) k₁ k₂ e₁ e₂)
    ; (inj₂ ny) → mk≃∞ 0# Is-0 (trans-top {pos∞ x} {neg∞ x} {pos∞ y} {neg∞ y} {pos∞ z} {neg∞ z} (neg∞-fin y) f₁ f₂
        (not-bnd-top (pos∞ y) ny) e₁ e₂) }

  ≤∞-refl : ∀ {x y} → x ≃∞ y → x ≤∞ y
  ≤∞-refl (mk≃∞ k fk e) = mk≤∞ k fk (≤-reflexive e)

  ≤∞-trans : ∀ {x y z} → x ≤∞ y → y ≤∞ z → x ≤∞ z
  ≤∞-trans {x} {y} {z} (mk≤∞ k₁ f₁ e₁) (mk≤∞ k₂ f₂ e₂) = case lem₁ (Bnd (pos∞ y)) of λ
    { (inj₁ by) → mk≤∞ (k₁ + k₂ + pos∞ y + neg∞ y) (Is-+ (Is-+ (Is-+ f₁ f₂) by) (neg∞-fin y))
        (trans-fin-le (pos∞ x) (neg∞ x) (pos∞ y) (neg∞ y) (pos∞ z) (neg∞ z) k₁ k₂ e₁ e₂)
    ; (inj₂ ny) → mk≤∞ 0# Is-0 (trans-top-le {pos∞ x} {neg∞ x} {pos∞ y} {neg∞ y} {pos∞ z} {neg∞ z} {k₂} (neg∞-fin y) f₂
        (not-bnd-top (pos∞ y) ny) e₂) }

  ≤∞-antisym : ∀ {x y} → x ≤∞ y → y ≤∞ x → x ≃∞ y
  ≤∞-antisym {x} {y} (mk≤∞ k₁ f₁ e₁) (mk≤∞ k₂ f₂ e₂) = mk≃∞ (k₁ + k₂) (Is-+ f₁ f₂)
    (≤-antisym (ext-le _ _ k₁ k₂ e₁) (ext-le′ _ _ k₁ k₂ e₂))

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
  scale∞ {c} bc x = (c * pos∞ x) −∞ (c * neg∞ x) [ Is-* bc (neg∞-fin x) ]

  -- laws
  ι∞-cong : ∀ {x y} → x ≃ y → ι∞ x ≃∞ ι∞ y
  ι∞-cong (mk≃ k fk e) = mk≃∞ k fk e

  ι∞-+ : ∀ x y → ι∞ (x +S y) ≃∞ ι∞ x +∞ ι∞ y
  ι∞-+ x y = ≃∞-refl

  ι∞-reflect : ∀ {x y} → ι∞ x ≃∞ ι∞ y → x ≃ y
  ι∞-reflect (mk≃∞ k fk e) = mk≃ k fk e

  +∞-cong : ∀ {x x′ y y′} → x ≃∞ x′ → y ≃∞ y′ → x +∞ y ≃∞ x′ +∞ y′
  +∞-cong (mk≃∞ k₁ f₁ e₁) (mk≃∞ k₂ f₂ e₂) = mk≃∞ (k₁ + k₂) (Is-+ f₁ f₂) (trans (solve 6
    (λ a b c d k l → (a :+ c) :+ (b :+ d) :+ (k :+ l) := (a :+ b :+ k) :+ (c :+ d :+ l)) refl _ _ _ _ _ _)
    (trans (+-cong e₁ e₂) (solve 6
    (λ a b c d k l → (a :+ b :+ k) :+ (c :+ d :+ l) := (a :+ c) :+ (b :+ d) :+ (k :+ l)) refl _ _ _ _ _ _)))

  +∞-comm : ∀ x y → x +∞ y ≃∞ y +∞ x
  +∞-comm x y = mk≃∞ 0# Is-0 (solve 4 (λ a b c d → (a :+ c) :+ (d :+ b) :+ con 0 := (c :+ a) :+ (b :+ d) :+ con 0) refl
    (pos∞ x) (neg∞ x) (pos∞ y) (neg∞ y))

  +∞-assoc : ∀ x y z → (x +∞ y) +∞ z ≃∞ x +∞ (y +∞ z)
  +∞-assoc x y z = mk≃∞ 0# Is-0 (solve 6 (λ a b c d e f →
    (a :+ c :+ e) :+ (b :+ (d :+ f)) :+ con 0 := (a :+ (c :+ e)) :+ (b :+ d :+ f) :+ con 0) refl
    (pos∞ x) (neg∞ x) (pos∞ y) (neg∞ y) (pos∞ z) (neg∞ z))

  +∞-identityˡ : ∀ x → ι∞ 0S +∞ x ≃∞ x
  +∞-identityˡ x = mk≃∞ 0# Is-0 (solve 2 (λ px nx → (con 0 :+ px) :+ nx :+ con 0 := px :+ (con 0 :+ nx) :+ con 0) refl
    (pos∞ x) (neg∞ x))

  +∞-mono : ∀ {x x′ y y′} → x ≤∞ x′ → y ≤∞ y′ → x +∞ y ≤∞ x′ +∞ y′
  +∞-mono (mk≤∞ k₁ f₁ e₁) (mk≤∞ k₂ f₂ e₂) = mk≤∞ (k₁ + k₂) (Is-+ f₁ f₂) (≤-trans (≤-reflexive (solve 6
    (λ a b c d k l → (a :+ c) :+ (b :+ d) :+ (k :+ l) := (a :+ b :+ k) :+ (c :+ d :+ l)) refl _ _ _ _ _ _))
    (≤-trans (+-mono e₁ e₂) (≤-reflexive (solve 6
    (λ a b c d k l → (a :+ b :+ k) :+ (c :+ d :+ l) := (a :+ c) :+ (b :+ d) :+ (k :+ l)) refl _ _ _ _ _ _))))

  +∞-top : ∀ x → x +∞ top∞ ≃∞ top∞
  +∞-top x = mk≃∞ 0# Is-0 (trans (top-sum (top-sum (trans (+-comm _ _) (top-sum refl _)) 0#) 0#)
    (sym (top-sum (top-sum refl _) 0#)))

  ≤∞-top : ∀ x → x ≤∞ top∞
  ≤∞-top x = mk≤∞ 0# Is-0 (top-ge (top-sum (top-sum refl _) 0#) _)

  fromPos-mono : ∀ {a b} → a ≤ b → fromPos a ≤∞ fromPos b
  fromPos-mono h = mk≤∞ 0# Is-0 (+-mono (+-mono h (≤-reflexive refl)) (≤-reflexive refl))

  fromPos-+ : ∀ a b → fromPos (a + b) ≃∞ fromPos a +∞ fromPos b
  fromPos-+ a b = mk≃∞ 0# Is-0 (solve 2 (λ a b → (a :+ b) :+ (con 0 :+ con 0) :+ con 0 := (a :+ b) :+ con 0 :+ con 0) refl a b)

  scale∞-+ : ∀ {c} (bc : Bnd c) x y → scale∞ bc (x +∞ y) ≃∞ scale∞ bc x +∞ scale∞ bc y
  scale∞-+ {c} bc x y = mk≃∞ 0# Is-0 (solve 5 (λ c a b d e →
    c :* (a :+ b) :+ (c :* d :+ c :* e) :+ con 0 := (c :* a :+ c :* b) :+ c :* (d :+ e) :+ con 0) refl
    c (pos∞ x) (pos∞ y) (neg∞ x) (neg∞ y))

  -- finite values come from `Sg`
  fin∞ : ∀ x → Bnd (pos∞ x) → Σ Sg (λ y → ι∞ y ≃∞ x)
  fin∞ x bp = (pos∞ x − neg∞ x [ bp , neg∞-fin x ]) , ≃∞-refl
