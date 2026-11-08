{-# OPTIONS --safe --without-K #-}

-- Algebra in a cartesian closed category, for the symmetric monoidal structure of its products
-- (`Categories.Category.Monoidal.Symmetric.Algebra`), so that instances state the familiar pointwise laws and need no
-- monoidal-category bookkeeping.
--   * `diagonal X`, the commutative comonoid `(⟨ id , id ⟩, !)` on every object `X`;
--   * `fromPointwise W mul one zero …`, the `CommutativeMonoidWithZero` over `diagonal W` of a commutative monoid with
--     an absorbing zero, given by the usual laws for all generalised elements `Z ⇒ W` (in `⟨_,_⟩` form, with the unit
--     and zero as `⊤ ⇒ W`).
-- Route: the comonoid laws are `first∘⟨⟩`, `second∘⟨⟩`, `assocʳ∘⟨⟩` and `swap∘⟨⟩` of `BinaryProducts`
-- with the uniqueness of `!`; each monoid law is the pointwise law at the projections of the product
-- (`Pointwise`), and the laws of `δ = !` into the trivial monoid on `⊤` are `!-unique₂`.
open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical

module QBS.CartesianAlgebra {o h e} {C : Category o h e} (CC : Canonical.CartesianClosed C) where

open import Categories.Category.Cartesian using (Cartesian)
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
import Categories.Category.Monoidal.Symmetric.Algebra as Algebra
open import Categories.Category.BinaryProducts C using (module BinaryProducts)
open import Categories.Object.Terminal C using (module Terminal)

open Category C
open HomReasoning
open Canonical.CartesianClosed CC using (⊤; _×_; !; ⟨_,_⟩; π₁; π₂; isCartesian)
open BinaryProducts (Cartesian.products isCartesian)
  using (_⁂_; η; unique; ⟨⟩-cong₂; ⁂∘⟨⟩; assocˡ; assocʳ; first∘⟨⟩; second∘⟨⟩; assocʳ∘⟨⟩
        ; swap; swap∘⟨⟩)
open Terminal (Cartesian.terminal isCartesian) using (!-unique; !-unique₂)

-- the symmetric monoidal structure of the products
symmetric = CSM.symmetric C isCartesian

open Algebra symmetric

------------------------------------------------------------------------
-- The diagonal comonoid

private
  Δ : ∀ {X} → X ⇒ X × X
  Δ = ⟨ id , id ⟩

  Δ-assoc : ∀ {X} → (Δ {X} ⁂ id) ∘ Δ ≈ (assocʳ ∘ (id ⁂ Δ {X})) ∘ Δ
  Δ-assoc = begin
    (Δ ⁂ id) ∘ Δ                  ≈⟨ first∘⟨⟩ ⟩
    ⟨ Δ ∘ id , id ⟩               ≈⟨ ⟨⟩-cong₂ identityʳ Equiv.refl ⟩
    ⟨ Δ , id ⟩                    ≈˘⟨ assocʳ∘⟨⟩ ⟩
    assocʳ ∘ ⟨ id , Δ ⟩          ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ Equiv.refl identityʳ ⟩
    assocʳ ∘ ⟨ id , Δ ∘ id ⟩     ≈˘⟨ refl⟩∘⟨ second∘⟨⟩ ⟩
    assocʳ ∘ (id ⁂ Δ) ∘ Δ        ≈˘⟨ assoc ⟩
    (assocʳ ∘ (id ⁂ Δ)) ∘ Δ      ∎

  Δ-identityˡ : ∀ {X} → ⟨ ! , id ⟩ ≈ (! {X} ⁂ id) ∘ Δ
  Δ-identityˡ = begin
    ⟨ ! , id ⟩                  ≈⟨ ⟨⟩-cong₂ (!-unique _) Equiv.refl ⟩
    ⟨ ! ∘ id , id ⟩             ≈˘⟨ first∘⟨⟩ ⟩
    (! ⁂ id) ∘ ⟨ id , id ⟩     ∎

  Δ-identityʳ : ∀ {X} → ⟨ id , ! ⟩ ≈ (id ⁂ ! {X}) ∘ Δ
  Δ-identityʳ = begin
    ⟨ id , ! ⟩                  ≈⟨ ⟨⟩-cong₂ Equiv.refl (!-unique _) ⟩
    ⟨ id , ! ∘ id ⟩             ≈˘⟨ second∘⟨⟩ ⟩
    (id ⁂ !) ∘ ⟨ id , id ⟩     ∎

-- the diagonal comonoid
diagonal : ∀ X → IsCommutativeComonoid X
diagonal X = record
  { isComonoid = record
    { μ = ⟨ id , id ⟩
    ; η = !
    ; assoc = Δ-assoc
    ; identityˡ = Δ-identityˡ
    ; identityʳ = Δ-identityʳ
    }
  ; cocomm = swap∘⟨⟩
  }

------------------------------------------------------------------------
-- Monoids with zero in pointwise form

module Pointwise {W : Obj} (mul : W × W ⇒ W) (one zero : ⊤ ⇒ W)
    (mul-assoc : ∀ {Z} (a b c : Z ⇒ W)
               → mul ∘ ⟨ mul ∘ ⟨ a , b ⟩ , c ⟩ ≈ mul ∘ ⟨ a , mul ∘ ⟨ b , c ⟩ ⟩)
    (mul-comm : ∀ {Z} (a b : Z ⇒ W) → mul ∘ ⟨ a , b ⟩ ≈ mul ∘ ⟨ b , a ⟩)
    (mul-one : ∀ {Z} (a : Z ⇒ W) → mul ∘ ⟨ a , one ∘ ! ⟩ ≈ a)
    (mul-zero : ∀ {Z} (a : Z ⇒ W) → mul ∘ ⟨ a , zero ∘ ! ⟩ ≈ zero ∘ !) where

  -- `⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩` is `π₁`
  π₁-eta : ∀ {A B C} → ⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ≈ π₁ {A × B} {C}
  π₁-eta = unique Equiv.refl Equiv.refl

  assoc-law : mul ∘ (mul ⁂ id) ≈ mul ∘ (id ⁂ mul) ∘ assocˡ
  assoc-law = begin
    mul ∘ ⟨ mul ∘ π₁ , id ∘ π₂ ⟩
      ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ π₁-eta) (⟺ identityˡ) ⟩
    mul ∘ ⟨ mul ∘ ⟨ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ , π₂ ⟩
      ≈⟨ mul-assoc _ _ _ ⟩
    mul ∘ ⟨ π₁ ∘ π₁ , mul ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ≈˘⟨ refl⟩∘⟨ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ Equiv.refl) ⟩
    mul ∘ (id ⁂ mul) ∘ assocˡ ∎

  identityˡ-law : π₂ ≈ mul ∘ (one ⁂ id)
  identityˡ-law = begin
    π₂                         ≈˘⟨ mul-one π₂ ⟩
    mul ∘ ⟨ π₂ , one ∘ ! ⟩     ≈˘⟨ mul-comm _ _ ⟩
    mul ∘ ⟨ one ∘ ! , π₂ ⟩     ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ !-unique₂) (⟺ identityˡ) ⟩
    mul ∘ ⟨ one ∘ π₁ , id ∘ π₂ ⟩ ∎

  identityʳ-law : π₁ ≈ mul ∘ (id ⁂ one)
  identityʳ-law = begin
    π₁                         ≈˘⟨ mul-one π₁ ⟩
    mul ∘ ⟨ π₁ , one ∘ ! ⟩     ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (⟺ identityˡ) (refl⟩∘⟨ !-unique₂) ⟩
    mul ∘ ⟨ id ∘ π₁ , one ∘ π₂ ⟩ ∎

  comm-law : mul ∘ swap ≈ mul
  comm-law = begin
    mul ∘ ⟨ π₂ , π₁ ⟩ ≈˘⟨ mul-comm π₁ π₂ ⟩
    mul ∘ ⟨ π₁ , π₂ ⟩ ≈⟨ refl⟩∘⟨ η ⟩
    mul ∘ id          ≈⟨ identityʳ ⟩
    mul               ∎

  zeroʳ-law : mul ∘ (id ⁂ zero) ≈ zero ∘ ! ∘ π₁
  zeroʳ-law = begin
    mul ∘ ⟨ id ∘ π₁ , zero ∘ π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (refl⟩∘⟨ !-unique₂) ⟩
    mul ∘ ⟨ π₁ , zero ∘ ! ⟩       ≈⟨ mul-zero π₁ ⟩
    zero ∘ !                       ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
    zero ∘ ! ∘ π₁                  ∎

-- A commutative monoid with an absorbing zero, in the usual pointwise form (laws for all generalised elements `Z ⇒ W`,
-- with the unit and zero as `⊤ ⇒ W`), as the `Algebra` structure over the diagonal comonoid.
fromPointwise : (W : Obj) (mul : W × W ⇒ W) (one zero : ⊤ ⇒ W)
  (mul-assoc : ∀ {Z} (a b c : Z ⇒ W)
             → mul ∘ ⟨ mul ∘ ⟨ a , b ⟩ , c ⟩ ≈ mul ∘ ⟨ a , mul ∘ ⟨ b , c ⟩ ⟩)
  (mul-comm : ∀ {Z} (a b : Z ⇒ W) → mul ∘ ⟨ a , b ⟩ ≈ mul ∘ ⟨ b , a ⟩)
  (mul-one : ∀ {Z} (a : Z ⇒ W) → mul ∘ ⟨ a , one ∘ ! ⟩ ≈ a)
  (mul-zero : ∀ {Z} (a : Z ⇒ W) → mul ∘ ⟨ a , zero ∘ ! ⟩ ≈ zero ∘ !) →
  CommutativeMonoidWithZero
fromPointwise W mul one zero mul-assoc mul-comm mul-one mul-zero = record
  { Carrier = W
  ; isCommutativeComonoid = diagonal W
  ; isCommutativeMonoidWithZero = record
    { *-isCommutativeMonoid = record
      { isMonoid = record
        { μ = mul
        ; η = one
        ; assoc = assoc-law
        ; identityˡ = identityˡ-law
        ; identityʳ = identityʳ-law
        }
      ; comm = comm-law
      }
    ; zero⇒ = zero
    ; zeroʳ = zeroʳ-law
    ; δ-unit = !-unique₂
    ; δ-mul = !-unique₂
    ; δ-zero = !-unique₂
    }
  }
  where open Pointwise mul one zero mul-assoc mul-comm mul-one mul-zero
