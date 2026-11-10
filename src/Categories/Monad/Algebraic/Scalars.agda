{-# OPTIONS --safe --without-K #-}

-- Scalars of a commutative monad `M`: the kernels `Z ⇒ M ⊤` (measures on the one-point space depending on a context `Z`).
-- The product `f ⋆ g` runs `f`, then `g` in the same context (the strength of `M`); its unit is the Dirac mass `𝟙`.
-- `scalarModel AL`: for a monad algebraic for commutative monoids (`Monad.Algebraic`), `M ⊤` is a model of `CommSemiring`
-- internal to `C` (`Theory.Equational.Model`): `⊕`, `𝟘` from the kernels, `⋆`, `𝟙` from the strength, and the semiring laws.
-- For abelian groups the analogue is a ring.
-- That `(M ⊤, id)` is terminal among semirings `W` with a homomorphism `W → M ⊤` is general nonsense (any `(S, id)` is
-- terminal in the slice over `S`), so it is not formalized: the weights are `M ⊤`, not further data
-- (`plans/08-canonical-weights.md`).
open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical
open import QBS.Monad.CommMonad using (CartCommMonad)

module Categories.Monad.Algebraic.Scalars
  {o h e} {C : Category o h e} {CC : Canonical.CartesianClosed C}
  (cm : CartCommMonad CC)
  where

open import Level using (_⊔_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_,_)
open import Algebra using (Op₂)

import Categories.Monad.Notation as Notation
open import Categories.Monad using (Monad)
open import Categories.Category.Construction.Kleisli using (Kleisli)
import Categories.Theory.Equational.CommutativeMonoid as CM
import Categories.Theory.Equational.CommutativeSemiring as CS
open CM using (CommMonoid)
open CS using (CommSemiring)
open import Categories.Theory.Equational.Model C
import Categories.Monad.Algebraic.Properties as Properties
open import Categories.Theory.Equational.Model.CommutativeSemiring C using (fromMonoids)
import Categories.NaturalTransformation as NT
open import Categories.Monad.Commutative using (CommutativeMonad)
open import Categories.Monad.Strong using (StrongMonad; Strength)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational using (Theory)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Cartesian C using (Cartesian)


open Category C hiding (op)
open HomReasoning
open Canonical.CartesianClosed CC using (⊤; !; !-unique; _×_; π₁; π₂; π₁-comp; π₂-comp; ⟨_,_⟩; isCartesian)
open CartesianMonoidal isCartesian using (monoidal)
open import Categories.Object.Monoid monoidal using (IsMonoid)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.BinaryProducts C using (module BinaryProducts)
open BinaryProducts (Cartesian.products isCartesian) using (_⁂_; ⁂∘⟨⟩; ⟨⟩∘; ⟨⟩-cong₂; ⁂-cong₂; π₁∘⁂)
open Monoidal monoidal using (module associator)
import Algebra.Structures as S
import Categories.Morphism.Reasoning C as MR
open MR using (pullˡ; pullʳ; cancelˡ)

private
  module M = Notation (CommutativeMonad.M cm)
  module Mon = Monad (CommutativeMonad.M cm)
  module Str = Strength (StrongMonad.strength (CommutativeMonad.strongMonad cm))
  module K = Category (Kleisli (CommutativeMonad.M cm))
  module σ = NT.NaturalTransformation (Strength.strengthen (StrongMonad.strength (CommutativeMonad.strongMonad cm)))

Scalar : Obj
Scalar = M.₀ ⊤

ScalarAt : Obj → Set h
ScalarAt Z = Z ⇒ Scalar

infixr 7 _⋆_
_⋆_ : ∀ {Z} → Op₂ (ScalarAt Z)
_⋆_ {Z} f g = M.μ ⊤ ∘ M.₁ (g ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , f ⟩

𝟙 : ∀ {Z} → ScalarAt Z
𝟙 = M.η ⊤ ∘ !

⋆-cong : ∀ {Z} {f f′ g g′ : ScalarAt Z} → f ≈ f′ → g ≈ g′ → f ⋆ g ≈ f′ ⋆ g′
⋆-cong ef eg = refl⟩∘⟨ M.₁-resp-≈ (eg ⟩∘⟨refl) ⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ Equiv.refl ef

-- `⋆` commutes with a change of context: naturality of the strength in the context
⋆-∘ : ∀ {Z W} (f k : ScalarAt Z) (g : W ⇒ Z) → (f ⋆ k) ∘ g ≈ (f ∘ g) ⋆ (k ∘ g)
⋆-∘ {Z} {W} f k g = begin
  (M.μ ⊤ ∘ M.₁ (k ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , f ⟩) ∘ g
    ≈⟨ assoc ○ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ assoc) ⟩
  M.μ ⊤ ∘ M.₁ (k ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , f ⟩ ∘ g
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⟨⟩∘ ○ ⟨⟩-cong₂ identityˡ Equiv.refl ○ ⟺ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityʳ identityˡ)) ⟩
  M.μ ⊤ ∘ M.₁ (k ∘ π₁) ∘ σ.η (Z , ⊤) ∘ (g ⁂ id) ∘ ⟨ id , f ∘ g ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ σ-nat ⟩∘⟨refl ○ assoc) ⟩
  M.μ ⊤ ∘ M.₁ (k ∘ π₁) ∘ M.₁ (g ⁂ id) ∘ σ.η (W , ⊤) ∘ ⟨ id , f ∘ g ⟩
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ M.homomorphism) ⟩
  M.μ ⊤ ∘ M.₁ ((k ∘ π₁) ∘ (g ⁂ id)) ∘ σ.η (W , ⊤) ∘ ⟨ id , f ∘ g ⟩
    ≈⟨ refl⟩∘⟨ (M.₁-resp-≈ (assoc ○ refl⟩∘⟨ π₁∘⁂ ○ sym-assoc) ⟩∘⟨refl) ⟩
  (f ∘ g) ⋆ (k ∘ g)
    ∎
  where
    σ-nat : σ.η (Z , ⊤) ∘ (g ⁂ id) ≈ M.₁ (g ⁂ id) ∘ σ.η (W , ⊤)
    σ-nat = refl⟩∘⟨ ⁂-cong₂ Equiv.refl (⟺ M.identity) ○ σ.commute (g , id)

⋆-identityˡ : ∀ {Z} (f : ScalarAt Z) → 𝟙 ⋆ f ≈ f
⋆-identityˡ {Z} f = begin
  M.μ ⊤ ∘ M.₁ (f ∘ π₁) ∘ σ.η (Z , ⊤) ∘ ⟨ id , M.η ⊤ ∘ ! ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identity² Equiv.refl) ⟩
  M.μ ⊤ ∘ M.₁ (f ∘ π₁) ∘ σ.η (Z , ⊤) ∘ (id ⁂ M.η ⊤) ∘ ⟨ id , ! ⟩
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (sym-assoc ○ Str.η-comm ⟩∘⟨refl) ⟩
  M.μ ⊤ ∘ M.₁ (f ∘ π₁) ∘ M.η (Z × ⊤) ∘ ⟨ id , ! ⟩
    ≈⟨ refl⟩∘⟨ pullˡ (⟺ (M.η-commute (f ∘ π₁))) ⟩
  M.μ ⊤ ∘ (M.η (M.₀ ⊤) ∘ f ∘ π₁) ∘ ⟨ id , ! ⟩
    ≈⟨ refl⟩∘⟨ assoc ⟩
  M.μ ⊤ ∘ M.η (M.₀ ⊤) ∘ (f ∘ π₁) ∘ ⟨ id , ! ⟩
    ≈⟨ cancelˡ Mon.identityʳ ⟩
  (f ∘ π₁) ∘ ⟨ id , ! ⟩
    ≈⟨ assoc ○ refl⟩∘⟨ π₁-comp ○ identityʳ ⟩
  f
    ∎

⋆-assoc : ∀ {Z} (f g k : ScalarAt Z) → (f ⋆ g) ⋆ k ≈ f ⋆ (g ⋆ k)
⋆-assoc f g k = {!!}

⋆-comm : ∀ {Z} (f g : ScalarAt Z) → f ⋆ g ≈ g ⋆ f
⋆-comm f g = {!!}

-- 1. For every theory `T` that `M` supports, the scalars are a `T`-model: the operations of the kernels `K [ Z , ⊤ ]`.
-- 2. `⋆` is a `T`-homomorphism in each argument (the second, the continuation, by `op-resp-∘`; the first by `⋆-comm`).
-- 3. Independently of `T`, `(⋆, 𝟙)` is a commutative monoid model (the strength and commutativity of `M`).
-- 4. For `T` the commutative monoids these assemble to a model of `CommSemiring`: `⊕`, `𝟘` from 1, `⋆`, `𝟙` from 3,
--    distributivity and annihilation from 2.  (`M` itself is not algebraic for `CommSemiring`: `⋆` is natural in the
--    context but not linear in the continuation.)
module _ {T : Theory} (AL : IsAlgebraic T (CommutativeMonad.M cm)) where
  private module AL = IsAlgebraic AL
  open Theory T

  scalarModel : IsModel T Scalar
  scalarModel = Properties.M-model T (CommutativeMonad.M cm) AL ⊤

  -- `⋆` is linear in its second argument (the continuation): `op-resp-∘` for the operation and for bind.  The first argument
  -- follows by `⋆-comm`.
  ⋆-op
    : ∀ (φ : Op) {Z} (k : ScalarAt Z) (gs : Fin (arity φ) → ScalarAt Z)
    → k ⋆ AL.op φ gs ≈ AL.op φ (λ i → k ⋆ gs i)
  ⋆-op φ {Z} k gs = begin
    M.μ ⊤ ∘ M.₁ (AL.op φ gs ∘ π₁) ∘ κ                    ≈⟨ refl⟩∘⟨ M.₁-resp-≈ (IsModel.op-resp-∘ T scalarModel φ gs π₁) ⟩∘⟨refl ⟩
    M.μ ⊤ ∘ M.₁ (AL.op φ (λ i → gs i ∘ π₁)) ∘ κ           ≈⟨ sym-assoc ⟩
    (M.μ ⊤ ∘ M.₁ (AL.op φ (λ i → gs i ∘ π₁)))∘ κ          ≈⟨ ⟺ K.identityˡ ○ AL.op-resp-∘ φ K.id (λ i → gs i ∘ π₁) κ ○ AL.op-cong φ (λ i → K.identityˡ) ⟩
    AL.op φ (λ i → (M.μ ⊤ ∘ M.₁ (gs i ∘ π₁)) ∘ κ)          ≈⟨ AL.op-cong φ (λ i → assoc) ⟩
    AL.op φ (λ i → k ⋆ gs i)                                ∎
    where κ = σ.η (Z , ⊤) ∘ ⟨ id , k ⟩

scalarCommMonoid : IsAlgebraic CommMonoid (CommutativeMonad.M cm) → IsModel CommMonoid Scalar
scalarCommMonoid = scalarModel

-- `(⋆, 𝟙)`: needs only the strength and commutativity of `M`
private
  mulOperations : Operations CommMonoid Scalar
  mulOperations = record
    { op = mul-op
    ; op-cong = mul-cong
    ; op-resp-∘ = mul-resp-∘
    }
    where
      mul-op : ∀ (φ : CM.CMOp) {Z} → (Fin (CM.cm-arity φ) → ScalarAt Z) → ScalarAt Z
      mul-op CM.unit gs = 𝟙
      mul-op CM.plus gs = gs zero ⋆ gs (suc zero)

      mul-cong : ∀ (φ : CM.CMOp) {Z} {gs hs : Fin (CM.cm-arity φ) → ScalarAt Z}
        → (∀ i → gs i ≈ hs i) → mul-op φ gs ≈ mul-op φ hs
      mul-cong CM.unit eq = Equiv.refl
      mul-cong CM.plus eq = ⋆-cong (eq zero) (eq (suc zero))

      mul-resp-∘ : ∀ (φ : CM.CMOp) {Z W} (gs : Fin (CM.cm-arity φ) → ScalarAt Z) (g : W ⇒ Z)
        → mul-op φ gs ∘ g ≈ mul-op φ (λ i → gs i ∘ g)
      mul-resp-∘ CM.unit gs g = assoc ○ ∘-resp-≈ʳ (⟺ (!-unique (! ∘ g)))
      mul-resp-∘ CM.plus gs g = ⋆-∘ (gs zero) (gs (suc zero)) g

  mul-laws : ∀ (q : CM.CMEqn) {Z} (ρ : Fin (CM.cm-vars q) → ScalarAt Z)
    → Operations.eval CommMonoid mulOperations (CM.cm-lhs q) ρ ≈ Operations.eval CommMonoid mulOperations (CM.cm-rhs q) ρ
  mul-laws CM.assoc ρ = ⋆-assoc (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero)))
  mul-laws CM.comm ρ = ⋆-comm (ρ zero) (ρ (suc zero))
  mul-laws CM.identity ρ = ⋆-identityˡ (ρ zero)

scalarMulMonoid : IsModel CommMonoid Scalar
scalarMulMonoid = record
  { operations = mulOperations
  ; laws = mul-laws
  }

module _ (AL : IsAlgebraic CommMonoid (CommutativeMonad.M cm)) where
  private
    module Add = IsModel CommMonoid (scalarCommMonoid AL)

    pair : ∀ {Z} → ScalarAt Z → ScalarAt Z → Fin 2 → ScalarAt Z
    pair y z zero = y
    pair y z (suc zero) = z

    -- `x ⋆ (y ⊕ z) ≈ x ⋆ y ⊕ x ⋆ z` is `⋆-op` at `plus`, up to the pointwise comparison of the arguments of `⊕`
    ⋆-distrib : ∀ {Z} (x y z : ScalarAt Z) → x ⋆ Add.op CM.plus (pair y z) ≈ Add.op CM.plus (λ i → x ⋆ pair y z i)
    ⋆-distrib x y z = ⋆-op AL CM.plus x (pair y z)

  scalarCommSemiring : IsModel CommSemiring Scalar
  scalarCommSemiring = fromMonoids (scalarCommMonoid AL) scalarMulMonoid
    (λ x y z → ⋆-cong Equiv.refl (Add.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → Equiv.refl })) ○ ⋆-distrib x y z
      ○ Add.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → Equiv.refl }))
    (λ x → ⋆-comm _ x ○ ⋆-cong Equiv.refl (Add.op-cong CM.unit (λ ())) ○ ⋆-op AL CM.unit x (λ ())
      ○ Add.op-cong CM.unit (λ ()))

-- Consequently the semiring of scalars of every context, and (by `Model.Exponential`) of context-dependent weights
-- `A → M ⊤`, are commutative semirings.
