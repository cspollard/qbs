{-# OPTIONS --safe --without-K #-}

-- A model of `CommSemiring` from two models of `CommMonoid` on the same object, an additive and a multiplicative one,
-- together with distributivity and annihilation (the only equations that mix the two).
open import Categories.Category.Core using (Category)

module Categories.Theory.Equational.Model.CommutativeSemiring {o h e} (C : Category o h e) where

open import Data.Fin.Base using (Fin; zero; suc)

open import Categories.Theory.Equational using (Term; var; app)
import Categories.Theory.Equational.CommutativeMonoid as CM
import Categories.Theory.Equational.CommutativeSemiring as CS
open import Categories.Theory.Equational.Model C

open Category C hiding (op)
open HomReasoning

module _ {X : Obj} (A M : IsModel CM.CommMonoid X) where
  private
    module A = IsModel CM.CommMonoid A
    module M = IsModel CM.CommMonoid M

  -- binary sum and product, and zero, of kernels into `X`
  private
    _⊕_ _⊗_ : ∀ {Z} → Z ⇒ X → Z ⇒ X → Z ⇒ X
    x ⊕ y = A.op CM.plus λ { zero → x ; (suc zero) → y }
    x ⊗ y = M.op CM.plus λ { zero → x ; (suc zero) → y }

    𝟘 : ∀ {Z} → Z ⇒ X
    𝟘 = A.op CM.unit λ ()

    operations : Operations CS.CommSemiring X
    operations = record
      { op = op′
      ; op-cong = cong′
      ; op-resp-∘ = resp-∘′
      }
      where
        op′ : ∀ (φ : CS.CSOp) {Z} → (Fin (CS.cs-arity φ) → Z ⇒ X) → Z ⇒ X
        op′ CS.zro gs = A.op CM.unit gs
        op′ CS.one gs = M.op CM.unit gs
        op′ CS.add gs = A.op CM.plus gs
        op′ CS.mul gs = M.op CM.plus gs

        cong′ : ∀ (φ : CS.CSOp) {Z} {gs hs : Fin (CS.cs-arity φ) → Z ⇒ X}
          → (∀ i → gs i ≈ hs i) → op′ φ gs ≈ op′ φ hs
        cong′ CS.zro eq = A.op-cong CM.unit eq
        cong′ CS.one eq = M.op-cong CM.unit eq
        cong′ CS.add eq = A.op-cong CM.plus eq
        cong′ CS.mul eq = M.op-cong CM.plus eq

        resp-∘′ : ∀ (φ : CS.CSOp) {Z W} (gs : Fin (CS.cs-arity φ) → Z ⇒ X) (g : W ⇒ Z)
          → op′ φ gs ∘ g ≈ op′ φ (λ i → gs i ∘ g)
        resp-∘′ CS.zro gs g = A.op-resp-∘ CM.unit gs g
        resp-∘′ CS.one gs g = M.op-resp-∘ CM.unit gs g
        resp-∘′ CS.add gs g = A.op-resp-∘ CM.plus gs g
        resp-∘′ CS.mul gs g = M.op-resp-∘ CM.plus gs g

    -- evaluating the translation of a `CommMonoid` term is evaluating the term in the corresponding model
    eval-add : ∀ {n Z} (t : Term CM.CMOp CM.cm-arity n) (ρ : Fin n → Z ⇒ X)
      → Operations.eval CS.CommSemiring operations (CS.add-embed t) ρ ≈ A.eval t ρ
    eval-add (var i) ρ = Equiv.refl
    eval-add (app CM.unit ts) ρ = A.op-cong CM.unit (λ i → eval-add (ts i) ρ)
    eval-add (app CM.plus ts) ρ = A.op-cong CM.plus (λ i → eval-add (ts i) ρ)

    eval-mul : ∀ {n Z} (t : Term CM.CMOp CM.cm-arity n) (ρ : Fin n → Z ⇒ X)
      → Operations.eval CS.CommSemiring operations (CS.mul-embed t) ρ ≈ M.eval t ρ
    eval-mul (var i) ρ = Equiv.refl
    eval-mul (app CM.unit ts) ρ = M.op-cong CM.unit (λ i → eval-mul (ts i) ρ)
    eval-mul (app CM.plus ts) ρ = M.op-cong CM.plus (λ i → eval-mul (ts i) ρ)

  module _
    (distrib : ∀ {Z} (x y z : Z ⇒ X) → x ⊗ (y ⊕ z) ≈ (x ⊗ y) ⊕ (x ⊗ z))
    (annihilate : ∀ {Z} (x : Z ⇒ X) → 𝟘 ⊗ x ≈ 𝟘)
    where

    private
      laws′ : ∀ (q : CS.CSEqn) {Z} (ρ : Fin (CS.cs-vars q) → Z ⇒ X)
        → Operations.eval CS.CommSemiring operations (CS.cs-lhs q) ρ
        ≈ Operations.eval CS.CommSemiring operations (CS.cs-rhs q) ρ
      laws′ CS.add-assoc ρ = eval-add (CM.cm-lhs CM.assoc) ρ ○ A.laws CM.assoc ρ ○ ⟺ (eval-add (CM.cm-rhs CM.assoc) ρ)
      laws′ CS.add-comm ρ = eval-add (CM.cm-lhs CM.comm) ρ ○ A.laws CM.comm ρ ○ ⟺ (eval-add (CM.cm-rhs CM.comm) ρ)
      laws′ CS.add-identity ρ = eval-add (CM.cm-lhs CM.identity) ρ ○ A.laws CM.identity ρ ○ ⟺ (eval-add (CM.cm-rhs CM.identity) ρ)
      laws′ CS.mul-assoc ρ = eval-mul (CM.cm-lhs CM.assoc) ρ ○ M.laws CM.assoc ρ ○ ⟺ (eval-mul (CM.cm-rhs CM.assoc) ρ)
      laws′ CS.mul-comm ρ = eval-mul (CM.cm-lhs CM.comm) ρ ○ M.laws CM.comm ρ ○ ⟺ (eval-mul (CM.cm-rhs CM.comm) ρ)
      laws′ CS.mul-identity ρ = eval-mul (CM.cm-lhs CM.identity) ρ ○ M.laws CM.identity ρ ○ ⟺ (eval-mul (CM.cm-rhs CM.identity) ρ)
      -- the two sides are the hypotheses up to a pointwise comparison of the arguments of `op`
      laws′ CS.distrib ρ =
        M.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → A.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → Equiv.refl }) })
        ○ distrib (ρ zero) (ρ (suc zero)) (ρ (suc (suc zero)))
        ○ A.op-cong CM.plus (λ { zero → M.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → Equiv.refl })
                               ; (suc zero) → M.op-cong CM.plus (λ { zero → Equiv.refl ; (suc zero) → Equiv.refl }) })
      laws′ CS.annihilate ρ =
        M.op-cong CM.plus (λ { zero → A.op-cong CM.unit (λ ()) ; (suc zero) → Equiv.refl })
        ○ annihilate (ρ zero)
        ○ A.op-cong CM.unit (λ ())

    fromMonoids : IsModel CS.CommSemiring X
    fromMonoids = record
      { operations = operations
      ; laws = laws′
      }
