{-# OPTIONS --safe --without-K #-}

-- The category of semirings (standard library `Semiring`) and semiring homomorphisms, up to pointwise equality.
-- Route: homomorphisms, identity and composition are the standard library's (`Algebra.Morphism.Bundles`,
-- `Construct.Identity`, `Construct.Composition`); the category laws hold by the equivalence of the target.
open import Level using (Level; suc; _⊔_)

module Categories.Category.Instance.Semirings (c ℓ : Level) where

open import Algebra.Bundles using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)
import Algebra.Morphism.Construct.Identity as Id
import Algebra.Morphism.Construct.Composition as Comp
open import Relation.Binary using (IsEquivalence)

open import Categories.Category.Core using (Category)

private
  _⇒ˢ_ : Semiring c ℓ → Semiring c ℓ → Set (c ⊔ ℓ)
  R ⇒ˢ S = SemiringHomomorphism (Semiring.rawSemiring R) (Semiring.rawSemiring S)

  _≈ˢ_ : ∀ {R S} → R ⇒ˢ S → R ⇒ˢ S → Set (c ⊔ ℓ)
  _≈ˢ_ {S = S} f g = ∀ x → Semiring._≈_ S (SemiringHomomorphism.⟦ f ⟧ x) (SemiringHomomorphism.⟦ g ⟧ x)

  _∘ˢ_ : ∀ {R S T} → S ⇒ˢ T → R ⇒ˢ S → R ⇒ˢ T
  _∘ˢ_ {T = T} g f = record
    { ⟦_⟧ = λ x → ⟦ g ⟧ (⟦ f ⟧ x)
    ; isSemiringHomomorphism =
        Comp.isSemiringHomomorphism (Semiring.trans T) (isSemiringHomomorphism f) (isSemiringHomomorphism g)
    }
    where open SemiringHomomorphism

  ∘ˢ-resp-≈ : ∀ {R S T} {f h : S ⇒ˢ T} {g i : R ⇒ˢ S} → f ≈ˢ h → g ≈ˢ i → (f ∘ˢ g) ≈ˢ (h ∘ˢ i)
  ∘ˢ-resp-≈ {T = T} {f = f} {i = i} f≈h g≈i x =
    Semiring.trans T (SemiringHomomorphism.⟦⟧-cong f (g≈i x)) (f≈h (SemiringHomomorphism.⟦ i ⟧ x))

Semirings : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Semirings = record
  { Obj       = Semiring c ℓ
  ; _⇒_       = _⇒ˢ_
  ; _≈_       = _≈ˢ_
  ; id        = λ {R} → Id.semiringHomomorphism R
  ; _∘_       = _∘ˢ_
  ; assoc     = λ {_ _ _ D _ _ _} _ → Semiring.refl D
  ; sym-assoc = λ {_ _ _ D _ _ _} _ → Semiring.refl D
  ; identityˡ = λ {_ B _} _ → Semiring.refl B
  ; identityʳ = λ {_ B _} _ → Semiring.refl B
  ; identity² = λ {A} _ → Semiring.refl A
  ; equiv     = λ {_ B} → record
    { refl  = λ _ → Semiring.refl B
    ; sym   = λ eq x → Semiring.sym B (eq x)
    ; trans = λ eq eq′ x → Semiring.trans B (eq x) (eq′ x)
    }
  ; ∘-resp-≈  = ∘ˢ-resp-≈
  }
