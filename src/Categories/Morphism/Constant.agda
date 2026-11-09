{-# OPTIONS --safe --without-K #-}

-- Constant morphisms: `c : A ⇒ B` is constant when `c ∘ f ≈ c ∘ g` for all `f g : Z ⇒ A`.
--   * `IsConstant c`, with `IsConstant-∘ˡ` (precomposition) and `IsConstant-∘ʳ` (postcomposition);
--   * with a terminal object, `const x = x ∘ !` for a point `x : ⊤ ⇒ B`, `IsConstant (const x)`, and the converse for
--     `A` with a point: a constant `c` is `const (c ∘ a)` for any `a : ⊤ ⇒ A`.
-- Route: `IsConstant-∘ˡ` and `IsConstant-∘ʳ` are `assoc` and the constant's own law; `const-isConstant` and
-- `isConstant⇒const` use `!-unique₂` (any two maps into `⊤` agree).
open import Categories.Category.Core using (Category)

module Categories.Morphism.Constant {o h e} (C : Category o h e) where

open import Level using (_⊔_)

open import Categories.Object.Terminal C using (Terminal)

open Category C
open HomReasoning

IsConstant : ∀ {A B} → A ⇒ B → Set (o ⊔ h ⊔ e)
IsConstant {A} c = ∀ {Z} (f g : Z ⇒ A) → c ∘ f ≈ c ∘ g

-- a constant stays constant after precomposition and after postcomposition
IsConstant-∘ˡ : ∀ {A B Z} {c : B ⇒ Z} {f : A ⇒ B} → IsConstant c → IsConstant (c ∘ f)
IsConstant-∘ˡ {c = c} {f} k g₁ g₂ = begin
  (c ∘ f) ∘ g₁ ≈⟨ assoc ⟩
  c ∘ f ∘ g₁   ≈⟨ k (f ∘ g₁) (f ∘ g₂) ⟩
  c ∘ f ∘ g₂   ≈˘⟨ assoc ⟩
  (c ∘ f) ∘ g₂ ∎

IsConstant-∘ʳ : ∀ {A B Z} {c : A ⇒ B} {g : B ⇒ Z} → IsConstant c → IsConstant (g ∘ c)
IsConstant-∘ʳ {c = c} {g} k f₁ f₂ = begin
  (g ∘ c) ∘ f₁ ≈⟨ assoc ⟩
  g ∘ c ∘ f₁   ≈⟨ refl⟩∘⟨ k f₁ f₂ ⟩
  g ∘ c ∘ f₂   ≈˘⟨ assoc ⟩
  (g ∘ c) ∘ f₂ ∎

module WithTerminal (T : Terminal) where
  open Terminal T using (⊤; !; !-unique₂)

  -- the constant morphism at a point
  const : ∀ {A B} → ⊤ ⇒ B → A ⇒ B
  const x = x ∘ !

  const-isConstant : ∀ {A B} (x : ⊤ ⇒ B) → IsConstant (const {A} x)
  const-isConstant x f g = begin
    (x ∘ !) ∘ f ≈⟨ assoc ⟩
    x ∘ ! ∘ f   ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
    x ∘ ! ∘ g   ≈˘⟨ assoc ⟩
    (x ∘ !) ∘ g ∎

  -- a constant morphism out of an object with a point is the constant at its value there
  isConstant⇒const : ∀ {A B} {c : A ⇒ B} → IsConstant c → (a : ⊤ ⇒ A) → c ≈ const (c ∘ a)
  isConstant⇒const {c = c} k a = begin
    c               ≈˘⟨ identityʳ ⟩
    c ∘ id          ≈⟨ k id (a ∘ !) ⟩
    c ∘ a ∘ !       ≈˘⟨ assoc ⟩
    (c ∘ a) ∘ !     ∎
