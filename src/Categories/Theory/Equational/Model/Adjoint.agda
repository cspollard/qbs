{-# OPTIONS --safe --without-K #-}

-- Models transfer along a right adjoint: for `L ⊣ R`, a model `X` of `T` in `D` gives the model `R X` in `C`, with the
-- operations of `Z ⇒ R X ≅ L Z ⇒ X`.
open import Categories.Category.Core using (Category)
open import Categories.Functor using (Functor)
open import Categories.Adjoint using (Adjoint; _⊣_)
open import Categories.Theory.Equational using (Theory)

module Categories.Theory.Equational.Model.Adjoint
  {o h e o′ h′ e′} {C : Category o h e} {D : Category o′ h′ e′} (T : Theory)
  {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R)
  where

open import Data.Fin.Base using (Fin)

import Categories.Theory.Equational.Model C T as MC
import Categories.Theory.Equational.Model D T as MD
open import Categories.Theory.Equational using (var; app)

private
  module C = Category C
  module D = Category D
  module L = Functor L
  module R = Functor R
open Theory T
open Adjoint L⊣R using (Ladjunct; Radjunct; Ladjunct-comm′; Ladjunct-resp-≈; Radjunct-resp-≈; LRadjunct≈id; RLadjunct≈id; module counit)

module _ {X : D.Obj} (m : MD.IsModel X) where
  private module m = MD.IsModel m
  open C.HomReasoning
  open D.HomReasoning using () renaming (_○_ to _○ᴰ_; ⟺ to ⟺ᴰ)

  -- `Radjunct` commutes with a change of context
  Radjunct-∘ : ∀ {Z W} (f : Z C.⇒ R.₀ X) (g : W C.⇒ Z) → Radjunct (f C.∘ g) D.≈ Radjunct f D.∘ L.₁ g
  Radjunct-∘ f g = D.∘-resp-≈ʳ L.homomorphism ○ᴰ D.sym-assoc

  transferOps : MC.Operations (R.₀ X)
  transferOps = record
    { op = λ φ gs → Ladjunct (m.op φ (λ i → Radjunct (gs i)))
    ; op-cong = λ φ eq → Ladjunct-resp-≈ (m.op-cong φ (λ i → Radjunct-resp-≈ (eq i)))
    ; op-resp-∘ = λ φ gs g →
        ⟺ Ladjunct-comm′ ○ Ladjunct-resp-≈ (m.op-resp-∘ φ _ (L.₁ g) ○ᴰ m.op-cong φ (λ i → ⟺ᴰ (Radjunct-∘ (gs i) g)))
    }

  private module t = MC.Operations transferOps

  -- the value of a term in the transferred model is the transpose of its value in `X`
  eval-transfer : ∀ {n Z} (tm : Tm n) (ρ : Fin n → Z C.⇒ R.₀ X)
    → t.eval tm ρ C.≈ Ladjunct (m.eval tm (λ i → Radjunct (ρ i)))
  eval-transfer (var i) ρ = ⟺ LRadjunct≈id
  eval-transfer (app φ ts) ρ =
    Ladjunct-resp-≈ (m.op-cong φ (λ i → Radjunct-resp-≈ (eval-transfer (ts i) ρ) ○ᴰ RLadjunct≈id))

  transfer : MC.IsModel (R.₀ X)
  transfer = record
    { operations = transferOps
    ; laws = λ q ρ → eval-transfer (lhs q) ρ ○ Ladjunct-resp-≈ (m.laws q _) ○ ⟺ (eval-transfer (rhs q) ρ)
    }
