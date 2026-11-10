{-# OPTIONS --safe --without-K #-}

-- Properties of algebraic monads.
--   `M-model X`   the hom-sets `Z ⇒ M X` are a model of `T`: the operations of the kernel sets `K [ Z , X ]`, linear for
--                 a change of context by `op-resp-∘` at `k = id`.  (Not conversely: `IsAlgebraic` also makes bind linear
--                 in the continuation.)
-- Models transfer along right adjoints (`Theory.Equational.Model.Adjoint`), e.g. `X ^ A`.
open import Categories.Category.Core using (Category)
open import Categories.Monad using (Monad)
open import Categories.Monad.Algebraic using (IsAlgebraic)
open import Categories.Theory.Equational using (Theory; Term; var; app)

module Categories.Monad.Algebraic.Properties
  {o h e} {C : Category o h e} (T : Theory) (M : Monad C) (AL : IsAlgebraic T M)
  where

open import Categories.Category.Construction.Kleisli using (Kleisli)
open import Data.Fin.Base using (Fin)
import Categories.Monad.Notation as Notation
import Categories.Theory.Equational.Model C T as Mod

private
  module M = Notation M
  module K = Category (Kleisli M)
  module AL = IsAlgebraic AL
open Category C hiding (op)
open HomReasoning
open Theory T

-- running a kernel after a morphism `g` (as a kernel `η ∘ g`) is the precomposite
pre : ∀ {A B D} (f : B ⇒ M.₀ D) (g : A ⇒ B) → f K.∘ (M.η B ∘ g) ≈ f ∘ g
pre f g = sym-assoc ○ ∘-resp-≈ˡ K.identityʳ

M-operations : ∀ X → Mod.Operations (M.₀ X)
M-operations X = record
  { op = λ φ gs → AL.op φ gs
  ; op-cong = λ φ eq → AL.op-cong φ eq
  ; op-resp-∘ = λ φ gs g →
      ⟺ (pre _ g) ○ ⟺ K.identityˡ ○ AL.op-resp-∘ φ K.id gs (M.η _ ∘ g)
        ○ AL.op-cong φ (λ i → K.identityˡ ○ pre (gs i) g)
  }

-- the two values of a term agree (they differ only in the order of arguments of `op`)
eval-agree : ∀ {n X Z} (t : Tm n) (ρ : Fin n → Z ⇒ M.₀ X)
  → Mod.Operations.eval (M-operations X) t ρ ≈ AL.eval t ρ
eval-agree (var i) ρ = Equiv.refl
eval-agree (app φ ts) ρ = AL.op-cong φ (λ i → eval-agree (ts i) ρ)

M-model : ∀ X → Mod.IsModel (M.₀ X)
M-model X = record
  { operations = M-operations X
  ; laws = λ q ρ → eval-agree (lhs q) ρ ○ AL.laws q ρ ○ ⟺ (eval-agree (rhs q) ρ)
  }
