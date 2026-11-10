{-# OPTIONS --safe --without-K #-}

-- `IsNormalizedInclusion inc`: a probability monad is the normalized (mass one) part of a measure monad.  For a monad
-- morphism `inc : Prob ⇒ M`, `ι X : Prob X ⇒ M X` is the equalizer, inside `M X`, of the mass `M ! : M X ⇒ M ⊤`
-- (pushforward to the point) and the constant unit measure `η ⊤ ∘ !`.  So `ι` is monic, and every kernel `Z ⇒ M X` of
-- total mass one factors uniquely through `Prob X`.  This says what a probability measure is, without any division and
-- without weights.  Dividing by mass is not part of the interface.
open import Level using (_⊔_)

open import Categories.Category.Core using (Category)
import Categories.Category.CartesianClosed.Canonical as Canonical

module QBS.Monad.Normalized {o h e} {C : Category o h e} where

open import Categories.Morphism C using (Mono)
open import Categories.Diagram.Equalizer C using (IsEqualizer; IsEqualizer⇒Mono)
import Categories.Monad.Notation as Notation
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
import Categories.NaturalTransformation as NT

open import QBS.Monad.Measure using (MeasureMonad)
open import QBS.Monad.Probability using (ProbMonad)

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

record IsNormalizedInclusion
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC}
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; !)
  private
    module M = Notation (MeasureMonad.monad MM)
    module inc = StrongMonad⇒ inc

  -- the component `ι X : Prob X ⇒ M X` of the inclusion: a probability measure on `X`, regarded as a measure
  open NT.NaturalTransformation inc.α public using () renaming (η to ι)

  field
    -- `Prob X` is the measures of mass one: `ι X` equalizes the mass `M !` with the unit measure `η ⊤ ∘ !`
    ι-equalizer : ∀ X → IsEqualizer (ι X) (M.₁ (! {X})) (M.η ⊤ ∘ !)

  -- a probability measure is determined by the measure it gives
  ι-mono : ∀ X → Mono (ι X)
  ι-mono X = IsEqualizer⇒Mono (ι-equalizer X)

