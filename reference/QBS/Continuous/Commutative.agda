{-# OPTIONS --safe --without-K #-}

-- Commutativity of the continuous probability monad, which is Fubini's theorem: sampling two independent
-- measures in either order gives the same result.  Split from `Continuous/Strong` to keep each module's check time low.
--   * `commutative`: the strong monad of `Continuous/Strong` is commutative.
-- Route: `swapEq` merges the two coordinate streams into one (`hmerge`) and swaps the integrals with `fubini`.
module QBS.Continuous.Commutative where

import Level as L
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core using (Category)
open import Categories.Monad.Strong using (StrongMonad)
import Categories.Monad.Strong.Properties
open import Categories.Monad.Commutative using (Commutative)
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Cartesian.Monoidal as CM
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.Category.Monoidal.Core using (Monoidal)
import Categories.Category.CartesianClosed.Canonical as Canonical
open import QBS.Exponential using (cartesianClosed)

open import Function.Base using (_$_)
open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; pairQ; rand-fst; rand-snd; rand-pair)
import QBS.Probes as Probes
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators
open import QBS.Analysis.Param
open import QBS.Analysis.Tensor
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Classical using (LEM₀)

module Commutativity (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) (K : Integration.MeasureClass A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Indicators A lem
  open Tensor A lem
  open UnitInterval A
  open Continuous A lem K
  open Strength A lem K
  open QBS
  open Hom
  open Wit
  open SetoidReasoning Aˢ

  private
    Ir : ∀ (μ : Measure) {h h′ : R → ∣A∣} {fh : Fun h} {fh′ : Fun h′} →
      (∀ r → h r ≈ h′ r) → I μ h fh ≈ I μ h′ fh′
    Ir μ e = I-cong μ e _ _

    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)


  private
    braided = Symmetric.braided (CSM.symmetric (QBSCat S) cartesian)

  private
    module SP = Categories.Monad.Strong.Properties
    module RS = SP.Right.Shorthands (SP.Strength⇒RightStrength braided (StrongMonad.strength strongMonad))

  -- the joint test function u ↦ g (s (evens u), t (odds u))
  hF : ∀ {X Y : QBS S} → Pre X → Pre Y → Hom S (_×Q_ S X Y) AQ → R → ∣A∣
  hF s t g u = proj₁ (map g ⟨$⟩ (α s ⟨$⟩ evensR u , α t ⟨$⟩ oddsR u))

  fhF : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) → Fun (hF s t g)
  fhF {X} {Y} s t g =
    rand-Fun $ map-random g {< α s ∘ₛ proj₁ₛ ∘ₛ map fromH , α t ∘ₛ proj₂ₛ ∘ₛ map fromH >ₛ}
      (rand-pair S {X} {Y} {< α s ∘ₛ proj₁ₛ ∘ₛ map fromH , α t ∘ₛ proj₂ₛ ∘ₛ map fromH >ₛ}
        (QBS.pre-random X (α-random s) (rand-fst S {Probes.ℛQ S} {Probes.ℛQ S} {map fromH} (Probes.unprobe S fromH)))
        (QBS.pre-random Y (α-random t) (rand-snd S {Probes.ℛQ S} {Probes.ℛQ S} {map fromH} (Probes.unprobe S fromH))))

  hmerge : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (k r : R) →
    hF s t g (mergeR k r) ≈ proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r))
  hmerge {X} {Y} s t g k r = Func.cong (map g)
    (Func.cong (α s) (merge-evens k r) , Func.cong (α t) (merge-odds k r))

  private
    module C = Category (QBSCat S)
    module SM = StrongMonad strongMonad
    module V = Monoidal (CM.CartesianMonoidal.monoidal cartesian)
    module Br = Braided braided

  -- the inverse braiding `Z ⊗ X ⇒ X ⊗ Z`, which `RS.τ` is built from
  B⇐ : ∀ (X Z : QBS S) → Hom S (Z V.⊗₀ X) (X V.⊗₀ Z)
  B⇐ X Z = NaturalTransformation.η (NaturalIsomorphism.F⇐G Br.braiding) (X , Z)

  -- the right strength on a pair, from `σ-red` (`strength` is abstract, so this is the only way to see into `RS.τ`)
  τ-red : ∀ {X Z : QBS S} (p : ∣ TQ X V.⊗₀ Z ∣) (h : Hom S (X V.⊗₀ Z) AQ) →
    ∫ {X V.⊗₀ Z} (map (RS.τ {X} {Z}) ⟨$⟩ p) h
    ≈ ∫ {X V.⊗₀ Z} (map (SM.M.F.₁ (B⇐ X Z)) ⟨$⟩ σPre {Z} {X} (proj₂ p , proj₁ p)) h
  τ-red {X} {Z} p h = Func.cong (map (SM.M.F.₁ (B⇐ X Z))) (λ k → σ-red {Z} {X} (proj₂ p , proj₁ p) k) h

  -- `∫-join` on both sides, at variables: the two large pre-measures are never unfolded here
  joinEq : ∀ {Z : QBS S} (P Q : Pre (TQ Z)) (g : Hom S Z AQ) →
    ∫ {TQ Z} P (∫ᶠ {Z} g) ≈ ∫ {TQ Z} Q (∫ᶠ {Z} g) → ∫ {Z} (joinPre P) g ≈ ∫ {Z} (joinPre Q) g
  joinEq {Z} P Q g e = begin
    ∫ {Z} (joinPre P) g      ≈⟨ ∫-join {Z} P g ⟩
    ∫ {TQ Z} P (∫ᶠ {Z} g)    ≈⟨ e ⟩
    ∫ {TQ Z} Q (∫ᶠ {Z} g)    ≈˘⟨ ∫-join {Z} Q g ⟩
    ∫ {Z} (joinPre Q) g      ∎

  -- `Pre`-level congruences, so that the equations below never compare the large categorical composites
  mapCong : ∀ {X Y : QBS S} (h : Hom S X Y) {P Q : Pre X} → (∀ k → ∫ {X} P k ≈ ∫ {X} Q k) →
    ∀ k → ∫ {Y} (mapPre h P) k ≈ ∫ {Y} (mapPre h Q) k
  mapCong {X} {Y} h {P} {Q} e k = begin
    ∫ {Y} (mapPre h P) k  ≈⟨ ∫-map h P k ⟩
    ∫ {X} P (_∘H_ S k h)  ≈⟨ e (_∘H_ S k h) ⟩
    ∫ {X} Q (_∘H_ S k h)  ≈˘⟨ ∫-map h Q k ⟩
    ∫ {Y} (mapPre h Q) k  ∎

  -- application of composites and of the functor/monad structure, at variables (so no unfolding is needed)
  ∘-app : ∀ {A B D : QBS S} (f : Hom S B D) (g : Hom S A B) (x : ∣ A ∣) →
    Setoid._≈_ (Carrier D) (map (f C.∘ g) ⟨$⟩ x) (map f ⟨$⟩ (map g ⟨$⟩ x))
  ∘-app {D = D} f g x = Setoid.refl (Carrier D)

  F-app : ∀ {A B : QBS S} (h : Hom S A B) (P : ∣ TQ A ∣) →
    Setoid._≈_ (Carrier (TQ B)) (map (SM.M.F.₁ h) ⟨$⟩ P) (mapPre h P)
  F-app {B = B} h P = Setoid.refl (Carrier (TQ B))

  μ-app : ∀ {Z : QBS S} (P : ∣ TQ (TQ Z) ∣) →
    Setoid._≈_ (Carrier (TQ Z)) (map (SM.M.μ.η Z) ⟨$⟩ P) (joinPre P)
  μ-app {Z} P = Setoid.refl (Carrier (TQ Z))

  -- The two sides of `commutes`, restated at the types the goal has (stating them separately keeps
  -- the unifier from comparing the large categorical composites with the `∫-join` instances).
  lhsEq : ∀ {X Y : QBS S} (p : ∣ TQ X V.⊗₀ TQ Y ∣) (g : Hom S (X V.⊗₀ Y) AQ) →
    ∫ {X V.⊗₀ Y} (map ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (RS.τ {X} {Y})) C.∘ SP.Left.Shorthands.σ SM.strength) ⟨$⟩ p) g
    ≈ ∫ {X V.⊗₀ Y} (joinPre (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} p))) g
  lhsEq {X} {Y} p g =
    Setoid.trans Aˢ (∘-app (SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (RS.τ {X} {Y})) (SP.Left.Shorthands.σ SM.strength) p g)
      (Setoid.trans Aˢ (∘-app (SM.M.μ.η (X V.⊗₀ Y)) (SM.M.F.₁ (RS.τ {X} {Y})) _ g)
        (Setoid.trans Aˢ (μ-app _ g)
          (joinEq {X V.⊗₀ Y} _ _ g
            (Setoid.trans Aˢ (F-app (RS.τ {X} {Y}) _ (∫ᶠ {X V.⊗₀ Y} g))
              (mapCong (RS.τ {X} {Y}) (λ k → σ-red {TQ X} {Y} p k) (∫ᶠ {X V.⊗₀ Y} g))))))

  rhsEq : ∀ {X Y : QBS S} (p : ∣ TQ X V.⊗₀ TQ Y ∣) (g : Hom S (X V.⊗₀ Y) AQ) →
    ∫ {X V.⊗₀ Y} (map ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) C.∘ RS.τ {X} {TQ Y}) ⟨$⟩ p) g
    ≈ ∫ {X V.⊗₀ Y} (joinPre (mapPre (σH X Y) (mapPre (B⇐ X (TQ Y)) (σPre {TQ Y} {X} (proj₂ p , proj₁ p))))) g
  rhsEq {X} {Y} p g =
    Setoid.trans Aˢ (∘-app (SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) (RS.τ {X} {TQ Y}) p g)
      (Setoid.trans Aˢ (∘-app (SM.M.μ.η (X V.⊗₀ Y)) (SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) _ g)
        (Setoid.trans Aˢ (μ-app _ g)
          (joinEq {X V.⊗₀ Y} _ _ g
            (Setoid.trans Aˢ
              (SM.M.F.F-resp-≈ {f = SP.Left.Shorthands.σ SM.strength} {g = σH X Y} (λ {q} h → σ-red q h) (∫ᶠ {X V.⊗₀ Y} g))
              (Setoid.trans Aˢ (F-app (σH X Y) _ (∫ᶠ {X V.⊗₀ Y} g))
                (mapCong (σH X Y)
                  (λ k → Setoid.trans Aˢ (τ-red {X} {TQ Y} p k) (F-app (B⇐ X (TQ Y)) _ k)) (∫ᶠ {X V.⊗₀ Y} g)))))))

  -- Kock's double strength `ψ = μ ∘ F₁ σ ∘ τ` (right-associated, as in `DoubleStrength`) on a pair, as a `joinPre` of pre-measures
  ψ-join : ∀ {X Y : QBS S} (p : ∣ TQ X V.⊗₀ TQ Y ∣) (g : Hom S (X V.⊗₀ Y) AQ) →
    ∫ {X V.⊗₀ Y} (map (SM.M.μ.η (X V.⊗₀ Y) C.∘ (SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength) C.∘ RS.τ {X} {TQ Y})) ⟨$⟩ p) g
    ≈ ∫ {X V.⊗₀ Y} (joinPre (mapPre (σH X Y) (mapPre (B⇐ X (TQ Y)) (σPre {TQ Y} {X} (proj₂ p , proj₁ p))))) g
  ψ-join {X} {Y} p g =
    Setoid.trans Aˢ (∘-app (SM.M.μ.η (X V.⊗₀ Y)) (SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength) C.∘ RS.τ {X} {TQ Y}) p g)
      (Setoid.trans Aˢ (μ-app _ g)
        (joinEq {X V.⊗₀ Y} _ _ g
          (Setoid.trans Aˢ (∘-app (SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) (RS.τ {X} {TQ Y}) p (∫ᶠ {X V.⊗₀ Y} g))
            (Setoid.trans Aˢ
              (SM.M.F.F-resp-≈ {f = SP.Left.Shorthands.σ SM.strength} {g = σH X Y} (λ {q} h → σ-red q h) (∫ᶠ {X V.⊗₀ Y} g))
              (Setoid.trans Aˢ (F-app (σH X Y) _ (∫ᶠ {X V.⊗₀ Y} g))
                (mapCong (σH X Y)
                  (λ k → Setoid.trans Aˢ (τ-red {X} {TQ Y} p k) (F-app (B⇐ X (TQ Y)) _ k)) (∫ᶠ {X V.⊗₀ Y} g)))))))

  -- the test functions of the inner integrals (one coordinate frozen)
  fhL : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (r : R) →
    Fun (λ k → proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r)))
  fhL {X} {Y} s t g r = rand-Fun $ map-random g {< α s , constₛ (α t ⟨$⟩ r) >ₛ}
    (rand-pair S {X} {Y} {< α s , constₛ (α t ⟨$⟩ r) >ₛ} (α-random s) (QBS.const-random Y (α t ⟨$⟩ r)))

  fhR : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (k : R) →
    Fun (λ r → proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r)))
  fhR {X} {Y} s t g k = rand-Fun $ map-random g {< constₛ (α s ⟨$⟩ k) , α t >ₛ}
    (rand-pair S {X} {Y} {< constₛ (α s ⟨$⟩ k) , α t >ₛ} (QBS.const-random X (α s ⟨$⟩ k)) (α-random t))

  -- the inner integrals of the two iterated integrals, unfolded to `I`
  lhsInner : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (r : R) →
    ∫ {_×Q_ S X Y} (map (RS.τ {X} {Y}) ⟨$⟩ (s , α t ⟨$⟩ r)) g ≈ I (m s) (λ k → proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r))) (fhL s t g r)
  lhsInner {X} {Y} s t g r = Setoid.trans Aˢ (τ-red {X} {Y} (s , α t ⟨$⟩ r) g)
    (Setoid.trans Aˢ (∫-unfold {_×Q_ S X Y} _ g) (Ir (m s) (λ k → Setoid.refl Aˢ)))

  rhsInner : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (k : R) →
    ∫ {_×Q_ S X Y} (σPre {X} {Y} (α s ⟨$⟩ k , t)) g ≈ I (m t) (λ r → proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r))) (fhR s t g k)
  rhsInner {X} {Y} s t g k = Setoid.trans Aˢ (∫-σ {X} {Y} (α s ⟨$⟩ k) t g) (Setoid.trans Aˢ (∫-unfold {Y} t _) (Ir (m t) (λ r → Setoid.refl Aˢ)))

  -- Fubini on the two pre-measures: integrate over t then s, or s then t, after merging the coordinate streams
  abstract
    swapEq : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) →
      ∫ {TQ (_×Q_ S X Y)} (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t))) (∫ᶠ {_×Q_ S X Y} g)
      ≈ ∫ {TQ (_×Q_ S X Y)} (mapPre (σH X Y) (mapPre (B⇐ X (TQ Y)) (σPre {TQ Y} {X} (t , s)))) (∫ᶠ {_×Q_ S X Y} g)
    swapEq {X} {Y} s t g = via {TQ (_×Q_ S X Y)} {TQ (_×Q_ S X Y)} (
      Setoid.trans Aˢ
        (Ir (m t) (λ r → Setoid.trans Aˢ (lhsInner s t g r) (Ir (m s) (λ k → Setoid.sym Aˢ (hmerge s t g k r)))))
        (Setoid.trans Aˢ (Setoid.sym Aˢ (fubini (m s) (m t) {hF s t g} (fhF s t g)))
          (Ir (m s) (λ k → Setoid.trans Aˢ (Ir (m t) (λ r → hmerge s t g k r)) (Setoid.sym Aˢ (rhsInner s t g k))))))

  mid : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (joinPre (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t)))) g
    ≈ ∫ {_×Q_ S X Y} (joinPre (mapPre (σH X Y) (mapPre (B⇐ X (TQ Y)) (σPre {TQ Y} {X} (t , s))))) g
  mid {X} {Y} s t g = joinEq {_×Q_ S X Y} _ _ g (swapEq {X} {Y} s t g)

  -- stated at the types of the record field (`V.⊗₀ X Y` for `X ×Q Y`), so that the field is a plain application
  commutes′ : ∀ {X Y : QBS S} (p : ∣ TQ X V.⊗₀ TQ Y ∣) (g : Hom S (X V.⊗₀ Y) AQ) →
    ∫ {X V.⊗₀ Y} (map ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (RS.τ {X} {Y})) C.∘ SP.Left.Shorthands.σ SM.strength) ⟨$⟩ p) g
    ≈ ∫ {X V.⊗₀ Y} (map ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) C.∘ RS.τ {X} {TQ Y}) ⟨$⟩ p) g
  commutes′ {X} {Y} p g = Setoid.trans Aˢ (lhsEq {X} {Y} p g)
    (Setoid.trans Aˢ (mid {X} {Y} (proj₁ p) (proj₂ p) g) (Setoid.sym Aˢ (rhsEq {X} {Y} p g)))

  -- the field of `Commutative`, stated with the category's own equality of homs
  commutesH : ∀ {X Y : QBS S} →
    ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (RS.τ {X} {Y})) C.∘ SP.Left.Shorthands.σ SM.strength) C.≈
    ((SM.M.μ.η (X V.⊗₀ Y) C.∘ SM.M.F.₁ (SP.Left.Shorthands.σ SM.strength)) C.∘ RS.τ {X} {TQ Y})
  commutesH {X} {Y} {p} g = commutes′ {X} {Y} p g

  commutative : Commutative braided strongMonad
  commutative = record { commutes = commutesH }
