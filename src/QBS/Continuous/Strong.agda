{-# OPTIONS --safe --without-K #-}

-- Strength and commutativity of the continuous probability monad.  Commutativity is Fubini's
-- theorem: sampling two independent measures in either order gives the same result.
module QBS.Continuous.Strong where

import Level as L
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core using (Category)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; pairQ)
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
open import QBS.Classical using (LEM₀)

module Strength (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) (K : Integration.MeasureClass A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Indicators A lem
  open Tensor A lem
  open UnitInterval A
  open Continuous A lem K
  open QBS
  open Hom
  open Pre
  open Wit

  -- the test function y ↦ f (x , y)
  fixH : ∀ {X Y : QBS S} → ∣ X ∣ → Hom S (_×Q_ S X Y) AQ → Hom S Y AQ
  fixH {X} {Y} = fixL {X} {Y} {AQ}

  -- the left strength on pre-measures
  σPre : ∀ {X Y : QBS S} → ∣ _×Q_ S X (TQ Y) ∣ → Pre (_×Q_ S X Y)
  σPre {X} {Y} (x , q) = mk < constₛ x , α q >ₛ (const-random X x , α-random q) (m q) (ok q)

  ∫-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre Y) (f : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f ≈ ∫ {Y} q (fixH {X} {Y} x f)
  ∫-σ {X} {Y} x q f = I-cong (m q) (λ r → Setoid.refl Aˢ) _ _

  open SetoidReasoning Aˢ

  σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
  σH X Y = record
    { map = record
        { to = σPre {X} {Y}
        ; cong = λ {(x , q)} {(x′ , q′)} (ex , eq) f → begin
            ∫ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f   ≈⟨ ∫-σ {X} {Y} x q f ⟩
            ∫ {Y} q (fixH {X} {Y} x f)                ≈⟨ eq (fixH {X} {Y} x f) ⟩
            ∫ {Y} q′ (fixH {X} {Y} x f)               ≈⟨ I-cong (m q′) (λ r → Func.cong (map f) (ex , Setoid.refl (Carrier Y))) _ _ ⟩
            ∫ {Y} q′ (fixH {X} {Y} x′ f)              ≈˘⟨ ∫-σ {X} {Y} x′ q′ f ⟩
            ∫ {_×Q_ S X Y} (σPre {X} {Y} (x′ , q′)) f ∎
        }
    ; map-random = λ {β} (pb , w) → record
        { a = pairQ S (fstJ {X} (proj₁ₛ ∘ₛ β) pb) (a w)
        ; g = g w
        ; g-ok = g-ok w
        ; g-pr = g-pr w
        ; w-eq = λ r f →
            Setoid.trans Aˢ (∫-σ {X} {Y} (proj₁ (β ⟨$⟩ r)) (proj₂ (β ⟨$⟩ r)) f)
              (Setoid.trans Aˢ (w-eq w r (fixH {X} {Y} (proj₁ (β ⟨$⟩ r)) f))
                (I-cong (g w r) (λ s → Setoid.refl Aˢ) _ _))
        }
    }

  private
    Ir : ∀ (μ : Measure) {h h′ : R → ∣A∣} {fh : Fun h} {fh′ : Fun h′} →
      (∀ r → h r ≈ h′ r) → I μ h fh ≈ I μ h′ fh′
    Ir μ e = I-cong μ e _ _

  open import Categories.Monad.Strong using (Strength; StrongMonad)
  import Categories.Monad.Strong.Properties
  import Categories.Category.Cartesian.Monoidal as CM
  import Categories.Category.CartesianClosed.Canonical as Canonical
  open import QBS.Exponential using (cartesianClosed)

  -- Not `QBS.Category.Cartesian`: using the exported aliases here made `commutative` about 7% slower (45 s
  -- against 42 s) for no reason found, so this module keeps its own (see plans/Simplify.md, Stage 4 follow-up).
  private
    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
    V = CM.CartesianMonoidal.monoidal cartesian

  strength : Strength V TM
  strength = record
    { strengthen = record
        { η = λ { (X , Y) → σH X Y }
        ; commute = λ f {(x , q)} h → Ir (m q) (λ r → Setoid.refl Aˢ)
        ; sym-commute = λ f {(x , q)} h → Ir (m q) (λ r → Setoid.refl Aˢ)
        }
    ; identityˡ = λ {_} {(_ , q)} h → Ir (m q) (λ r → Setoid.refl Aˢ)
    ; η-comm = λ {A} {B} {x} h → Func.cong (map h) (Setoid.refl (Carrier (_×Q_ S A B)))
    ; μ-η-comm = λ {A} {B} {(a , P)} g → begin
        ∫ {_×Q_ S A B} (joinPre (mapPre (σH A B) (σPre {A} {TQ B} (a , P)))) g
          ≈⟨ ∫-join (mapPre (σH A B) (σPre {A} {TQ B} (a , P))) g ⟩
        ∫ {TQ (_×Q_ S A B)} (mapPre (σH A B) (σPre {A} {TQ B} (a , P))) (∫ᶠ g)
          ≈⟨ Ir (m P) (λ r → ∫-σ {A} {B} a (α P ⟨$⟩ r) g) ⟩
        ∫ {TQ B} P (∫ᶠ (fixH {A} {B} a g))
          ≈˘⟨ ∫-join {B} P (fixH {A} {B} a g) ⟩
        ∫ {B} (joinPre P) (fixH {A} {B} a g)
          ≈˘⟨ ∫-σ {A} {B} a (joinPre P) g ⟩
        ∫ {_×Q_ S A B} (σPre {A} {B} (a , joinPre P)) g ∎
    ; strength-assoc = λ {_} {_} {_} {((x , y) , q)} h → Ir (m q) (λ r → Setoid.refl Aˢ)
    }

  strongMonad : StrongMonad V
  strongMonad = record { M = TM ; strength = strength }

  open import Categories.Monad.Commutative using (Commutative)
  import Categories.Category.Cartesian.SymmetricMonoidal as CSM
  open import Categories.Category.Monoidal.Symmetric using (Symmetric)

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
    map-random g {< α s ∘ₛ proj₁ₛ ∘ₛ map fromH , α t ∘ₛ proj₂ₛ ∘ₛ map fromH >ₛ}
      (QBS.pre-random X (α-random s) (proj₁ (Probes.unprobe S fromH)) ,
       QBS.pre-random Y (α-random t) (proj₂ (Probes.unprobe S fromH)))

  hmerge : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) (k r : R) →
    hF s t g (mergeR k r) ≈ proj₁ (map g ⟨$⟩ (α s ⟨$⟩ k , α t ⟨$⟩ r))
  hmerge {X} {Y} s t g k r = Func.cong (map g)
    (Func.cong (α s) (merge-evens k r) , Func.cong (α t) (merge-odds k r))

  private
    module C = Category (QBSCat S)
    module SM = StrongMonad strongMonad

  -- The two sides of `commutes`, restated at the types the goal has (stating them separately keeps
  -- the unifier from comparing the large categorical composites with the `∫-join` instances).
  lhsEq : ∀ {X Y : QBS S} (p : ∣ _×Q_ S (TQ X) (TQ Y) ∣) (g : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (map (SM.M.μ.η (_×Q_ S X Y) C.∘ (SM.M.F.₁ (RS.τ {X} {Y}) C.∘ SP.Left.Shorthands.σ SM.strength)) ⟨$⟩ p) g
    ≈ ∫ {_×Q_ S X Y} (joinPre (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} p))) g
  lhsEq p g = Setoid.refl Aˢ

  rhsEq : ∀ {X Y : QBS S} (p : ∣ _×Q_ S (TQ X) (TQ Y) ∣) (g : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (map (SM.M.μ.η (_×Q_ S X Y) C.∘ (SM.M.F.₁ (σH X Y) C.∘ RS.τ {X} {TQ Y})) ⟨$⟩ p) g
    ≈ ∫ {_×Q_ S X Y} (joinPre (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ p))) g
  rhsEq p g = Setoid.refl Aˢ

  mid : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (joinPre (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t)))) g
    ≈ ∫ {_×Q_ S X Y} (joinPre (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ (s , t)))) g
  mid {X} {Y} s t g = begin
    ∫ {_×Q_ S X Y} (joinPre (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t)))) g
      ≈⟨ ∫-join (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t))) g ⟩
    ∫ {TQ (_×Q_ S X Y)} (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t))) (∫ᶠ g)
      ≈⟨ swap-order ⟩
    ∫ {TQ (_×Q_ S X Y)} (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ (s , t))) (∫ᶠ g)
      ≈˘⟨ ∫-join (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ (s , t))) g ⟩
    ∫ {_×Q_ S X Y} (joinPre (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ (s , t)))) g ∎
    where
    -- Fubini: integrate over t then s, or s then t, after merging the two coordinate streams
    swap-order = Setoid.trans Aˢ (Ir (m t) (λ r → Ir (m s) (λ k → Setoid.sym Aˢ (hmerge s t g k r))))
          (Setoid.trans Aˢ (Setoid.sym Aˢ (fubini (m s) (m t) {hF s t g} (fhF s t g)))
            (Ir (m s) (λ k → Ir (m t) (λ r → hmerge s t g k r))))

  commutative : Commutative braided strongMonad
  commutative = record { commutes = λ {X} {Y} {p} g →
    Setoid.trans Aˢ (lhsEq {X} {Y} p g)
      (Setoid.trans Aˢ (mid {X} {Y} (proj₁ p) (proj₂ p) g) (Setoid.sym Aˢ (rhsEq {X} {Y} p g))) }
