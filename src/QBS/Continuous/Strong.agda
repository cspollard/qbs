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
  open Wit

  -- the test function y ↦ f (x , y)
  fixH : ∀ {X Y : QBS S} → ∣ X ∣ → Hom S (_×Q_ S X Y) AQ → Hom S Y AQ
  fixH {X} {Y} = fixL {X} {Y} {AQ}

  -- the left strength on pre-measures
  σPre : ∀ {X Y : QBS S} → ∣ _×Q_ S X (TQ Y) ∣ → Pre (_×Q_ S X Y)
  σPre {X} {Y} (x , q) = mk < constₛ x , α q >ₛ
    (rand-pair S {X} {Y} {< constₛ x , α q >ₛ} (QBS.const-random X x) (α-random q)) (m q) (ok q)

  ∫-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre Y) (f : Hom S (_×Q_ S X Y) AQ) →
    ∫ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f ≈ ∫ {Y} q (fixH {X} {Y} x f)
  ∫-σ {X} {Y} x q f = via {_×Q_ S X Y} {Y} {σPre {X} {Y} (x , q)} {q} (I-cong (m q) (λ r → Setoid.refl Aˢ) _ _)

  open SetoidReasoning Aˢ

  σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
  σH X Y = record
    { map = record
        { to = σPre {X} {Y}
        ; cong = λ {(x , q)} {(x′ , q′)} (ex , eq) f → begin
            ∫ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f   ≈⟨ ∫-σ {X} {Y} x q f ⟩
            ∫ {Y} q (fixH {X} {Y} x f)                ≈⟨ eq (fixH {X} {Y} x f) ⟩
            ∫ {Y} q′ (fixH {X} {Y} x f)               ≈⟨ via {Y} {Y} {q′} {q′} (I-cong (m q′) (λ r → Func.cong (map f) (ex , Setoid.refl (Carrier Y))) _ _) ⟩
            ∫ {Y} q′ (fixH {X} {Y} x′ f)              ≈˘⟨ ∫-σ {X} {Y} x′ q′ f ⟩
            ∫ {_×Q_ S X Y} (σPre {X} {Y} (x′ , q′)) f ∎
        }
    ; map-random = λ {β} m →
        let pb = rand-fst S {X} {TQ Y} {β} m
            w = witOf (rand-snd S {X} {TQ Y} {β} m) in
        rwit record
          { a = pairQ S (fstJ {X} (proj₁ₛ ∘ₛ β) pb) (a w)
          ; g = g w
          ; g-ok = g-ok w
          ; g-pr = g-pr w
          ; w-eq = λ r f →
              Setoid.trans Aˢ (∫-σ {X} {Y} (proj₁ (β ⟨$⟩ r)) (proj₂ (β ⟨$⟩ r)) f)
                (Setoid.trans Aˢ (w-eq w r (fixH {X} {Y} (proj₁ (β ⟨$⟩ r)) f))
                  (via {Y} {_×Q_ S X Y} (I-cong (g w r) (λ s → Setoid.refl Aˢ) _ _)))
          }
    }

  private
    Ir : ∀ (μ : Measure) {h h′ : R → ∣A∣} {fh : Fun h} {fh′ : Fun h′} →
      (∀ r → h r ≈ h′ r) → I μ h fh ≈ I μ h′ fh′
    Ir μ e = I-cong μ e _ _

  open import Categories.Monad.Strong using (Strength; StrongMonad)
  open import Categories.NaturalTransformation.Core using (NaturalTransformation)
  import Categories.Monad.Strong.Properties
  import Categories.Category.Cartesian.Monoidal as CM
  import Categories.Category.CartesianClosed.Canonical as Canonical
  open import QBS.Exponential using (cartesianClosed)

  -- strength commutes with join, stated on pre-measures only (the record then only converts to this type)
  abstract
    muEta : ∀ {A B : QBS S} (a : ∣ A ∣) (P : Pre (TQ B)) (g : Hom S (_×Q_ S A B) AQ) →
      ∫ {_×Q_ S A B} (joinPre (mapPre (σH A B) (σPre {A} {TQ B} (a , P)))) g
      ≈ ∫ {_×Q_ S A B} (σPre {A} {B} (a , joinPre P)) g
    muEta {A} {B} a P g = begin
      ∫ {_×Q_ S A B} (joinPre (mapPre (σH A B) (σPre {A} {TQ B} (a , P)))) g
        ≈⟨ ∫-join (mapPre (σH A B) (σPre {A} {TQ B} (a , P))) g ⟩
      ∫ {TQ (_×Q_ S A B)} (mapPre (σH A B) (σPre {A} {TQ B} (a , P))) (∫ᶠ g)
        ≈⟨ via {TQ (_×Q_ S A B)} {TQ B} {mapPre (σH A B) (σPre {A} {TQ B} (a , P))} {P}
             (Ir (m P) (λ r → ∫-σ {A} {B} a (α P ⟨$⟩ r) g)) ⟩
      ∫ {TQ B} P (∫ᶠ (fixH {A} {B} a g))
        ≈˘⟨ ∫-join {B} P (fixH {A} {B} a g) ⟩
      ∫ {B} (joinPre P) (fixH {A} {B} a g)
        ≈˘⟨ ∫-σ {A} {B} a (joinPre P) g ⟩
      ∫ {_×Q_ S A B} (σPre {A} {B} (a , joinPre P)) g ∎

  -- Not `QBS.Category.Cartesian`: using the exported aliases here made `commutative` about 7% slower (45 s
  -- against 42 s) for no reason found, so this module keeps its own (see plans/Simplify.md, Stage 4 follow-up).
  private
    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
    V = CM.CartesianMonoidal.monoidal cartesian

  abstract
    strength : Strength V TM
    strength = record
      { strengthen = record
          { η = λ { (X , Y) → σH X Y }
          ; commute = λ f {(x , q)} h → via (Ir (m q) (λ r → Setoid.refl Aˢ))
          ; sym-commute = λ f {(x , q)} h → via (Ir (m q) (λ r → Setoid.refl Aˢ))
          }
      ; identityˡ = λ {_} {(_ , q)} h → via (Ir (m q) (λ r → Setoid.refl Aˢ))
      ; η-comm = λ {A} {B} {x} h →
          Setoid.trans Aˢ (∫-σ {A} {B} (proj₁ x) (ηPre {B} (proj₂ x)) h)
            (Setoid.trans Aˢ (∫-unfold {B} (ηPre {B} (proj₂ x)) (fixH {A} {B} (proj₁ x) h))
              (Setoid.sym Aˢ (∫-unfold {_×Q_ S A B} (ηPre {_×Q_ S A B} x) h)))
      ; μ-η-comm = λ {A} {B} {(a , P)} g → muEta {A} {B} a P g
      ; strength-assoc = λ {_} {_} {_} {((x , y) , q)} h → via (Ir (m q) (λ r → Setoid.refl Aˢ))
      }

    -- the left strength acts on pre-measures as `σPre` (the only fact about the abstract `strength` that is used)
    σ-red : ∀ {X Y : QBS S} (p : ∣ _×Q_ S X (TQ Y) ∣) (f : Hom S (_×Q_ S X Y) AQ) →
      ∫ {_×Q_ S X Y} (map (NaturalTransformation.η (Strength.strengthen strength) (X , Y)) ⟨$⟩ p) f
      ≈ ∫ {_×Q_ S X Y} (σPre {X} {Y} p) f
    σ-red p f = Setoid.refl Aˢ

  strongMonad : StrongMonad V
  strongMonad = record { M = TM ; strength = strength }
