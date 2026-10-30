{-# OPTIONS --safe --without-K #-}

-- Strength and commutativity of the s-finite measure monad.  Commutativity is Fubini for unbounded
-- integrands (`Analysis/JFubini`).

module QBS.Continuous.SFiniteStrong where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)

module SFiniteStrong (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroW)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open Split funext
  open UnitInterval A using (AQ)
  open RandomSource S using () renaming (meas-id to measId)
  open SFinite lem funext
  open WitM
  open SFiniteMonad lem funext
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  -- the test function y ↦ f (x , y)
  fixH : ∀ {X Y : QBS S} → ∣ X ∣ → Hom S (_×Q_ S X Y) WQ → Hom S Y WQ
  fixH {X} {Y} x f = record
    { map = record
        { to = λ y → map f ⟨$⟩ (x , y)
        ; cong = λ e → Func.cong (map f) (Setoid.refl (Carrier X) , e) }
    ; map-random = λ {γ} rγ → map-random f {λ r → x , γ r} (const-random X x , rγ)
    }

  -- the left strength on pre-measures
  σPre : ∀ {X Y : QBS S} → ∣ _×Q_ S X (TQ Y) ∣ → Pre (XW (_×Q_ S X Y))
  σPre {X} {Y} (x , q) = mk (λ r → proj₁ (α q r) , (x , proj₂ (α q r)))
    (proj₁ (α-random q) , (const-random X x , proj₂ (α-random q))) (m q) (ok q)

  ∫ᴹ-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre (XW Y)) (f : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f ≈ ∫ᴹ {Y} q (fixH {X} {Y} x f)
  ∫ᴹ-σ {X} {Y} x q f = J-cong (m q) {ψ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f} {ψ {Y} q (fixH {X} {Y} x f)}
    (mψ {_×Q_ S X Y} (σPre {X} {Y} (x , q)) f) (mψ {Y} q (fixH {X} {Y} x f)) (λ r → refl)

  -- the joint probe of a random family `r ↦ (x r , q r)` with `q` given by a section witness
  σJ : ∀ {X Y : QBS S} {β : R₁ → ∣ _×Q_ S X (TQ Y) ∣} → Random X (λ r → proj₁ (β r)) →
    WitM {Y} (λ r → proj₂ (β r)) → Joint (XW (_×Q_ S X Y))
  σJ {X} {Y} {β} pb w = pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {WQ} {_×Q_ S X Y}
    (_∘H_ S (fstQ S {WQ} {Y}) (a w))
    (pairQ S {_×Q_ S (Probes.ℛQ S) (Probes.ℛQ S)} {X} {Y} (fstJ {X} (λ r → proj₁ (β r)) pb)
       (_∘H_ S (sndQ S {WQ} {Y}) (a w)))

  σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
  σH X Y = record
    { map = record
        { to = σPre {X} {Y}
        ; cong = λ {(x , q)} {(x′ , q′)} (ex , eq) f →
            trans (∫ᴹ-σ {X} {Y} x q f)
              (trans (eq (fixH {X} {Y} x f))
                (trans (∫ᴹ-cong {Y} q′ {fixH {X} {Y} x f} {fixH {X} {Y} x′ f}
                          (λ y → Func.cong (map f) (ex , Setoid.refl (Carrier Y))))
                  (sym (∫ᴹ-σ {X} {Y} x′ q′ f))))
        }
    ; map-random = λ {β} (pb , w) → record
        { a = σJ {X} {Y} {β} pb w
        ; g = g w
        ; g-ok = g-ok w
        ; g-pr = g-pr w
        ; w-eq = λ r f →
            trans (∫ᴹ-σ {X} {Y} (proj₁ (β r)) (proj₂ (β r)) f)
              (trans (w-eq w r (fixH {X} {Y} (proj₁ (β r)) f))
                (J-cong (g w r) {ψ {Y} (kerP {Y} (a w) (g w) (g-pr w) r) (fixH {X} {Y} (proj₁ (β r)) f)}
                  {ψ {_×Q_ S X Y} (kerP {_×Q_ S X Y} (σJ {X} {Y} {β} pb w) (g w) (g-pr w) r) f}
                  (mψ {Y} (kerP {Y} (a w) (g w) (g-pr w) r) (fixH {X} {Y} (proj₁ (β r)) f))
                  (mψ {_×Q_ S X Y} (kerP {_×Q_ S X Y} (σJ {X} {Y} {β} pb w) (g w) (g-pr w) r) f)
                  (λ s → refl)))
        }
    }

  -- naturality of σ
  σ-nat : ∀ {X Y X′ Y′ : QBS S} (F : Hom S (_×Q_ S X Y) (_×Q_ S X′ Y′)) (f₁ : Hom S X X′) (f₂ : Hom S Y Y′) →
    (∀ x y → Setoid._≈_ (Carrier (_×Q_ S X′ Y′)) (map F ⟨$⟩ (x , y)) (map f₁ ⟨$⟩ x , map f₂ ⟨$⟩ y)) →
    ∀ (x : ∣ X ∣) (q : Pre (XW Y)) (h : Hom S (_×Q_ S X′ Y′) WQ) →
    ∫ᴹ {_×Q_ S X′ Y′} (σPre {X′} {Y′} (map f₁ ⟨$⟩ x , mapM {Y} {Y′} f₂ q)) h
      ≈ ∫ᴹ {_×Q_ S X′ Y′} (mapM {_×Q_ S X Y} {_×Q_ S X′ Y′} F (σPre {X} {Y} (x , q))) h
  σ-nat {X} {Y} {X′} {Y′} F f₁ f₂ e x q h =
    trans (∫ᴹ-σ {X′} {Y′} (map f₁ ⟨$⟩ x) (mapM {Y} {Y′} f₂ q) h)
      (trans (∫ᴹ-map {Y} {Y′} f₂ q (fixH {X′} {Y′} (map f₁ ⟨$⟩ x) h))
        (trans (∫ᴹ-cong {Y} q {_∘H_ S (fixH {X′} {Y′} (map f₁ ⟨$⟩ x) h) f₂} {fixH {X} {Y} x (_∘H_ S h F)}
                  (λ y → Func.cong (map h) (Setoid.sym (Carrier (_×Q_ S X′ Y′)) (e x y))))
          (sym (trans (∫ᴹ-map {_×Q_ S X Y} {_×Q_ S X′ Y′} F (σPre {X} {Y} (x , q)) h)
                      (∫ᴹ-σ {X} {Y} x q (_∘H_ S h F))))))

  open import Categories.Category.Product using (Product; _⁂_)
  open import Categories.Monad.Strong using (Strength; StrongMonad)
  import Categories.Monad.Strong.Properties
  import Categories.Category.Cartesian.Monoidal as CM
  import Categories.Category.CartesianClosed.Canonical as Canonical
  open import QBS.Exponential using (cartesianClosed)

  private
    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
    V = CM.CartesianMonoidal.monoidal cartesian
    {-# INLINE cartesian #-}
    {-# INLINE V #-}

  strength : Strength V TM
  strength = record
    { strengthen = record
        { η = λ { (X , Y) → σH X Y }
        ; commute = λ { {X₁ , X₂} {Y₁ , Y₂} (f₁ , f₂) (x , q) h →
            σ-nat _ f₁ f₂ (λ x y → Setoid.refl (Carrier (_×Q_ S Y₁ Y₂))) x q h }
        ; sym-commute = λ { {X₁ , X₂} {Y₁ , Y₂} (f₁ , f₂) (x , q) h →
            sym (σ-nat _ f₁ f₂ (λ x y → Setoid.refl (Carrier (_×Q_ S Y₁ Y₂))) x q h) }
        }
    ; identityˡ = λ {A} (t , q) h →
        trans (∫ᴹ-map _ (σPre {_} {A} (t , q)) h)
          (trans (∫ᴹ-σ {_} {A} t q _) (∫ᴹ-cong q (λ y → refl)))
    ; η-comm = λ {A} {B} (a , b) h →
        trans (∫ᴹ-σ {A} {B} a (C.ηPre {XW B} (1# , b)) h)
          (trans (∫ᴹ-η {B} b (fixH {A} {B} a h)) (sym (∫ᴹ-η {_×Q_ S A B} (a , b) h)))
    ; μ-η-comm = λ {A} {B} (a , P) g →
        trans (∫ᴹ-join (mapM (σH A B) (σPre {A} {TQ B} (a , P))) g)
          (trans (∫ᴹ-map (σH A B) (σPre {A} {TQ B} (a , P)) (∫ᶠ g))
            (trans (∫ᴹ-σ {A} {TQ B} a P (_∘H_ S (∫ᶠ g) (σH A B)))
              (trans (∫ᴹ-cong {TQ B} P {fixH {A} {TQ B} a (_∘H_ S (∫ᶠ g) (σH A B))} {∫ᶠ (fixH {A} {B} a g)}
                        (λ ν → ∫ᴹ-σ {A} {B} a ν g))
                (sym (trans (∫ᴹ-σ {A} {B} a (joinPre P) g) (∫ᴹ-join P (fixH {A} {B} a g)))))))
    ; strength-assoc = λ {A} {B} {C} ((x , y) , q) h →
        trans (∫ᴹ-map _ (σPre {_} {C} ((x , y) , q)) h)
          (trans (∫ᴹ-σ {_×Q_ S A B} {C} (x , y) q _)
            (trans (∫ᴹ-cong q (λ z → refl))
              (sym (trans (∫ᴹ-σ {A} {_} x (σPre {B} {C} (y , q)) h) (∫ᴹ-σ {B} {C} y q (fixH {A} {_} x h))))))
    }

  strongMonad : StrongMonad V
  strongMonad = record { M = TM ; strength = strength }
  {-# INLINE strongMonad #-}
