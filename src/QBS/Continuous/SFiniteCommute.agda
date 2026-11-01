{-# OPTIONS --safe --without-K #-}

-- Commutativity of the s-finite measure monad: Fubini for unbounded integrands (`Analysis/JFubini`).

module QBS.Continuous.SFiniteCommute where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (proj₁ₛ; proj₂ₛ; <_,_>ₛ)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; measurable-merge₂; Cyl-rect)
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
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Classical using (LEM₀)

module SFiniteCommute (lem : LEM₀) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zero⇒)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open UnitInterval A using (AQ)
  open RandomSource S using (Rˢ) renaming (meas-id to measId)
  open SFinite lem
  open WitM
  open SFiniteMonad lem
  open SFiniteStrong lem
  open JFubini lem
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  open import Categories.Monad.Strong using (Strength; StrongMonad)
  import Categories.Monad.Strong.Properties
  open import QBS.Category.Cartesian S using (cartesian; braided)
  open import Categories.Monad.Commutative using (Commutative; CommutativeMonad)

  private
    module SP = Categories.Monad.Strong.Properties
    module RS = SP.Right.Shorthands (SP.Strength⇒RightStrength braided strength)

  τH : ∀ X Y → Hom S (_×Q_ S (TQ X) Y) (TQ (_×Q_ S X Y))
  τH X Y = RS.τ {X} {Y}

  τ-app : ∀ {X Y : QBS S} → Pre (XW X) → ∣ Y ∣ → Pre (XW (_×Q_ S X Y))
  τ-app {X} {Y} s y = map (τH X Y) ⟨$⟩ (s , y)

  -- the test function x ↦ f (x , y)
  fixH₂ : ∀ {X Y : QBS S} → ∣ Y ∣ → Hom S (_×Q_ S X Y) WQ → Hom S X WQ
  fixH₂ {X} {Y} y f = record
    { map = record
        { to = λ x → map f ⟨$⟩ (x , y)
        ; cong = λ e → Func.cong (map f) (e , Setoid.refl (Carrier Y)) }
    ; map-random = λ {γ} rγ → map-random f {< γ , constₛ y >ₛ} (rγ , const-random Y y)
    }

  -- the right strength integrates the left component
  τ-int : ∀ {X Y : QBS S} (s : Pre (XW X)) (y : ∣ Y ∣) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (τ-app {X} {Y} s y) g ≈ ∫ᴹ {X} s (fixH₂ {X} {Y} y g)
  τ-int {X} {Y} s y g =
    trans (∫ᴹ-map _ (σPre {Y} {X} (y , s)) g)
      (trans (∫ᴹ-σ {Y} {X} y s _) (∫ᴹ-cong s (λ x → refl)))

  ----------------------------------------------------------------------------
  -- Fubini for two measures on W × X and W × Y

  module Fub {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) where
    -- the joint weighted integrand at the merged parameter
    Φ : R₁ → Cut
    Φ u = proj₁ (α s ⟨$⟩ (evensR u)) * (proj₁ (α t ⟨$⟩ (oddsR u)) *
            (map g ⟨$⟩ (proj₂ (α s ⟨$⟩ (evensR u)) , proj₂ (α t ⟨$⟩ (oddsR u)))))

    abstract
      mΦ : Meas Φ
      mΦ = Meas-⊗ {λ u → proj₁ (α s ⟨$⟩ (evensR u))} {λ u → proj₁ (α t ⟨$⟩ (oddsR u)) *
              (map g ⟨$⟩ (proj₂ (α s ⟨$⟩ (evensR u)) , proj₂ (α t ⟨$⟩ (oddsR u))))}
             (Meas-pre {λ r → proj₁ (α s ⟨$⟩ r)} {evensR} (proj₁ (α-random s)) measurable-evens)
             (Meas-⊗ {λ u → proj₁ (α t ⟨$⟩ (oddsR u))} {λ u → map g ⟨$⟩ (proj₂ (α s ⟨$⟩ (evensR u)) , proj₂ (α t ⟨$⟩ (oddsR u)))}
                (Meas-pre {λ r → proj₁ (α t ⟨$⟩ r)} {oddsR} (proj₁ (α-random t)) measurable-odds)
                (map-random g {< proj₂ₛ ∘ₛ α s ∘ₛ evensₛ , proj₂ₛ ∘ₛ α t ∘ₛ oddsₛ >ₛ}
                   (QBS.pre-random X {proj₂ₛ ∘ₛ α s} {evensₛ} (proj₂ (α-random s)) measurable-evens ,
                    QBS.pre-random Y {proj₂ₛ ∘ₛ α t} {oddsₛ} (proj₂ (α-random t)) measurable-odds)))
        where
          evensₛ oddsₛ : Func Rˢ Rˢ
          evensₛ = proj₁ₛ ∘ₛ map fromH
          oddsₛ = proj₂ₛ ∘ₛ map fromH

    -- Φ at a merged pair of parameters
    Φ-merge : ∀ r r′ → Φ (mergeR r r′) ≈
      proj₁ (α s ⟨$⟩ r) * (proj₁ (α t ⟨$⟩ r′) * (map g ⟨$⟩ (proj₂ (α s ⟨$⟩ r) , proj₂ (α t ⟨$⟩ r′))))
    Φ-merge r r′ =
      let cs = Func.cong (α s) (merge-evens r r′)
          ct = Func.cong (α t) (merge-odds r r′)
      in *-cong (proj₁ cs) (*-cong (proj₁ ct) (Func.cong (map g) (proj₂ cs , proj₂ ct)))

    constH : ∀ {A B : QBS S} → ∣ B ∣ → Hom S A B
    constH {A} {B} b = record
      { map = record { to = λ _ → b ; cong = λ _ → Setoid.refl (Carrier B) }
      ; map-random = λ _ → const-random B b }

    -- the two sides of Fubini as test functions on the other factor
    Gs : Hom S Y WQ
    Gs = _∘H_ S {Y} {_×Q_ S (TQ X) Y} {WQ} (_∘H_ S {_×Q_ S (TQ X) Y} {TQ (_×Q_ S X Y)} {WQ} (∫ᶠ {_×Q_ S X Y} g) (τH X Y))
           (pairQ S {Y} {TQ X} {Y} (constH s) (idH S))

    Gt : Hom S X WQ
    Gt = _∘H_ S {X} {_×Q_ S X (TQ Y)} {WQ} (_∘H_ S {_×Q_ S X (TQ Y)} {TQ (_×Q_ S X Y)} {WQ} (∫ᶠ {_×Q_ S X Y} g) (σH X Y))
           (pairQ S {X} {X} {TQ Y} (idH S) (constH t))

    open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup using () renaming (x∙yz≈y∙xz to swap3)

    pw₂ : ∀ r → ψ {Y} t Gs r ≈ J (m s) (λ k → Φ (P₂.mergeR r k))
      (Meas-pre {Φ} {P₂.mergeR r} mΦ (measurable-merge₂ (lower r)))
    pw₂ r = trans (*-cong refl (τ-int {X} {Y} s (proj₂ (α t ⟨$⟩ r)) g))
      (trans (sym (J-scale (m s) (proj₁ (α t ⟨$⟩ r)) {ψ {X} s (fixH₂ {X} {Y} (proj₂ (α t ⟨$⟩ r)) g)}
                     (mψ {X} s (fixH₂ {X} {Y} (proj₂ (α t ⟨$⟩ r)) g))))
        (J-cong (m s) {λ k → proj₁ (α t ⟨$⟩ r) * ψ {X} s (fixH₂ {X} {Y} (proj₂ (α t ⟨$⟩ r)) g) k} {λ k → Φ (P₂.mergeR r k)}
          (Meas-⊗ {λ _ → proj₁ (α t ⟨$⟩ r)} {ψ {X} s (fixH₂ {X} {Y} (proj₂ (α t ⟨$⟩ r)) g)}
            (Meas-const (proj₁ (α t ⟨$⟩ r))) (mψ {X} s (fixH₂ {X} {Y} (proj₂ (α t ⟨$⟩ r)) g)))
          (Meas-pre {Φ} {P₂.mergeR r} mΦ (measurable-merge₂ (lower r)))
          (λ k → trans (swap3 _ _ _) (sym (Φ-merge k r)))))

    pw₁ : ∀ k → ψ {X} s Gt k ≈ J (m t) (λ r → Φ (P₁.mergeR k r))
      (Meas-pre {Φ} {P₁.mergeR k} mΦ (measurable-merge₁ (lower k)))
    pw₁ k = trans (*-cong refl (∫ᴹ-σ {X} {Y} (proj₂ (α s ⟨$⟩ k)) t g))
      (trans (sym (J-scale (m t) (proj₁ (α s ⟨$⟩ k)) {ψ {Y} t (fixH {X} {Y} (proj₂ (α s ⟨$⟩ k)) g)}
                     (mψ {Y} t (fixH {X} {Y} (proj₂ (α s ⟨$⟩ k)) g))))
        (J-cong (m t) {λ r → proj₁ (α s ⟨$⟩ k) * ψ {Y} t (fixH {X} {Y} (proj₂ (α s ⟨$⟩ k)) g) r} {λ r → Φ (P₁.mergeR k r)}
          (Meas-⊗ {λ _ → proj₁ (α s ⟨$⟩ k)} {ψ {Y} t (fixH {X} {Y} (proj₂ (α s ⟨$⟩ k)) g)}
            (Meas-const (proj₁ (α s ⟨$⟩ k))) (mψ {Y} t (fixH {X} {Y} (proj₂ (α s ⟨$⟩ k)) g)))
          (Meas-pre {Φ} {P₁.mergeR k} mΦ (measurable-merge₁ (lower k)))
          (λ r → sym (Φ-merge k r))))

    fubiniᴹ : ∫ᴹ {Y} t Gs ≈ ∫ᴹ {X} s Gt
    fubiniᴹ = trans
      (J-cong (m t) {ψ {Y} t Gs} {λ r → J (m s) (λ k → Φ (P₂.mergeR r k))
          (Meas-pre {Φ} {P₂.mergeR r} mΦ (measurable-merge₂ (lower r)))}
        (mψ {Y} t Gs) (Meas-Jsec₂ (λ _ → m s) (constK (m s)) {Φ} mΦ) pw₂)
      (trans (sym (J-fubini (m s) (m t) {Φ} mΦ))
        (sym (J-cong (m s) {ψ {X} s Gt} {λ k → J (m t) (λ r → Φ (P₁.mergeR k r))
            (Meas-pre {Φ} {P₁.mergeR k} mΦ (measurable-merge₁ (lower k)))}
          (mψ {X} s Gt) (Meas-Jsec (λ _ → m t) (constK (m t)) {Φ} mΦ) pw₁)))

  commA : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (joinPre {_×Q_ S X Y} (mapM {_×Q_ S (TQ X) Y} {TQ (_×Q_ S X Y)} (τH X Y) (σPre {TQ X} {Y} (s , t)))) g
      ≈ ∫ᴹ {Y} t (Fub.Gs {X} {Y} s t g)
  commA {X} {Y} s t g =
    trans (∫ᴹ-join {_×Q_ S X Y} (mapM {_×Q_ S (TQ X) Y} {TQ (_×Q_ S X Y)} (τH X Y) (σPre {TQ X} {Y} (s , t))) g)
      (trans (∫ᴹ-map {_×Q_ S (TQ X) Y} {TQ (_×Q_ S X Y)} (τH X Y) (σPre {TQ X} {Y} (s , t)) (∫ᶠ {_×Q_ S X Y} g))
        (trans (∫ᴹ-σ {TQ X} {Y} s t (_∘H_ S (∫ᶠ {_×Q_ S X Y} g) (τH X Y)))
          (∫ᴹ-cong {Y} t {fixH {TQ X} {Y} s (_∘H_ S (∫ᶠ {_×Q_ S X Y} g) (τH X Y))} {Fub.Gs {X} {Y} s t g}
            (λ y → refl))))

  Hg : ∀ {X Y : QBS S} → Hom S (_×Q_ S X Y) WQ → Hom S (_×Q_ S X (TQ Y)) WQ
  Hg {X} {Y} g = _∘H_ S (∫ᶠ g) (σH X Y)

  zz : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ s (fixH₂ {X} {TQ Y} t (Hg g)) ≈ ∫ᴹ s (Fub.Gt s t g)
  zz s t g = ∫ᴹ-cong s (λ x → refl)

  commB₀ : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ (τ-app {X} {TQ Y} s t) (Hg g) ≈ ∫ᴹ s (Fub.Gt s t g)
  commB₀ s t g = trans (τ-int s t (Hg g)) (zz s t g)

  mapStep : ∀ {X Y : QBS S} (p : Pre (XW (_×Q_ S X (TQ Y)))) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ (mapM {_×Q_ S X (TQ Y)} {TQ (_×Q_ S X Y)} (σH X Y) p) (∫ᶠ g) ≈ ∫ᴹ p (Hg g)
  mapStep {X} {Y} p g = ∫ᴹ-map (σH X Y) p (∫ᶠ g)

  commB₁ : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ (mapM {_×Q_ S X (TQ Y)} {TQ (_×Q_ S X Y)} (σH X Y) (τ-app {X} {TQ Y} s t)) (∫ᶠ g) ≈ ∫ᴹ s (Fub.Gt s t g)
  commB₁ s t g = trans (mapStep (τ-app s t) g) (commB₀ s t g)

  commB₂ : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (joinPre {_×Q_ S X Y} (mapM {_×Q_ S X (TQ Y)} {TQ (_×Q_ S X Y)} (σH X Y) (τ-app {X} {TQ Y} s t))) g
      ≈ ∫ᴹ s (Fub.Gt s t g)
  commB₂ s t g = trans (∫ᴹ-join _ g) (commB₁ s t g)

  commB : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ {_×Q_ S X Y} (map (joinT (_×Q_ S X Y)) ⟨$⟩ (map (TH {_×Q_ S X (TQ Y)} {TQ (_×Q_ S X Y)} (σH X Y)) ⟨$⟩
                       (τ-app {X} {TQ Y} s t))) g
      ≈ ∫ᴹ {X} s (Fub.Gt {X} {Y} s t g)
  commB s t g = commB₂ s t g

  open import Categories.Category.Core using (Category)

  catB : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ (Func.to (map (Category._∘_ (QBSCat S)
          (NaturalTransformation.η (Monad.μ (StrongMonad.M strongMonad)) (_×Q_ S X Y))
          (Category._∘_ (QBSCat S)
            (Functor.F₁ (Monad.F (StrongMonad.M strongMonad))
                (NaturalTransformation.η (Strength.strengthen (StrongMonad.strength strongMonad)) (X , Y)))
            (RS.τ {X} {TQ Y}))) ) (s , t)) g
      ≈ ∫ᴹ s (Fub.Gt s t g)
  catB s t g = commB₂ s t g

  catA : ∀ {X Y : QBS S} (s : Pre (XW X)) (t : Pre (XW Y)) (g : Hom S (_×Q_ S X Y) WQ) →
    ∫ᴹ (Func.to (map (Category._∘_ (QBSCat S)
          (NaturalTransformation.η (Monad.μ (StrongMonad.M strongMonad)) (_×Q_ S X Y))
          (Category._∘_ (QBSCat S)
            (Functor.F₁ (Monad.F (StrongMonad.M strongMonad)) (RS.τ {X} {Y}))
            (NaturalTransformation.η (Strength.strengthen (StrongMonad.strength strongMonad)) (TQ X , Y)))) ) (s , t)) g
      ≈ ∫ᴹ t (Fub.Gs s t g)
  catA s t g = commA s t g

  commutative : Commutative braided strongMonad
  commutative = record { commutes = λ {X} {Y} {(s , t)} g →
    trans (catA s t g) (trans (Fub.fubiniᴹ s t g) (sym (catB s t g))) }
