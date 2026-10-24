{-# OPTIONS --safe --without-K #-}

-- Strength of the measure monad: σ_{X,Y} : X × T Y → T (X × Y), (x, q) ↦ T (x, –) q.
module QBS.Model.Strong where

open import Level using (Level; suc; _⊔_; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

open import Categories.Category.Core using (Category)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_)
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad

module Strength {ℓ} (A : CompleteSemiring ℓ) (K : WeightClass A) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open WeightClass K
  open Measures A K
  private
    S = discreteSource ℓ
    R = Lift ℓ ℕ
  open RandomSource S using () renaming (pair to pairᴺ; unpair to unpairᴺ; unpair-pair to unpair-pairᴺ)
  open QBS
  open Hom
  open Pre
  open Wit

  -- the left strength on pre-measures
  σPre : ∀ {X Y : QBS S} → ∣ _×Q_ S X (TQ Y) ∣ → Pre (_×Q_ S X Y)
  σPre {X} {Y} (x , q) =
    mk (λ r → x , α q r) (QBS.const-random X x , α-random q) (μ q) (μ-ok q)

  private
    φ : ℕ → R → R
    φ n m = lift (pairᴺ n (lower m))

    ιR : R → R
    ιR k = lift (proj₁ (unpairᴺ (lower k)))

    ρ : R → R
    ρ k = lift (proj₂ (unpairᴺ (lower k)))

    -- the test function y ↦ f (x, y)
    fix : ∀ {X Y : QBS S} → ∣ X ∣ → Func (×-setoid (Carrier X) (Carrier Y)) Aˢ → Func (Carrier Y) Aˢ
    fix {X} {Y} x f = record
      { to = λ y → f ⟨$⟩ (x , y)
      ; cong = λ e → Func.cong f (Setoid.refl (Carrier X) , e)
      }

  σH : ∀ X Y → Hom S (_×Q_ S X (TQ Y)) (TQ (_×Q_ S X Y))
  σH X Y = record
    { map = record
        { to = σPre {X} {Y}
        ; cong = λ {(x , q)} {(x′ , q′)} (ex , eq) f →
            Setoid.trans Aˢ (eq (fix {X} {Y} x f))
              (∑-cong (λ r → *-cong (Setoid.refl Aˢ)
                (Func.cong f (ex , Setoid.refl (Carrier Y)))))
        }
    ; map-random = λ {β} (pb , w) → record
        { wα = λ k → B β w (unpairᴺ (lower k))
        ; wα-random =
            QBS.pre-random X pb tt , QBS.pre-random Y (wα-random w) tt
        ; wg = λ r → push (φ (lower r)) (wg w r)
        ; wg-ok = λ r → ok-push (φ (lower r)) (wg-ok w r)
        ; w-eq = λ r f →
            Setoid.trans Aˢ (w-eq w r (fix {X} {Y} (proj₁ (β r)) f))
              (Setoid.sym Aˢ (Setoid.trans Aˢ
                (push-∑ (φ (lower r)) (wg w r) (λ k → f ⟨$⟩ B β w (unpairᴺ (lower k))))
                (∑-cong (λ m → *-cong (Setoid.refl Aˢ)
                  (Func.cong f (Setoid.reflexive (Carrier (_×Q_ S X Y))
                    (≡.cong (B β w) (unpair-pairᴺ (lower r) (lower m)))))))))
        }
    }
    where
      B : ∀ (β : R → ∣ _×Q_ S X (TQ Y) ∣) → Wit (λ r → proj₂ (β r)) → ℕ × ℕ → ∣ _×Q_ S X Y ∣
      B β w u = proj₁ (β (lift (proj₁ u))) , wα w (lift (proj₂ u))

  open import Categories.Category.Product using (Product; _⁂_)
  open import Categories.Monad.Strong using (Strength; StrongMonad)
  import Categories.Monad.Strong.Properties
  import Categories.Category.Cartesian.Monoidal as CM
  import Categories.Category.CartesianClosed.Canonical as Canonical
  open import Categories.NaturalTransformation using (NaturalTransformation)
  open import QBS.Exponential using (cartesianClosed)

  private
    cartesian = Canonical.CartesianClosed.isCartesian (cartesianClosed S)
    V = CM.CartesianMonoidal.monoidal cartesian

  strength : Strength V TM
  strength = record
    { strengthen = record
        { η = λ { (X , Y) → σH X Y }
        ; commute = λ _ _ _ → Setoid.refl Aˢ
        ; sym-commute = λ _ _ _ → Setoid.refl Aˢ
        }
    ; identityˡ = λ _ _ → Setoid.refl Aˢ
    ; η-comm = λ _ _ → Setoid.refl Aˢ
    ; μ-η-comm = λ {A} {B} (a , P) g →
        Setoid.trans Aˢ (∫-join (mapPre (σH A B) (σPre {A} {TQ B} (a , P))) g)
          (Setoid.sym Aˢ (∫-join {B} P (fix {A} {B} a g)))
    ; strength-assoc = λ _ _ → Setoid.refl Aˢ
    }

  open import Categories.Monad.Commutative using (Commutative; CommutativeMonad)
  import Categories.Category.Cartesian.SymmetricMonoidal as CSM
  open import Categories.Category.Monoidal.Symmetric using (Symmetric)

  strongMonad : StrongMonad V
  strongMonad = record { M = TM ; strength = strength }

  private
    braided = Symmetric.braided (CSM.symmetric (QBSCat S) cartesian)

  -- Fubini: the two orders of integrating a pair of independent measures agree.
  fubini : ∀ {X Y : QBS S} (s : Pre X) (t : Pre Y) (g : Func (×-setoid (Carrier X) (Carrier Y)) Aˢ) →
    ∑ (λ r → μ t r * ∑ (λ k → μ s k * (g ⟨$⟩ (α s k , α t r))))
      ≈ ∑ (λ k → μ s k * ∑ (λ r → μ t r * (g ⟨$⟩ (α s k , α t r))))
  fubini {X} {Y} s t g = begin
    ∑ (λ r → μ t r * ∑ (λ k → μ s k * G k r))
      ≈⟨ ∑-cong (λ r → sym (∑-scale (μ t r) (λ k → μ s k * G k r))) ⟩
    ∑ (λ r → ∑ (λ k → μ t r * (μ s k * G k r)))
      ≈⟨ ∑-swap (λ r k → μ t r * (μ s k * G k r)) ⟩
    ∑ (λ k → ∑ (λ r → μ t r * (μ s k * G k r)))
      ≈⟨ ∑-cong (λ k → ∑-cong (λ r → mid (μ t r) (μ s k) (G k r))) ⟩
    ∑ (λ k → ∑ (λ r → μ s k * (μ t r * G k r)))
      ≈⟨ ∑-cong (λ k → ∑-scale (μ s k) (λ r → μ t r * G k r)) ⟩
    ∑ (λ k → μ s k * ∑ (λ r → μ t r * G k r))
      ∎
    where
      open SetoidReasoning Aˢ
      G = λ k r → g ⟨$⟩ (α s k , α t r)
      mid : ∀ x y z → x * (y * z) ≈ y * (x * z)
      mid x y z = trans (sym (*-assoc x y z)) (trans (*-cong (*-comm x y) refl) (*-assoc y x z))

  private
    module SP = Categories.Monad.Strong.Properties
    module RS = SP.Right.Shorthands (SP.Strength⇒RightStrength braided strength)

  commutative : Commutative braided strongMonad
  commutative = record { commutes = λ {X} {Y} (s , t) g →
    Setoid.trans Aˢ
      (∫-join (mapPre (RS.τ {X} {Y}) (σPre {TQ X} {Y} (s , t))) g)
      (Setoid.trans Aˢ (fubini {X} {Y} s t g)
        (Setoid.sym Aˢ (∫-join (mapPre (σH X Y) (map (RS.τ {X} {TQ Y}) ⟨$⟩ (s , t))) g))) }
