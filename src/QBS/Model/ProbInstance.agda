{-# OPTIONS --safe --without-K #-}

-- The discrete probability monad is a model of `ProbabilityInterface`.
module QBS.Model.ProbInstance where

open import Level using (Level; suc; Lift; lift; lower)
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_; _↔_; mk↔ₛ′)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import Categories.Category.Core using (Category)
open import Categories.Monad.Commutative using (CommutativeMonad)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe; unprobe)
open import QBS.Probability
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.WeightClasses
open import QBS.Model.Strong
open import QBS.Model.Cantor

module _ {ℓ} (A : CompleteSemiring ℓ) where
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  open Cantor A
  private
    open DS ℓ using (S)
    K = probClass A
    R = Lift ℓ ℕ
  open WeightClass K
  open Measures A K
  open Strength A K using (strongMonad; commutative; commutativeMonad)
  open QBS
  open Hom
  open Pre

  private
    -- the law of a probe under a probability measure
    lawP : ∀ {X : QBS S} → Hom S (ℛQ S) X → Σ (R → ∣A∣) Ok → Pre X
    lawP a (μ , ok) = mk (λ r → map a ⟨$⟩ r) (unprobe S a) μ ok

    lawH : ∀ {X : QBS S} → Hom S (ℛQ S) X → Σ (R → ∣A∣) Ok → Hom S (1Q S) (TQ X)
    lawH {X} a m = record
      { map = record { to = λ _ → lawP a m ; cong = λ _ _ → Setoid.refl Aˢ }
      ; map-random = λ _ → QBS.const-random (TQ X) (lawP a m)
      }

    tensorW : (R → ∣A∣) → (R → ∣A∣) → R → ∣A∣
    tensorW μ ν k = μ (ιR k) * ν (ρR k)

    kerPre : ∀ {X : QBS S} → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) X → Σ (R → ∣A∣) Ok → R → Pre X
    kerPre {X} γ (ν , ok) r = mk (λ s → map γ ⟨$⟩ (r , s)) (map-random γ {λ s → r , s} (tt , tt)) ν ok

    kerEq : ∀ {X : QBS S} (γ : Hom S (_×Q_ S (ℛQ S) (ℛQ S)) X) (α : R → R) s m →
      map γ ⟨$⟩ (α (ιR (lift (pair (lower s) (lower m)))) , ρR (lift (pair (lower s) (lower m))))
        ≡ map γ ⟨$⟩ (α s , m)
    kerEq γ α s m rewrite unpair-pair (lower s) (lower m) = ≡.refl

    kerH : ∀ {X : QBS S} → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) X → Σ (R → ∣A∣) Ok → Hom S (ℛQ S) (TQ X)
    kerH {X} γ m@(ν , ok) = record
      { map = record { to = kerPre γ m ; cong = λ { ≡.refl _ → Setoid.refl Aˢ } }
      ; map-random = λ {α} _ → record
          { wα = λ k → map γ ⟨$⟩ (α (ιR k) , ρR k)
          ; wα-random = map-random γ {λ k → α (ιR k) , ρR k} (tt , tt)
          ; wg = λ s → push (φ (lower s)) ν
          ; wg-ok = λ s → ok-push _ ok
          ; w-eq = λ s f → Setoid.sym Aˢ (Setoid.trans Aˢ
              (push-∑ (φ (lower s)) ν (λ k → f ⟨$⟩ (map γ ⟨$⟩ (α (ιR k) , ρR k))))
              (∑-cong (λ m′ → *-cong (Setoid.refl Aˢ)
                (Func.cong f (Setoid.reflexive (Carrier X) (kerEq γ α s m′))))))
          }
      }

  discreteProbLaws : ProbLaws ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) commutativeMonad
  discreteProbLaws = record
    { Measure = Σ (R → ∣A∣) Ok
    ; pushforward = λ m (μ , ok) → push (λ r → map m ⟨$⟩ r) μ , ok-push _ ok
    ; measure = lawH (idH S)
    ; measure-push = λ m (μ , ok) _ g → Setoid.sym Aˢ (push-∑ (λ r → map m ⟨$⟩ r) μ (λ k → g ⟨$⟩ k))
    ; measure-total = λ (μ , ok) pt f →
        Setoid.sym Aˢ (Setoid.trans Aˢ (∫-η {1Q S} pt f)
          (Setoid.sym Aˢ (trans (sym (∑-distribʳ μ (f ⟨$⟩ pt)))
            (trans (*-cong ok refl) (*-identityˡ _)))))
    ; law-surjective = λ {X} t →
        let p = map t ⟨$⟩ tt
        in probe S (α-random p) , (μ p , μ-ok p) , (λ pt f → Setoid.refl Aˢ)
    }

  discreteProbFubini : Fubini ℓ (QBSCat S) (ℛQ S) (cartesianClosed S) commutativeMonad discreteProbLaws
  discreteProbFubini = record
    { split = record
        { from = record
            { map = record { to = λ r → ιR r , ρR r ; cong = λ { ≡.refl → ≡.refl , ≡.refl } }
            ; map-random = λ _ → tt , tt }
        ; to = record
            { map = record
                { to = λ p → lift (pair (lower (proj₁ p)) (lower (proj₂ p)))
                ; cong = λ { (≡.refl , ≡.refl) → ≡.refl } }
            ; map-random = λ _ → tt }
        ; iso = record
            { isoˡ = λ r → ≡.cong lift (pair-unpair (lower r))
            ; isoʳ = λ { (r₁ , r₂) →
                ≡.cong (λ u → lift (proj₁ u)) (unpair-pair (lower r₁) (lower r₂))
                , ≡.cong (λ u → lift (proj₂ u)) (unpair-pair (lower r₁) (lower r₂)) }
            }
        }
    ; tensor = λ (μ , okμ) (ν , okν) →
        tensorW μ ν
        , trans (cantor (λ a b → μ a * ν b))
            (trans (∑-prod μ ν) (trans (*-cong okμ okν) (*-identityˡ 1#)))
    ; kernel = kerH
    ; kernel-law = λ γ m r _ f → Setoid.refl Aˢ
    ; law-join = λ {X} γ (μ , okμ) (ν , okν) _ f →
        Setoid.trans Aˢ (∫-join {X} (lawP (kerH γ (ν , okν)) (μ , okμ)) f)
          (Setoid.trans Aˢ (∑-cong (λ s → sym (∑-scale (μ s) _)))
            (Setoid.trans Aˢ (∑-cong (λ s → ∑-cong (λ m → sym (*-assoc (μ s) (ν m) _))))
              (Setoid.sym Aˢ (cantor (λ a b → (μ a * ν b) * (f ⟨$⟩ (map γ ⟨$⟩ (a , b))))))))
    }

  discreteProb : ProbabilityInterface ℓ (QBSCat S) (ℛQ S) (cartesianClosed S)
  discreteProb = record
    { commutativeMonad = commutativeMonad
    ; laws = discreteProbLaws
    ; fubini = discreteProbFubini
    }
