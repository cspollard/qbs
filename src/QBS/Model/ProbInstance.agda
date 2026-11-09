{-# OPTIONS --safe --without-K #-}

-- The discrete probability monad is a model of `ProbabilityInterface`.
module QBS.Model.ProbInstance where

open import Level using (Lift; lift; lower)
open import Function.Bundles using (Func; Inverse; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning


open import QBS.Core
import Categories.Category.SubCategory.SubHom as SH
open import Categories.Category.Instance.Setoids using (Setoids)
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; rand-pair)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe; unprobe)
open import QBS.Probability
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
  open SH (Setoids ℓ ℓ) using (mem)
  open QBS
  open Hom
  open Pre

  private
    -- the law of a probe under a probability measure
    lawP : ∀ {X : QBS S} → Hom S (ℛQ S) X → Σ (R → ∣A∣) Ok → Pre X
    lawP {X} a (μ , ok) = mk (map a) (unprobe S a) μ ok

    lawH : ∀ {X : QBS S} → Hom S (ℛQ S) X → Σ (R → ∣A∣) Ok → Hom S (1Q S) (TQ X)
    lawH {X} a m = record
      { map = record { to = λ _ → lawP a m ; cong = λ _ _ → Setoid.refl Aˢ }
      ; map-random = λ _ → QBS.const-random (TQ X) (lawP a m)
      }

    tensorW : (R → ∣A∣) → (R → ∣A∣) → R → ∣A∣
    tensorW μ ν k = μ (ιR k) * ν (ρR k)

    kerPre : ∀ {X : QBS S} → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) X → Σ (R → ∣A∣) Ok → R → Pre X
    kerPre {X} γ (ν , ok) r =
      mk (map γ ∘ₛ ⇑ (λ s → r , s)) (map-random γ {⇑ (λ s → r , s)}
        (rand-pair S {ℛQ S} {ℛQ S} {⇑ (λ s → r , s)} (RandomSource.meas₀ S tt) (RandomSource.meas₀ S tt))) ν ok

    kerH : ∀ {X : QBS S} → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) X → Σ (R → ∣A∣) Ok → Hom S (ℛQ S) (TQ X)
    kerH {X} γ m@(ν , ok) = record
      { map = kerF
      ; map-random = λ {α} _ → mem (kerF ∘ₛ α , record
          { wαₛ = map γ ∘ₛ ⇑ (λ k → α ⟨$⟩ ιR k , ρR k)
          ; wα-random = map-random γ {⇑ (λ k → α ⟨$⟩ ιR k , ρR k)}
            (rand-pair S {ℛQ S} {ℛQ S} {⇑ (λ k → α ⟨$⟩ ιR k , ρR k)}
              (RandomSource.meas₀ S tt) (RandomSource.meas₀ S tt))
          ; wg = λ s → push (φ (lower s)) ν
          ; wg-ok = λ s → ok-push _ ok
          ; w-eq = λ s f → Setoid.sym Aˢ
              (push-pair-∑ (lower s) ν (λ u → f ⟨$⟩ (map γ ⟨$⟩ (α ⟨$⟩ lift (proj₁ u) , lift (proj₂ u)))))
          })
          (λ {r} → Setoid.refl (Carrier (TQ X)) {kerPre γ m (α ⟨$⟩ r)})
      }
      where
        kerF : Func (RandomSource.Rˢ S) (Carrier (TQ X))
        kerF = record { to = kerPre γ m ; cong = λ { ≡.refl _ → Setoid.refl Aˢ } }

  discreteProbLaws : ProbLaws ℓ (ℛQ S) (cartesianClosed S) commutativeMonad
  discreteProbLaws = record
    { Measure = Σ (R → ∣A∣) Ok
    ; pushforward = λ m (μ , ok) → push (λ r → map m ⟨$⟩ r) μ , ok-push _ ok
    ; measure = lawH (idH S)
    ; measure-push = λ m (μ , ok) {_} g → Setoid.sym Aˢ (push-∑ (λ r → map m ⟨$⟩ r) μ (λ k → g ⟨$⟩ k))
    ; measure-total = λ (μ , ok) {pt} f →
        Setoid.sym Aˢ (Setoid.trans Aˢ (∫-η {1Q S} pt f)
          (Setoid.sym Aˢ (trans (sym (∑-distribʳ μ (f ⟨$⟩ pt)))
            (trans (*-cong ok refl) (*-identityˡ _)))))
    ; law-surjective = λ {X} t →
        let p = map t ⟨$⟩ tt
        in probe S (α-random p) , (μ p , μ-ok p) , (λ {pt} f → Setoid.refl Aˢ)
    }

  discreteProbFubini : Fubini ℓ (ℛQ S) (cartesianClosed S) commutativeMonad discreteProbLaws
  discreteProbFubini = record
    { split = record
        { from = record
            { map = record { to = Inverse.from cantorIso ; cong = λ { ≡.refl → ≡.refl , ≡.refl } }
            ; map-random = λ _ → rand-pair S {ℛQ S} {ℛQ S} (RandomSource.meas₀ S tt) (RandomSource.meas₀ S tt) }
        ; to = record
            { map = record { to = Inverse.to cantorIso ; cong = λ { (≡.refl , ≡.refl) → ≡.refl } }
            ; map-random = λ _ → RandomSource.meas₀ S tt }
        ; iso = record
            { isoˡ = λ {r} → proj₁ (Inverse.inverse cantorIso) {r} ≡.refl
            ; isoʳ = λ { {p} → let e = proj₂ (Inverse.inverse cantorIso) {p} ≡.refl
                               in ≡.cong proj₁ e , ≡.cong proj₂ e } }
        }
    ; tensor = λ (μ , okμ) (ν , okν) →
        tensorW μ ν
        , trans (cantor (λ a b → μ a * ν b))
            (trans (∑-prod μ ν) (trans (*-cong okμ okν) (*-identityˡ 1#)))
    ; measure-tensor = λ (μ , okμ) (ν , okν) {pt} f →
        Setoid.trans Aˢ (cantor (λ a b → (μ a * ν b) * (f ⟨$⟩ (a , b))))
          (Setoid.trans Aˢ (∑-cong (λ a → ∑-cong (λ b → *-assoc (μ a) (ν b) _)))
            (Setoid.trans Aˢ (∑-cong (λ a → ∑-scale (μ a) _))
              (Setoid.sym Aˢ (∫-join _ f))))
    }

  discreteProb : ProbabilityInterface ℓ (ℛQ S) (cartesianClosed S)
  discreteProb = record
    { commutativeMonad = commutativeMonad
    ; laws = discreteProbLaws
    ; fubini = discreteProbFubini
    }
