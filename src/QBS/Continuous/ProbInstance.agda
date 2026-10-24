{-# OPTIONS --safe --without-K #-}

-- The continuous probability monad over Cantor space is a model of `ProbabilityInterface`.
module QBS.Continuous.ProbInstance where

open import Level using (Lift; lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe; unprobe)
open import QBS.Probability
open import QBS.Borel.Core
open import QBS.Borel.Source
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Indicators
open import QBS.Analysis.Tensor
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong

module ContinuousProb (A : OmegaSemiring (L.suc L.zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥))
                      (funext : Extensionality L.zero L.zero) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Tensor A lem
  open Indicators A lem using (I-const)
  open Split funext
  open Continuous A lem funext probClass
  open Strength A lem funext probClass using (strongMonad; commutative)
  open QBS
  open Hom
  open Pre
  open Wit

  private
    -- the law of a probe under a measure
    PM : Set₁
    PM = Σ Measure IsProb

    lawP : ∀ {X : QBS S} → Hom S (ℛQ S) X → PM → Pre X
    lawP a (μ , pμ) = mk (λ r → map a ⟨$⟩ r) (unprobe S a) μ pμ

    lawH : ∀ {X : QBS S} → Hom S (ℛQ S) X → PM → Hom S (1Q S) (TQ X)
    lawH {X} a μ = record
      { map = record { to = λ _ → lawP a μ ; cong = λ _ _ → Setoid.refl Aˢ }
      ; map-random = λ _ → QBS.const-random (TQ X) (lawP a μ)
      }

    kerPre : ∀ {X : QBS S} → Joint X → PM → R → Pre X
    kerPre γ (ν , pν) r = mk (sec γ r) (sec-random γ r) ν pν

    kerH : ∀ {X : QBS S} → Joint X → PM → Hom S (ℛQ S) (TQ X)
    kerH {X} γ νp@(ν , pν) = record
      { map = record { to = kerPre γ νp ; cong = λ { ≡.refl _ → Setoid.refl Aˢ } }
      ; map-random = λ {β} mβ → record
          { a = _∘H_ S γ (pairH β mβ)
          ; g = λ _ → ν
          ; g-ok = constK ν
          ; g-pr = λ _ → pν
          ; w-eq = λ r f → I-cong ν (λ s → Setoid.refl Aˢ) _ _
          }
      }
      where
        pairH : ∀ (β : R → R) → Measurable (down β) → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) (_×Q_ S (ℛQ S) (ℛQ S))
        pairH β mβ = record
          { map = record { to = λ p → β (proj₁ p) , proj₂ p ; cong = λ { (≡.refl , ≡.refl) → ≡.refl , ≡.refl } }
          ; map-random = λ {γ′} (m₁ , m₂) → measurable-∘ m₁ mβ , m₂
          }

  continuousProb : ProbabilityInterface (L.suc L.zero) (QBSCat S) (ℛQ S) (cartesianClosed S)
  continuousProb = record
    { commutativeMonad = record { strongMonad = strongMonad ; commutative = commutative }
    ; Measure = PM
    ; pushforward = λ m (μ , pμ) → push {λ r → map m ⟨$⟩ r} (map-random m (RandomSource.meas-id S)) μ
        , IsProb-push {λ r → map m ⟨$⟩ r} (map-random m (RandomSource.meas-id S)) {μ} pμ
    ; law = lawH
    ; law-resp = λ e (μ , _) _ f → I-cong μ (λ r → Func.cong (map f) (e r)) _ _
    ; law-map = λ f a (μ , _) _ g → I-cong μ (λ r → Setoid.refl Aˢ) _ _
    ; law-pre = λ a m (μ , _) _ g → I-cong μ (λ r → Setoid.refl Aˢ) _ _
    ; law-return = λ {X} x (μ , pμ) pt f →
        let c = proj₁ (map f ⟨$⟩ (map x ⟨$⟩ pt))
            c≤1 = proj₂ (map f ⟨$⟩ (map x ⟨$⟩ pt))
        in Setoid.sym Aˢ (Setoid.trans Aˢ (I-cong μ (λ _ → Setoid.refl Aˢ) _ (Fun-const c c≤1)) (I-const μ pμ c c≤1))
    ; law-surjective = λ {X} t →
        let p = map t ⟨$⟩ _
        in probe S (α-random p) , (m p , ok p) , (λ pt f → I-cong (m p) (λ r → Setoid.refl Aˢ) _ _)
    ; split = record
        { from = fromH
        ; to = toH
        ; iso = record
            { isoˡ = split-merge
            ; isoʳ = λ { (r₁ , r₂) → merge-evens r₁ r₂ , merge-odds r₁ r₂ } }
        }
    ; tensor = λ (μ , pμ) (ν , pν) → tensor₁ μ ν , IsProb-tensor₁ μ ν pμ pν
    ; kernel = kerH
    ; kernel-law = λ γ (ν , _) r _ f → I-cong ν (λ s → Setoid.refl Aˢ) _ _
    ; law-join = λ {X} γ μp@(μ , _) νp@(ν , _) _ f →
        Setoid.trans Aˢ (∫-join {X} (lawP (kerH γ νp) μp) f)
          (I-cong μ (λ r → I-cong ν (λ s → Func.cong (map f) (Func.cong (map γ)
              (Setoid.sym (Carrier (ℛQ S)) (merge-evens r s) , Setoid.sym (Carrier (ℛQ S)) (merge-odds r s)))) _ _) _ _)
    }

  open import QBS.IsQBSLike using (IsQBSLike)
  open import QBS.Instance using (isQBSLike)

  -- quasi-Borel spaces over Cantor space, with the Daniell probability monad, are QBS-like
  continuousQBSLike : IsQBSLike (L.suc L.zero) (QBSCat S)
  continuousQBSLike = isQBSLike S continuousProb
