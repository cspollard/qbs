{-# OPTIONS --safe --without-K #-}

-- The continuous probability monad over Cantor space is a model of `ProbabilityInterface`.
module QBS.Continuous.ProbInstance where

open import Level using (Lift; lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_)
import Function.Construct.Identity as Id
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡

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

module ContinuousProb (A : OmegaSemiring (L.suc L.zero)) (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Tensor A lem
  open Indicators A lem using (I-const)
  open Continuous A lem probClass
  open Strength A lem probClass using (strongMonad; commutative)
  open QBS
  open Hom
  open Pre
  open Wit
  open RandomSource S using (Rˢ; Meas)

  private
    -- the law of a probe under a measure
    PM : Set₁
    PM = Σ Measure IsProb

    lawP : ∀ {X : QBS S} → Hom S (ℛQ S) X → PM → Pre X
    lawP a (μ , pμ) = mk (map a) (unprobe S a) μ pμ

    lawH : ∀ {X : QBS S} → Hom S (ℛQ S) X → PM → Hom S (1Q S) (TQ X)
    lawH {X} a μ = record
      { map = record { to = λ _ → lawP a μ ; cong = λ _ _ → Setoid.refl Aˢ }
      ; map-random = λ _ → QBS.const-random (TQ X) (lawP a μ)
      }

    kerPre : ∀ {X : QBS S} → Joint X → PM → R → Pre X
    kerPre γ (ν , pν) r = mk (sec γ r) (sec-random γ r) ν pν

    kerH : ∀ {X : QBS S} → Joint X → PM → Hom S (ℛQ S) (TQ X)
    kerH {X} γ νp@(ν , pν) = record
      { map = record { to = kerPre γ νp ; cong = λ e f → I-cong ν (λ s → Func.cong (map f) (Func.cong (map γ) (e , R≈.refl))) _ _ }
      ; map-random = λ {β} mβ → record
          { a = _∘H_ S γ (pairH β mβ)
          ; g = λ _ → ν
          ; g-ok = constK ν
          ; g-pr = λ _ → pν
          ; w-eq = λ r f → I-cong ν (λ s → Setoid.refl Aˢ) _ _
          }
      }
      where
        pairH : ∀ (β : Func Rˢ Rˢ) → Meas β → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) (_×Q_ S (ℛQ S) (ℛQ S))
        pairH β mβ = record
          { map = β ×-function Id.function Rˢ
          ; map-random = λ {γ′} (m₁ , m₂) → measurable-∘ m₁ mβ , m₂
          }

  continuousMonad : ProbMonad (QBSCat S) (cartesianClosed S)
  continuousMonad = record { strongMonad = strongMonad ; commutative = commutative }

  continuousProbLaws : ProbLaws (L.suc L.zero) (QBSCat S) (ℛQ S) (cartesianClosed S) continuousMonad
  continuousProbLaws = record
    { Measure = PM
    ; pushforward = λ m (μ , pμ) → push {λ r → map m ⟨$⟩ r} (unprobe S m) μ
        , IsProb-push {λ r → map m ⟨$⟩ r} (unprobe S m) {μ} pμ
    ; measure = lawH (idH S)
    ; measure-push = λ m (μ , _) _ g → I-cong μ (λ r → Setoid.refl Aˢ) _ _
    ; measure-total = λ (μ , pμ) pt f →
        let c = proj₁ (map f ⟨$⟩ pt)
            c≤1 = proj₂ (map f ⟨$⟩ pt)
        in Setoid.trans Aˢ (I-cong μ (λ _ → Setoid.refl Aˢ) _ (Fun-const c c≤1)) (I-const μ pμ c c≤1)
    ; law-surjective = λ {X} t →
        let p = map t ⟨$⟩ _
        in probe S {α = α p} (α-random p) , (m p , ok p) , (λ pt f → I-cong (m p) (λ r → Setoid.refl Aˢ) _ _)
    }

  continuousProbFubini : Fubini (L.suc L.zero) (QBSCat S) (ℛQ S) (cartesianClosed S) continuousMonad continuousProbLaws
  continuousProbFubini = record
    { split = record
        { from = fromH
        ; to = toH
        ; iso = record
            { isoˡ = split-merge
            ; isoʳ = λ { (r₁ , r₂) → merge-evens r₁ r₂ , merge-odds r₁ r₂ } }
        }
    ; tensor = λ (μ , pμ) (ν , pν) → tensor₁ μ ν , IsProb-tensor₁ μ ν pμ pν
    ; measure-tensor = λ μp@(μ , _) νp@(ν , _) pt f →
        Setoid.trans Aˢ
          (I-cong μ (λ r → I-cong ν (λ s → Func.cong (map f)
              (merge-evens r s , merge-odds r s)) _ _) _ _)
          (Setoid.sym Aˢ (∫-join {_×Q_ S (ℛQ S) (ℛQ S)} (lawP (kerH (idH S) νp) μp) f))
    }

  continuousProb : ProbabilityInterface (L.suc L.zero) (QBSCat S) (ℛQ S) (cartesianClosed S)
  continuousProb = record
    { commutativeMonad = continuousMonad
    ; laws = continuousProbLaws
    ; fubini = continuousProbFubini
    }

  open import QBS.IsQBSLike using (IsQBSLike)
  open import QBS.Instance using (isQBSLike)

  -- quasi-Borel spaces over Cantor space, with the Daniell probability monad, are QBS-like
  continuousQBSLike : IsQBSLike (L.suc L.zero) (QBSCat S)
  continuousQBSLike = isQBSLike S continuousProb
