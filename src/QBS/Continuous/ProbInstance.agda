{-# OPTIONS --safe --without-K #-}

-- The continuous probability monad over Cantor space is a model of `ProbabilityInterface`.
module QBS.Continuous.ProbInstance where

import Level as L
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_)
import Function.Construct.Identity as Id
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
import Categories.Category.SubCategory.SubHom as SH
open import Categories.Category.Instance.Setoids using (Setoids)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; pairQ; fstQ; sndQ)
open import QBS.Exponential using (cartesianClosed)
open import QBS.Probes using (ℛQ; probe; unprobe)
open import QBS.CommMonad using (ProbMonad)
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
open import QBS.Continuous.Commutative using (module Commutativity)
open import QBS.Classical using (LEM₀)

module ContinuousProb (A : OmegaSemiring (L.suc L.zero)) (lem : LEM₀) where
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Measurable A
  open Integration A
  open Tensor A lem
  open Indicators A lem using (I-const)
  open Continuous A lem probClass
  open Strength A lem probClass using (strongMonad; ∫-σ; fixH)
  open Commutativity A lem probClass using (commutative; ψ-join)
  open QBS
  open Hom
  open Wit
  open RandomSource S using (Rˢ; Meas; meas-∘)

  open SH (Setoids (L.suc L.zero) (L.suc L.zero)) using () renaming (probe to mprobe; reads to mreads)

  private
    -- the two notions of measurable map agree (`Meas` is `Measurable` up to pointwise equality)
    Meas→Measurable : ∀ {f : Func Rˢ Rˢ} → Meas f → Measurable (down (f ⟨$⟩_))
    Meas→Measurable {f} m = measurable-ext (λ x → L.lower (mreads m {L.lift x})) (proj₂ (mprobe m))

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
      { map = record { to = kerPre γ νp ; cong = λ {x} {y} e f → via {X} {X} {kerPre γ νp x} {kerPre γ νp y}
          (I-cong ν (λ s → Func.cong (map f) (Func.cong (map γ) (e , R≈.refl))) _ _) }
      ; map-random = λ {β} mβ → rwit record
          { a = _∘H_ S γ (pairH β mβ)
          ; g = λ _ → ν
          ; g-ok = constK ν
          ; g-pr = λ _ → pν
          ; w-eq = λ r f → via {X} {X} (I-cong ν (λ s → Setoid.refl Aˢ) _ _)
          }
      }
      where
        pairH : ∀ (β : Func Rˢ Rˢ) → Meas β → Hom S (_×Q_ S (ℛQ S) (ℛQ S)) (_×Q_ S (ℛQ S) (ℛQ S))
        βH : ∀ (β : Func Rˢ Rˢ) → Meas β → Hom S (ℛQ S) (ℛQ S)
        βH β mβ = record { map = β ; map-random = λ m → meas-∘ mβ m }

        pairH β mβ = pairQ S {_×Q_ S (ℛQ S) (ℛQ S)} {ℛQ S} {ℛQ S}
          (_∘H_ S (βH β mβ) (fstQ S {ℛQ S} {ℛQ S})) (sndQ S {ℛQ S} {ℛQ S})

  continuousMonad : ProbMonad (cartesianClosed S)
  continuousMonad = record { strongMonad = strongMonad ; commutative = commutative }

  continuousProbLaws : ProbLaws (L.suc L.zero) (ℛQ S) (cartesianClosed S) continuousMonad
  continuousProbLaws = record
    { Measure = PM
    ; pushforward = λ m (μ , pμ) → push {λ r → map m ⟨$⟩ r} (Meas→Measurable (unprobe S m)) μ
        , IsProb-push {λ r → map m ⟨$⟩ r} (Meas→Measurable (unprobe S m)) {μ} pμ
    ; measure = lawH (idH S)
    ; measure-push = λ m (μ , _) {_} g → via (I-cong μ (λ r → Setoid.refl Aˢ) _ _)
    ; measure-total = λ (μ , pμ) {pt} f →
        let c = proj₁ (map f ⟨$⟩ pt)
            c≤1 = proj₂ (map f ⟨$⟩ pt)
        in Setoid.trans Aˢ (Setoid.trans Aˢ (∫-unfold _ f) (I-cong μ (λ _ → Setoid.refl Aˢ) _ (Fun-const c c≤1))) (Setoid.trans Aˢ (I-const μ pμ c c≤1) (Setoid.sym Aˢ (∫-unfold {1Q S} (ηPre {1Q S} pt) f)))
    ; law-surjective = λ {X} t →
        let p = map t ⟨$⟩ _
        in probe S {α = α p} (α-random p) , (m p , ok p) , (λ {pt} f → via (I-cong (m p) (λ r → Setoid.refl Aˢ) _ _))
    }

  continuousProbFubini : Fubini (L.suc L.zero) (ℛQ S) (cartesianClosed S) continuousMonad continuousProbLaws
  continuousProbFubini = record
    { split = record
        { from = fromH
        ; to = toH
        ; iso = record
            { isoˡ = λ {x} → split-merge x
            ; isoʳ = λ { {r₁ , r₂} → merge-evens r₁ r₂ , merge-odds r₁ r₂ } }
        }
    ; tensor = λ (μ , pμ) (ν , pν) → tensor₁ μ ν , IsProb-tensor₁ μ ν pμ pν
    ; measure-tensor = λ μp@(μ , _) νp@(ν , _) {pt} f →
        let P = lawP (kerH (idH S) νp) μp
            s = lawP (idH S) μp
            t = lawP (idH S) νp
            inner = λ r → Setoid.trans Aˢ (∫-σ {ℛQ S} {ℛQ S} (α s ⟨$⟩ r) t f)
              (Setoid.trans Aˢ (∫-unfold {ℛQ S} t (fixH {ℛQ S} {ℛQ S} (α s ⟨$⟩ r) f))
                (Setoid.trans Aˢ (I-cong ν (λ s′ → Setoid.refl Aˢ) _ _)
                  (Setoid.sym Aˢ (∫-unfold {_×Q_ S (ℛQ S) (ℛQ S)} (kerPre (idH S) νp r) f)))) in
        Setoid.trans Aˢ
          (Setoid.trans Aˢ (∫-unfold _ f)
            (Setoid.trans Aˢ
              (I-cong μ (λ r → Setoid.trans Aˢ
                (I-cong ν (λ s′ → Func.cong (map f) (merge-evens r s′ , merge-odds r s′)) _ _)
                (Setoid.sym Aˢ (∫-unfold _ f))) _ _)
              (Setoid.trans Aˢ (Setoid.sym Aˢ (∫-unfold {TQ _} P (∫ᶠ f)))
                (Setoid.sym Aˢ (∫-join {_×Q_ S (ℛQ S) (ℛQ S)} P f)))))
          (Setoid.sym Aˢ (Setoid.trans Aˢ (ψ-join {ℛQ S} {ℛQ S} (s , t) f) ?))
    }

  continuousProb : ProbabilityInterface (L.suc L.zero) (ℛQ S) (cartesianClosed S)
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
