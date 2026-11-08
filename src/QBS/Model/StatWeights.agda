{-# OPTIONS --safe --without-K #-}

-- Weights, inclusion, score and countable sums of the discrete model: the weights object `WQ`, the
-- inclusion of probability measures into all measures (`inclusion`), `scoreE` and the countable sums `sumKH`.
-- First of three parts of the `StatisticalInterface` instance (then `StatNormalize`, `StatInstance`).
module QBS.Model.StatWeights where

open import Level using (Lift; lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (tt)
import Data.Sum.Relation.Binary.Pointwise as ⊎ʳ
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Function.Construct.Composition as Comp

open import Categories.Monad.Morphism using (Monad⇒-id)
import Categories.Monad.Strong as CMS
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
open import Categories.NaturalTransformation using (NaturalTransformation)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; CodiscQ)
open import QBS.Probability
open import QBS.Statistical
open import QBS.Model.Pairing
open import QBS.Model.DiscreteSource
open import QBS.Model.Semiring
open import QBS.Model.Sums
open import QBS.Model.Monad
open import QBS.Model.WeightClasses
open import QBS.Model.Strong
open import QBS.Model.ProbInstance
open import QBS.Model.Cantor

module StatWeights {ℓ} (N : NormalizableSemiring ℓ) where
  A = NormalizableSemiring.complete N
  open CompleteSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Sums A
  private
    open DS ℓ using (S)
    R = Lift ℓ ℕ
  open Cantor A
  module MA = Measures A (allClass A)
  module MP = Measures A (probClass A)
  open QBS
  open Hom

  -- The weights object: A itself, with every function random.
  WQ : QBS S
  WQ = CodiscQ S Aˢ

  mulH : Hom S (_×Q_ S WQ WQ) WQ
  mulH = record
    { map = record { to = λ p → proj₁ p * proj₂ p ; cong = λ { (e₁ , e₂) → *-cong e₁ e₂ } }
    ; map-random = λ _ → tt
    }

  constH : ∣A∣ → Hom S (1Q S) WQ
  constH a = record
    { map = record { to = λ _ → a ; cong = λ _ → Setoid.refl Aˢ }
    ; map-random = λ _ → tt
    }

  ----------------------------------------------------------------------------
  -- Prob ⊆ M

  forgetPre : ∀ {X : QBS S} → MP.Pre X → MA.Pre X
  forgetPre p = MA.mk (MP.Pre.αₛ p) (MP.Pre.α-random p) (MP.Pre.μ p) tt

  inclH : ∀ X → Hom S (MP.TQ X) (MA.TQ X)
  inclH X = record
    { map = record { to = forgetPre ; cong = λ e f → e f }
    ; map-random = λ {β} w → record
        { wαₛ = MP.Wit.wαₛ w
        ; wα-random = MP.Wit.wα-random w
        ; wg = MP.Wit.wg w
        ; wg-ok = λ _ → tt
        ; w-eq = λ r f → MP.Wit.w-eq w r f
        }
    }

  inclN : NaturalTransformation MP.TF MA.TF
  inclN = record
    { η = inclH
    ; commute = λ _ {_} _ → Setoid.refl Aˢ
    ; sym-commute = λ _ {_} _ → Setoid.refl Aˢ
    }

  inclusion : Monad⇒-id MA.TM MP.TM
  inclusion = record
    { α = inclN
    ; unit-comp = λ {_} {_} _ → Setoid.refl Aˢ
    ; mult-comp = λ {U} {p} f →
        Setoid.trans Aˢ (MP.∫-join p f)
          (Setoid.sym Aˢ (MA.∫-join (forgetPre (MP.mapPre (inclH U) p)) f))
    }

  ----------------------------------------------------------------------------
  -- zero, score, scaling and countable sums on the measure monad M

  private
    r₀ : R
    r₀ = lift 0

  open MA using (Pre; mk; α; ∫; ∫ᶠ; mapPre; ηPre; joinPre; ∫-η; ∫-join; TQ; TH; TM; TF)
  open MA.Pre

  -- constant elements ⊤ ⇒ M X
  constE : ∀ {X : QBS S} → Pre X → Hom S (1Q S) (TQ X)
  constE {X} p = record
    { map = record { to = λ _ → p ; cong = λ _ _ → Setoid.refl Aˢ }
    ; map-random = λ _ → QBS.const-random (TQ X) p
    }

  zeroP : Pre (1Q S)
  zeroP = mk (constₛ tt) tt (λ _ → 0#) tt

  ∫-zero : ∀ f → ∫ zeroP f ≈ 0#
  ∫-zero f = ∑-zero _ (λ _ → zeroˡ _)

  scoreP : ∣A∣ → Pre (1Q S)
  scoreP a = mk (constₛ tt) tt (λ r → a * dirac r₀ r) tt

  weight-sum : ∀ a c → ∑ (λ r → (a * dirac r₀ r) * c) ≈ a * c
  weight-sum a c = begin
    ∑ (λ r → (a * dirac r₀ r) * c)    ≈⟨ ∑-cong (λ r → *-assoc a (dirac r₀ r) c) ⟩
    ∑ (λ r → a * (dirac r₀ r * c))    ≈⟨ ∑-scale a (λ r → dirac r₀ r * c) ⟩
    a * ∑ (λ r → dirac r₀ r * c)      ≈⟨ *-cong refl (dirac-∑ r₀ (λ _ → c)) ⟩
    a * c                              ∎
    where open SetoidReasoning Aˢ

  ∫-score : ∀ a f → ∫ (scoreP a) f ≈ a * (f ⟨$⟩ tt)
  ∫-score a f = weight-sum a (f ⟨$⟩ tt)

  scoreE : Hom S WQ (TQ (1Q S))
  scoreE = record
    { map = record
        { to = scoreP
        ; cong = λ e f → ∑-cong (λ r → *-cong (*-cong e refl) refl)
        }
    ; map-random = λ {α} _ → record
        { wαₛ = constₛ tt
        ; wα-random = tt
        ; wg = λ r k → (α ⟨$⟩ r) * dirac r₀ k
        ; wg-ok = λ _ → tt
        ; w-eq = λ r f → Setoid.refl Aˢ
        }
    }

  scaleP : ∀ {X : QBS S} → ∣A∣ → Pre X → Pre X
  scaleP c p = mk (αₛ p) (α-random p) (λ r → c * μ p r) tt

  ∫-scale : ∀ {X : QBS S} (c : ∣A∣) (p : Pre X) f → ∫ (scaleP c p) f ≈ c * ∫ p f
  ∫-scale c p f = begin
    ∑ (λ r → (c * μ p r) * z r)    ≈⟨ ∑-cong (λ r → *-assoc c (μ p r) (z r)) ⟩
    ∑ (λ r → c * (μ p r * z r))    ≈⟨ ∑-scale c (λ r → μ p r * z r) ⟩
    c * ∑ (λ r → μ p r * z r)      ∎
    where open SetoidReasoning Aˢ
          z = λ r → f ⟨$⟩ α p r

  scaleE : ∀ {X : QBS S} → Hom S (1Q S) WQ → Hom S (1Q S) (TQ X) → Hom S (1Q S) (TQ X)
  scaleE a t = constE (scaleP (map a ⟨$⟩ tt) (map t ⟨$⟩ tt))

  -- countable sums of measures: glue the probes through the Cantor pairing
  sumP : ∀ {X : QBS S} → (ℕ → Pre X) → Pre X
  sumP {X} t = mk (glueₛ (⇑ℕ (λ k → lower (ιR k))) (λ n → αₛ (t n) ∘ₛ ⇑ ρR))
    (QBS.glue-random X {⇑ℕ (λ k → lower (ιR k))} tt (λ n → αₛ (t n) ∘ₛ ⇑ ρR)
      (λ n → QBS.pre-random X (α-random (t n)) tt))
    (λ k → μ (t (lower (ιR k))) (ρR k)) tt

  ∫-sum : ∀ {X : QBS S} (t : ℕ → Pre X) f →
    ∫ (sumP t) f ≈ ∑ (λ (n : R) → ∫ (t (lower n)) f)
  ∫-sum {X} t f = cantor (λ n m → μ (t (lower n)) m * (f ⟨$⟩ α (t (lower n)) m))

  sumE : ∀ {X : QBS S} → (ℕ → Hom S (1Q S) (TQ X)) → Hom S (1Q S) (TQ X)
  sumE ts = constE (sumP (λ n → map (ts n) ⟨$⟩ tt))

  -- countable sums of kernels: pointwise sums of measures, the witnesses glued through the pairing
  sumKH : ∀ {X Y : QBS S} → (ℕ → Hom S X (TQ Y)) → Hom S X (TQ Y)
  sumKH {X} {Y} ks = record
    { map = record
        { to = λ x → sumP (λ n → map (ks n) ⟨$⟩ x)
        ; cong = λ {x} {y} e f →
            Setoid.trans Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ x) f)
              (Setoid.trans Aˢ (∑-cong (λ n → Func.cong (map (ks (lower n))) e f))
                (Setoid.sym Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ y) f)))
        }
    ; map-random = λ {β} rβ →
        let w = λ n → map-random (ks n) rβ
            t′ = λ (r : R) (n : ℕ) → mk {Y} (MA.Wit.wαₛ (w n)) (MA.Wit.wα-random (w n)) (MA.Wit.wg (w n) r) tt
        in record
          { wαₛ = αₛ (sumP (t′ r₀))
          ; wα-random = α-random (sumP (t′ r₀))
          ; wg = λ r → μ (sumP (t′ r))
          ; wg-ok = λ _ → tt
          ; w-eq = λ r f →
              Setoid.trans Aˢ (∫-sum (λ n → map (ks n) ⟨$⟩ (β ⟨$⟩ r)) f)
                (Setoid.trans Aˢ (∑-cong (λ n → MA.Wit.w-eq (w (lower n)) r f))
                  (Setoid.sym Aˢ (∫-sum (t′ r) f)))
          }
    }

