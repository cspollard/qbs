{-# OPTIONS --safe --without-K #-}

-- Statistical models as samplers, and the bridge to the frequentist layer (`plans/03-bayesian-frequentist.md`, "3c in
-- detail").  A sampler is a joint probe `Θ × ℛ ⇒ X`: a parameter and a stream of coin flips give an observation, which is how
-- a kernel `Θ ⇒ T X` is represented in this library (the fair coin supplies the measure).  For a bounded signed statistic g
-- (`Continuous/SignedTests`), the observations of an iid sample are `Xᵢ = g ∘ draw θ ∘ coordᵢ`, the coordinates of the coin
-- of `Continuous/CoinCoords`.  The moments of the iid experiment (`Inference/Frequentist.Moments`) then follow from the
-- moments of a single draw, so the unbiasedness theorems of the frequentist layer hold for every sampler.
--
-- Also here: the kernel `Θ ⇒ T X` induced by a sampler, and the expectation of a statistic under a measure of the monad.
--
-- SKELETON: the declarations are in place; the proofs marked by holes are the plan's next steps.
module QBS.Inference.Sampler where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
import Level as L
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Limits using (_×Q_)
import QBS.Probes as Probes
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.CoinIndep using (module CoinIndep)
open import QBS.Continuous.CoinCoords using (module CoinCoords)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Inference.Frequentist

module Sampler (lem₁ : ∀ (P : Set₁) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass; I-cong)
  open Tensor A (lemOf lem₁) using (constK)
  open RandomSource S using () renaming (meas-id to measId)
  open Continuous A (lemOf lem₁) funext probClass using (Pre; mk; TQ; _≈ᵖ_; Joint; sec-random; rand-irrel)
  open Pre
  open Bounded A using (Sg; _≃_; ≃-refl; _+S_; _*S_)
  open SignedIntegral (lemOf lem₁) using (E)
  open BoundedRing (lemOf lem₁) using (BSF; boundedRing; E-B)
  open SignedTests (lemOf lem₁) using (STest; pullback)
  open CoinCoords lem₁ funext using (coordSF; coordSF-bdd)
  open CoinIndep lem₁ using (fairCoin-prob)
  open FairCoin lem₁ using (fairCoin)
  module F = Frequentist lem₁

  open CommutativeRing (boundedRing fairCoin fairCoin-prob) using () renaming (_*_ to _*B_)

  ----------------------------------------------------------------------------
  -- samplers

  -- a randomised data-generating process: parameter and coin flips give an observation
  Sampler : QBS S → QBS S → Set₁
  Sampler Θ X = Hom S (_×Q_ S Θ (Probes.ℛQ S)) X

  -- the draw at a parameter, as a function of the coin flips, and its randomness
  draw : ∀ {Θ X} → Sampler Θ X → QBS.∣ Θ ∣ → R₁ → QBS.∣ X ∣
  draw s θ r = Hom.map s ⟨$⟩ (θ , r)

  draw-random : ∀ {Θ X} (s : Sampler Θ X) θ → QBS.Random X (draw s θ)
  draw-random {Θ} s θ = Hom.map-random s {λ r → θ , r} (QBS.const-random Θ θ , measId)

  -- the statistic of one draw, a bounded signed random variable on the fair coin
  single : ∀ {Θ X} → Sampler Θ X → STest X → QBS.∣ Θ ∣ → BSF fairCoin fairCoin-prob
  single s g θ = pullback g (draw-random s θ) fairCoin fairCoin-prob

  -- the i-th draw of an iid sample: the same draw, read off the i-th coordinate of the coin
  obsAt : ∀ {Θ X} → Sampler Θ X → STest X → QBS.∣ Θ ∣ → ℕ → BSF fairCoin fairCoin-prob
  obsAt s g θ i = coordSF i (proj₁ b) , coordSF-bdd i (proj₁ b) (proj₂ b)
    where b = single s g θ

  -- the iid experiment of a sampler and a statistic, one probability space (the coin) for all parameters
  iidExperiment : ∀ {Θ X} → Sampler Θ X → STest X → F.Experiment QBS.∣ Θ ∣
  iidExperiment s g = record
    { space = λ _ → fairCoin
    ; prob = λ _ → fairCoin-prob
    ; obs = obsAt s g }

  ----------------------------------------------------------------------------
  -- moments of one draw, and of the iid sample

  module _ {Θ X} (s : Sampler Θ X) (g : STest X) (μ σ² : QBS.∣ Θ ∣ → Sg) where
    -- E g = μ and E g² = σ² + μ², for a single draw at every parameter
    record SingleMoments : Set₂ where
      field
        mean : ∀ θ → E-B fairCoin fairCoin-prob (single s g θ) ≃ μ θ
        second : ∀ θ → E-B fairCoin fairCoin-prob (single s g θ *B single s g θ)
                         ≃ σ² θ +S (μ θ *S μ θ)

    -- the iid sample has the moments the frequentist layer asks for: the mean and second moment of each coordinate
    -- (`CoinCoords.E-coord`, the coordinates are measure preserving) and uncorrelatedness (`CoinCoords.E-indep`)
    iid-moments : SingleMoments → F.Moments (iidExperiment s g) μ σ²
    iid-moments sm = ?

    -- Sₙ / n is unbiased for μ, and (n Qₙ − Sₙ²) / (n² − n) for σ², for every sampler with these single-draw moments
    sampler-mean-unbiased : (sm : SingleMoments) → ∀ n →
      F.ScaledUnbiased (iidExperiment s g) (λ _ → F.natS (iid-moments sm) n) μ (sumT n)
    sampler-mean-unbiased sm = F.sample-mean-unbiased (iid-moments sm)

  ----------------------------------------------------------------------------
  -- the kernel of a sampler, and expectation under the monad

  -- a statistical model: a kernel from parameters to measures on the data space
  record Model (Θ X : QBS S) : Set₂ where
    field kernel : Hom S Θ (TQ X)

  lawAt : ∀ {Θ X} → Model Θ X → QBS.∣ Θ ∣ → Pre X
  lawAt M θ = Hom.map (Model.kernel M) ⟨$⟩ θ

  -- the model of a sampler: θ ↦ [draw θ, fair coin]; it is a morphism because (θ , r) ↦ draw is a joint probe
  samplerModel : ∀ {Θ X} → Sampler Θ X → Model Θ X
  samplerModel {Θ} {X} s = record { kernel = record
    { map = record
        { to = λ θ → mk (draw s θ) (draw-random s θ) fairCoin fairCoin-prob
        ; cong = λ {θ} {θ′} e f → I-cong fairCoin
            (λ r → Func.cong (Hom.map f) (Func.cong (Hom.map s) (e , Setoid.refl (QBS.Carrier (Probes.ℛQ S)))))
            (Hom.map-random f (draw-random s θ)) (Hom.map-random f (draw-random s θ′)) }
    ; map-random = λ {γ} rγ → record
        { a = joint rγ ; g = λ _ → fairCoin ; g-ok = constK fairCoin ; g-pr = λ _ → fairCoin-prob
        ; w-eq = λ r → rand-irrel {X} (draw-random s (γ r)) (sec-random {X} (joint rγ) r) fairCoin fairCoin-prob } } }
    where
    -- (r , t) ↦ draw (γ r) t, a joint probe because γ is random
    joint : ∀ {γ} → QBS.Random Θ γ → Joint X
    joint {γ} rγ = record
      { map = record { to = λ p → Hom.map s ⟨$⟩ (γ (proj₁ p) , proj₂ p)
                     ; cong = λ { (≡.refl , ≡.refl) → Func.cong (Hom.map s) (Setoid.refl (QBS.Carrier Θ) , ≡.refl) } }
      ; map-random = λ {δ} (m₁ , m₂) → Hom.map-random s {λ x → γ (proj₁ (δ x)) , proj₂ (δ x)} (QBS.pre-random Θ rγ m₁ , m₂)
      }

  -- the expectation of a bounded signed statistic under a measure of the monad
  E-at : ∀ {X} → Pre X → STest X → Sg
  E-at p g = E (proj₁ (pullback g (α p) (m p) (ok p)))

  -- for the model of a sampler it is the expectation of the single draw
  E-at-sampler : ∀ {Θ X} (s : Sampler Θ X) (g : STest X) θ →
    E-at (lawAt (samplerModel s) θ) g ≃ E-B fairCoin fairCoin-prob (single s g θ)
  E-at-sampler s g θ = ≃-refl

  -- the expectation respects the identification of measures by [0,1]-tests (truncate at n and use monotone convergence)
  E-resp : ∀ {X} {p q : Pre X} → p ≈ᵖ q → (g : STest X) → E-at p g ≃ E-at q g
  E-resp e g = ?
