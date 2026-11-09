{-# OPTIONS --safe --without-K #-}

-- Statistical models as samplers, and the bridge to the frequentist layer (`plans/03-bayesian-frequentist.md`, "3c in
-- detail").  A sampler is a joint probe `Θ × ℛ ⇒ X`: a parameter and a stream of coin flips give an observation, which is how
-- a kernel `Θ ⇒ T X` is represented in this library (the fair coin supplies the measure).  For a bounded signed statistic g
-- (`Continuous/BoundedSignedTests`), the observations of an iid sample are `Xᵢ = g ∘ draw θ ∘ coordᵢ`, the coordinates of the coin
-- of `Continuous/CoinCoords`.  The moments of the iid experiment (`Inference/Frequentist.Moments`) then follow from the
-- moments of a single draw, so the unbiasedness theorems of the frequentist layer hold for every sampler.
--
-- Also here: the kernel `Θ ⇒ T X` induced by a sampler, whose expectation of a statistic is that of the single draw
-- (`E-at`, `Inference/ExpectationResp`, which also shows that it respects the equality of measures).
--
-- Checking time: declaring a `record` in this module (the single-draw moments, or `Model`) costs seconds to gigabytes of
-- memory, so `SingleMoments` is a pair of dependent functions and `Model` a synonym for `Hom Θ (TQ X)`.
module QBS.Inference.Sampler where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as Id
open import Data.Product.Function.NonDependent.Setoid using (_×-function_)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡
open import QBS.Classical using (LEM₁)

open import QBS.Core
open import QBS.Limits using (_×Q_)
import QBS.Probes as Probes
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Variance using (module Variance)
open import QBS.Analysis.BoundedRing using (module BoundedRing)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.CoinIndep using (module CoinIndep)
open import QBS.Continuous.CoinCoords using (module CoinCoords)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
open import QBS.Inference.Frequentist
import QBS.Inference.ExpectationResp as ER

module Sampler (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass; I-cong)
  open Tensor A (lemOf lem₁) using (constK)
  open RandomSource S using (Rˢ) renaming (meas-id to measId)
  open Continuous A (lemOf lem₁) probClass using (Pre; mk; TQ; _≈ᵖ_; Joint; sec-random; rand-irrel)
  open Pre
  open Bounded A using (Sg; _≃_; ≃-refl; ≃-trans; _+S_; _*S_; *S-cong)
  open SignedIntegral (lemOf lem₁) using (E; E-cong)
  open Variance (lemOf lem₁) using (_*SF_[_])
  open BoundedRing (lemOf lem₁) using (BSF; boundedRing; E-B)
  open BoundedSignedTests (lemOf lem₁) using (STest; pullback)
  open CoinCoords lem₁ using (coordSF; coordSF-bdd; E-coord; E-indep)
  open CoinIndep lem₁ using (fairCoin-prob)
  open FairCoin lem₁ using (fairCoin)
  module F = Frequentist lem₁
  open ER.ExpectationResp lem₁ using (E-at)

  open CommutativeRing (boundedRing fairCoin fairCoin-prob) using () renaming (_*_ to _*B_)

  ----------------------------------------------------------------------------
  -- samplers

  -- a randomised data-generating process: parameter and coin flips give an observation
  Sampler : QBS S → QBS S → Set₁
  Sampler Θ X = Hom S (_×Q_ S Θ (Probes.ℛQ S)) X

  -- the draw at a parameter, as a function of the coin flips, and its randomness
  -- the parameter and the coin flips, as a function of the coin flips
  at-θ : ∀ {Θ} → QBS.∣ Θ ∣ → Func Rˢ (QBS.Carrier (_×Q_ S Θ (Probes.ℛQ S)))
  at-θ {Θ} θ = record { to = λ r → θ , r ; cong = λ e → Setoid.refl (QBS.Carrier Θ) , e }

  draw : ∀ {Θ X} → Sampler Θ X → QBS.∣ Θ ∣ → Func Rˢ (QBS.Carrier X)
  draw {Θ} s θ = Hom.map s ∘ₛ at-θ θ

  draw-random : ∀ {Θ X} (s : Sampler Θ X) θ → QBS.Random X (draw s θ)
  draw-random {Θ} s θ = Hom.map-random s {at-θ θ} (QBS.const-random Θ θ , measId)

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
    MeanAt SecondAt : QBS.∣ Θ ∣ → Set₁
    MeanAt θ = E-B fairCoin fairCoin-prob (single s g θ) ≃ μ θ
    SecondAt θ = E-B fairCoin fairCoin-prob (single s g θ *B single s g θ) ≃ σ² θ +S (μ θ *S μ θ)

    -- a pair, not a record: with a record here Agda exhausts 3 GB (see the header)
    SingleMoments : Set₁
    SingleMoments = (∀ θ → MeanAt θ) × (∀ θ → SecondAt θ)

    -- the iid sample has the moments the frequentist layer asks for: the mean and second moment of each coordinate
    -- (`CoinCoords.E-coord`, the coordinates are measure preserving) and uncorrelatedness (`CoinCoords.E-indep`)
    iid-moments : SingleMoments → F.Moments (iidExperiment s g) μ σ²
    iid-moments sm θ = record
      { mean = λ i → ≃-trans {E (coordSF i f)} {E f} {μ θ} (E-coord i f) (proj₁ sm θ)
      ; second = λ i → ≃-trans {E (coordSF i f *SF coordSF i f [ coordSF-bdd i f bf ])}
          {E (f *SF f [ bf ])} {σ² θ +S (μ θ *S μ θ)}
          (≃-trans {_} {E (coordSF i (f *SF f [ bf ]))} {_}
            (E-cong {fairCoin} {coordSF i f *SF coordSF i f [ coordSF-bdd i f bf ]} {coordSF i (f *SF f [ bf ])}
              (λ x → OmegaSemiring.refl A))
            (E-coord i (f *SF f [ bf ])))
          (proj₂ sm θ)
      ; uncorr = λ i j h → ≃-trans {_} {E f *S E f} {μ θ *S μ θ} (E-indep i j h f f bf)
          (*S-cong {E f} {μ θ} {E f} {μ θ} (proj₁ sm θ) (proj₁ sm θ))
      }
      where
      f = proj₁ (single s g θ)
      bf = proj₂ (single s g θ)

    -- Sₙ / n is unbiased for μ, and (n Qₙ − Sₙ²) / (n² − n) for σ², for every sampler with these single-draw moments
    sampler-mean-unbiased : (sm : SingleMoments) → ∀ n →
      F.ScaledUnbiased (iidExperiment s g) (λ _ → F.natS n) μ (sumT n)
    sampler-mean-unbiased sm = F.sample-mean-unbiased (iid-moments sm)

  ----------------------------------------------------------------------------
  -- the kernel of a sampler, and expectation under the monad

  -- a statistical model: a kernel from parameters to measures on the data space
  Model : QBS S → QBS S → Set₁
  Model Θ X = Hom S Θ (TQ X)

  lawAt : ∀ {Θ X} → Model Θ X → QBS.∣ Θ ∣ → Pre X
  lawAt M θ = Hom.map M ⟨$⟩ θ

  -- the model of a sampler: θ ↦ [draw θ, fair coin]; it is a morphism because (θ , r) ↦ draw is a joint probe
  samplerModel : ∀ {Θ X} → Sampler Θ X → Model Θ X
  samplerModel {Θ} {X} s = record
    { map = record
        { to = λ θ → mk (draw s θ) (draw-random s θ) fairCoin fairCoin-prob
        ; cong = λ {θ} {θ′} e f → I-cong fairCoin
            (λ r → Func.cong (Hom.map f) (Func.cong (Hom.map s) (e , Setoid.refl (QBS.Carrier (Probes.ℛQ S)))))
            (Hom.map-random f (draw-random s θ)) (Hom.map-random f (draw-random s θ′)) }
    ; map-random = λ {γ} rγ → record
        { a = joint rγ ; g = λ _ → fairCoin ; g-ok = constK fairCoin ; g-pr = λ _ → fairCoin-prob
        ; w-eq = λ r → rand-irrel {X} (draw-random s (γ ⟨$⟩ r))
            (QBS.random-resp X (λ t → Setoid.refl (QBS.Carrier X)) (sec-random {X} (joint rγ) r)) fairCoin fairCoin-prob } }
    where
    -- (r , t) ↦ draw (γ r) t, a joint probe because γ is random
    joint : ∀ {γ} → QBS.Random Θ γ → Joint X
    joint {γ} rγ = record
      { map = Hom.map s ∘ₛ (γ ×-function Id.function Rˢ)
      ; map-random = λ {δ} (m₁ , m₂) →
          Hom.map-random s {(γ ×-function Id.function Rˢ) ∘ₛ δ} (QBS.pre-random Θ rγ m₁ , m₂)
      }

  -- for the model of a sampler it is the expectation of the single draw
  E-at-sampler : ∀ {Θ X} (s : Sampler Θ X) (g : STest X) θ →
    E-at (lawAt (samplerModel s) θ) g ≃ E-B fairCoin fairCoin-prob (single s g θ)
  E-at-sampler s g θ = ≃-refl
