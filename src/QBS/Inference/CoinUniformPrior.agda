{-# OPTIONS --safe --without-K #-}

-- The coin with a continuous uniform prior on its bias: the Beta(1,1)-Bernoulli model (`plans/03-bayesian-frequentist.md`, 3c/3d).
--
--   * `coinKernel : Model AQ BoolQ`, θ ↦ `bernθ θ` (`Inference/BoolDist`): the sampler `(θ , r) ↦ [expansion r ≤ θ]` of the
--     uniform draw.  Its measurability in θ is the real content: for a random pair (θ(x), r(x)) the set
--     {x | expansion (r x) ≤ θ x} is Borel (`Below2-borel`, the variable-threshold version of `Analysis/Threshold`: the
--     complement of ⋃_q {q ∈ expansion (r x)} ∩ {q ∉ θ x}), so `indB-random` makes the indicator a random element of `BoolQ`;
--   * the marginal `marg = joinPre (mapPre coinKernel uniform)` has P(heads) = ∫ θ dθ = ½ (`E-at-marg`), from the tower law
--     `E-at-join`, `E-at-bernθ` and `E-at-uniform-id`.
--   * two flips conditionally independent given θ, `coinKernel² θ = coinKernel θ ⊗ coinKernel θ` (a morphism: strength, `TH`,
--     `joinH`), with `E-at (coinKernel² θ) (indT ⊗T indT) ≃ θ·θ`, hence under the uniform prior
--     P(HH) = ∫ θ² dθ = ⅓ (`E-at-marg²`, with `3m = 1` from `UniformMoment`).  The posterior mean after one head is
--     P(HH)/P(H) = ⅔, multiplied out `3·P(HH) = 2·P(H)` (`HH-from-H`).
--
-- Compare the discrete `Inference/CoinBias` and `Inference/BernoulliCompare` examples: there the prior is a two-point sum
-- ½·1 + ½·½; here the prior sum becomes the integral ∫ θ dθ against the uniform distribution, via the tower law.
module QBS.Inference.CoinUniformPrior where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂; Σ; _×_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lift)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; pairQ; fstQ; sndQ)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Pred; Borel; ⋃; compl; inter₂; resp; _≐_)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LowerReals using (Cut; _⊑_)
open import QBS.Analysis.LevelSets using (module LevelSets; enumQ; enumQ-surj)
open import QBS.Analysis.Threshold using (module Threshold)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.UniformMoment using (module UniformMoment)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.CoinIndep using (module CoinIndep)
import QBS.BoolQ as BQ
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.ExpectationProduct as EP
import QBS.Inference.ExpectationExamples as EE
import QBS.Inference.BoolDist as BD
import QBS.Inference.Sampler as SM
open BQ.BoolOn S
open _⊑_
open Cut

module CoinUniformPrior (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-irrel; J)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _+_; 0#; 1#; refl; sym; trans)
  open Bounded A using (Sg; Bnd; finite; _+S_; _*S_; *S-cong; *S-comm; ι-+; ι-*; +S-cong; _≃_; ≃-trans; ≃-sym; ≃-refl; ι; mk≃)
  open SignedTests (lemOf lem₁) using (CutQ; STest)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre; joinPre; TQ; _≈ᵖ_; TH; joinH)
  open Pre
  open Measurable A using (Fun; Fun-pre)
  open LevelSets (lemOf lem₁) using (LS)
  open Threshold (lemOf lem₁) using (Le)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open Expansion A half hh using (expansion; Fun-expansion)
  open Uniform lem₁ using (uniform; expansionProbe)
  open FairCoin lem₁ using (fairCoin)
  open CoinIndep lem₁ using (fairCoin-prob)
  open SM.Sampler lem₁ using (Sampler; Model; samplerModel; lawAt; draw)
  open ER.ExpectationResp lem₁ using (E-at)
  open EX.Expectation lem₁ using (valT; precompT; expT; E-at-join; E-at-map; E-at-expT)
  open EP.ExpectationProduct lem₁ using (E-at-cong; _⊗T_; E-at-σ)
  open Strength A (lemOf lem₁) probClass using (σPre; σH)
  open UniformMoment lem₁ using (m≤1; second-moment) renaming (m to m2)
  open EE.ExpectationExamples lem₁ using (idT; E-at-uniform-id; b1; E-at-ι; zeroJ; sqT; E-at-uniform-sq; ι-cong; fh)
  open BD.BoolDist lem₁ using (bernθ; indT; E-at-bernθ; J-indθ)
  open BD using (flag; flag-resp; indB; indB-random)

  ----------------------------------------------------------------------------
  -- the variable threshold {x | h x ≤ t x} is Borel

  Below2 : (R₁ → Cut) → (R₁ → Cut) → Pred
  Below2 h t c = Le (h (lift c)) (t (lift c))

  Below2-borel : ∀ {h t} → Fun h → Fun t → Borel (Below2 h t)
  Below2-borel {h} {t} fh ft = resp e (compl (⋃ cells))
    where
    lem = lemOf lem₁
    cells : ∀ k → Borel (λ c → mem (h (lift c)) (enumQ k) × (mem (t (lift c)) (enumQ k) → ⊥))
    cells k = inter₂ (LS fh (enumQ k)) (compl (LS ft (enumQ k)))

    fwd : ∀ x → ((Σ ℕ (λ k → mem (h (lift x)) (enumQ k) × (mem (t (lift x)) (enumQ k) → ⊥))) → ⊥) → Le (h (lift x)) (t (lift x))
    fwd x nex q mq with lem (mem (t (lift x)) q)
    ... | inj₁ yes = yes
    ... | inj₂ no with enumQ-surj q
    ...   | k , ≡.refl = ⊥-elim (nex (k , mq , no))

    e : _≐_ (λ x → (Σ ℕ (λ k → mem (h (lift x)) (enumQ k) × (mem (t (lift x)) (enumQ k) → ⊥))) → ⊥) (Below2 h t)
    e x = fwd x , (λ le (k , m , nm) → nm (le (enumQ k) m))

  ----------------------------------------------------------------------------
  -- the kernel: a sampler of the indicator [expansion r ≤ θ]

  decL : ∀ (a : QBS.∣ AQ ∣) (r : R₁) → Le (expansion r) (proj₁ a) ⊎ (Le (expansion r) (proj₁ a) → ⊥)
  decL a r = lemOf lem₁ (Le (expansion r) (proj₁ a))

  flipS : Sampler AQ BoolQ
  flipS = record
    { map = record
        { to = λ p → boolQ (flag (decL (proj₁ p) (proj₂ p)))
        ; cong = λ { {a , r} {b , r′} (ea , er) → boolQ-cong (flag-resp (decL a r) (decL b r′)
            (λ l q m → ap (proj₁ ea) q (l q (ap (proj₂ (Func.cong expansionProbe er)) q m)))
            (λ l q m → ap (proj₂ ea) q (l q (ap (proj₁ (Func.cong expansionProbe er)) q m)))) } }
    ; map-random = λ {γ} (m₁ , m₂) →
        indB-random (Below2-borel {h = λ x → expansion (proj₂ (γ ⟨$⟩ x))} {t = λ x → proj₁ (proj₁ (γ ⟨$⟩ x))}
          (Fun-pre {f = λ x → proj₂ (γ ⟨$⟩ x)} Fun-expansion m₂) m₁)
          (λ c → lemOf lem₁ (Below2 _ _ c))
    }

  coinKernel : Model AQ BoolQ
  coinKernel = samplerModel flipS

  ----------------------------------------------------------------------------
  -- the marginal: P(heads) = ∫ θ dθ = ½

  -- the marginal distribution of the coin, with the bias integrated out against the uniform prior
  marg : Pre BoolQ
  marg = joinPre (mapPre coinKernel uniform)

  -- E[1_true] = θ under the kernel at θ
  E-at-kernel : ∀ a → E-at (lawAt coinKernel a) indT ≃ ι (b1 (proj₂ a))
  E-at-kernel a = E-at-ι (lawAt coinKernel a) indT (b1 (proj₂ a))
    (trans (J-irrel fairCoin _ _) (J-indθ (proj₁ a) (proj₂ a))) (zeroJ (lawAt coinKernel a))

  ι≃id : ∀ a → ι (b1 (proj₂ a)) ≃ valT idT a
  ι≃id a = mk≃ 0# (SubSemiring.Is-0 finite) refl

  -- the expectation of heads at each parameter is the identity statistic
  kernel-id : ∀ a → valT (precompT coinKernel (expT indT)) a ≃ valT idT a
  kernel-id a = ≃-trans (E-at-expT (lawAt coinKernel a) indT) (≃-trans (E-at-kernel a) (ι≃id a))

  E-at-marg : E-at marg indT ≃ ι (b1 half≤1)
  E-at-marg = ≃-trans (E-at-join (mapPre coinKernel uniform) indT)
    (≃-trans (E-at-map coinKernel uniform (expT indT))
    (≃-trans (E-at-cong uniform _ idT kernel-id) E-at-uniform-id))

  ----------------------------------------------------------------------------
  -- two flips, conditionally independent given θ

  -- (θ , x) ↦ the law of (x , a further flip at θ)
  flipPair : Hom S (_×Q_ S AQ BoolQ) (TQ (_×Q_ S BoolQ BoolQ))
  flipPair = _∘H_ S (σH BoolQ BoolQ) (pairQ S {_×Q_ S AQ BoolQ} {BoolQ} {TQ BoolQ} (sndQ S {AQ} {BoolQ})
    (_∘H_ S coinKernel (fstQ S {AQ} {BoolQ})))

  -- θ ↦ (law of a flip at θ) ⊗ (law of a flip at θ): the first flip, then the second given it
  coinKernel² : Hom S AQ (TQ (_×Q_ S BoolQ BoolQ))
  coinKernel² = _∘H_ S (joinH (_×Q_ S BoolQ BoolQ)) (_∘H_ S (TH flipPair)
    (_∘H_ S (σH AQ BoolQ) (pairQ S {AQ} {AQ} {TQ BoolQ} (idH S) coinKernel)))

  -- the two-flip statistic 1_{true} ⊗ 1_{true}
  HH : STest (_×Q_ S BoolQ BoolQ)
  HH = indT ⊗T indT

  -- the statistic θ·1_{true} on `AQ × BoolQ`
  θH : STest (_×Q_ S AQ BoolQ)
  θH = idT ⊗T indT

  -- one step: after the first flip x, the second is heads with probability θ
  flipPair-θ : ∀ p → valT (precompT flipPair (expT HH)) p ≃ valT θH p
  flipPair-θ (a , x) = ≃-trans (E-at-expT (σPre (x , lawAt coinKernel a)) HH)
    (≃-trans (E-at-σ x (lawAt coinKernel a) indT indT)
    (≃-trans (*S-cong ≃-refl (≃-trans (E-at-kernel a) (ι≃id a))) (*S-comm (valT indT x) (valT idT a))))

  -- at θ the two flips both land heads with probability θ·θ
  E-at-kernel² : ∀ a → E-at (lawAt coinKernel² a) HH ≃ ι (b1 (proj₂ a)) *S ι (b1 (proj₂ a))
  E-at-kernel² a = ≃-trans (E-at-join (mapPre flipPair (σPre (a , lawAt coinKernel a))) HH)
    (≃-trans (E-at-map flipPair (σPre (a , lawAt coinKernel a)) (expT HH))
    (≃-trans (E-at-cong (σPre (a , lawAt coinKernel a)) _ θH flipPair-θ)
    (≃-trans (E-at-σ a (lawAt coinKernel a) idT indT) (*S-cong (≃-sym (ι≃id a)) (E-at-kernel a)))))

  ----------------------------------------------------------------------------
  -- P(HH) = ∫ θ² dθ = ⅓

  kernel²-sq : ∀ a → valT (precompT coinKernel² (expT HH)) a ≃ valT sqT a
  kernel²-sq a = ≃-trans (E-at-expT (lawAt coinKernel² a) HH) (≃-trans (E-at-kernel² a)
    (≃-trans (≃-sym (ι-* (b1 (proj₂ a)) (b1 (proj₂ a)))) (mk≃ 0# (SubSemiring.Is-0 finite) refl)))

  -- two flips of the marginal coin
  marg² : Pre (_×Q_ S BoolQ BoolQ)
  marg² = joinPre (mapPre coinKernel² uniform)

  -- P(heads, heads) = m, where 3m = 1 (`UniformMoment`)
  E-at-marg² : E-at marg² HH ≃ ι (b1 m≤1)
  E-at-marg² = ≃-trans (E-at-join (mapPre coinKernel² uniform) HH)
    (≃-trans (E-at-map coinKernel² uniform (expT HH))
    (≃-trans (E-at-cong uniform _ sqT kernel²-sq) E-at-uniform-sq))

  -- multiplied out, P(HH) = (2/3) P(H): three copies of P(HH) are two copies of P(H) (each side is 1)
  HH-from-H : let P₂ = E-at marg² HH ; P₁ = E-at marg indT in (P₂ +S P₂) +S P₂ ≃ P₁ +S P₁
  HH-from-H = ≃-trans (+S-cong (+S-cong E₂ E₂) E₂) (≃-trans (+S-cong (≃-sym (ι-+ f f)) ≃-refl)
    (≃-trans (≃-sym (ι-+ (SubSemiring.Is-+ finite f f) f)) (≃-trans (ι-cong _ _ eq)
    (≃-trans (ι-+ fh fh) (+S-cong (≃-sym E₁) (≃-sym E₁))))))
    where
    f = b1 m≤1
    E₂ = E-at-marg²
    E₁ = E-at-marg
    eq : (m2 + m2) + m2 ≈ half + half
    eq = trans second-moment (sym hh)
