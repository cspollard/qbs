{-# OPTIONS --safe --without-K #-}

-- n flips of the coin with a uniform prior on its bias, and Laplace's rule of succession
-- (`plans/03-bayesian-frequentist.md`, 3c/3d; the continuation of `Inference/CoinUniformPrior`).
--
--   * `powT n : STest AQ`, the statistic θⁿ on the unit interval; `E-at uniform (powT n) ≃ ι ∫ uⁿ`
--     (`E-at-uniform-pow`) and, from `Continuous/UniformMomentN`, `(n+1)·∫ uⁿ = 1` (`moment-E`, with `nsum k x`, the
--     k-fold sum `x + (x + … + 0)`);
--   * `Fl n`, the outcomes of n+1 flips (`Fl 0 = BoolQ`, `Fl (suc n) = BoolQ × Fl n`), and `Kn n : AQ → T (Fl n)`,
--     θ ↦ the n+1 flips conditionally independent given θ, defined recursively exactly as `coinKernel²`: the first
--     flip, then the rest given it (`σ`, `T`, `join`).  The all-heads test `AH n = 1_{true} ⊗ … ⊗ 1_{true}` has
--     `E-at (lawAt (Kn n) θ) (AH n) ≃ θⁿ⁺¹` (`E-at-Kn`);
--   * under the uniform prior `margN n = join (map (Kn n) uniform)`, `E-at (margN n) (AH n) ≃ ∫ uⁿ⁺¹`
--     (`E-at-margN`), so (n+2)·P(Hⁿ⁺¹) = 1 (`heads-prob`);
--   * Laplace's rule of succession, multiplied out (no division): with `HP 0 = 1` and `HP (n+1) = P(Hⁿ⁺¹)`,
--     (n+2)·P(Hⁿ⁺¹) ≃ (n+1)·P(Hⁿ), i.e. P(next head | n heads) = (n+1)/(n+2) (`succession`).
module QBS.Inference.CoinUniformPriorN where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; pairQ; fstQ; sndQ)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.FairCoin using (module FairCoin)
import QBS.Continuous.UniformMomentN as UMN
import QBS.BoolQ as BQ
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.ExpectationProduct as EP
import QBS.Inference.ExpectationExamples as EE
import QBS.Inference.BoolDist as BD
import QBS.Inference.Sampler as SM
import QBS.Inference.CoinUniformPrior as CUP
open BQ.BoolOn S

module CoinUniformPriorN (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-irrel; J; J-fun)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; *-comm;
    *-identityʳ; +-cong; 0-least; ≤-trans; ≤-reflexive; +-identityʳ)
  open Bounded A using (Sg; Bnd; finite; _+S_; _*S_; ι-+; ι-*; _≃_; ≃-trans; ≃-sym; ≃-refl; ι; mk≃; +S-cong; *S-cong;
    *S-comm; 0S)
  open BoundedSignedTests (lemOf lem₁) using (CutQ; STest)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre; joinPre; TQ; TH; joinH)
  open LevelSets (lemOf lem₁) using (LS)
  open Uniform lem₁ using (uniform)
  open FairCoin lem₁ using (fairCoin)
  open SM.Sampler lem₁ using (lawAt)
  open ER.ExpectationResp lem₁ using (E-at)
  open EX.Expectation lem₁ using (valT; precompT; expT; constH; E-at-join; E-at-map; E-at-expT)
  open EP.ExpectationProduct lem₁ using (E-at-cong; _⊗T_; E-at-σ; valT-⊗T)
  open Strength A (lemOf lem₁) probClass using (σPre; σH)
  open EE.ExpectationExamples lem₁ using (b1; E-at-ι; zeroJ; ι-cong)
  open BD.BoolDist lem₁ using (indT)
  open CUP.CoinUniformPrior lem₁ using (coinKernel; E-at-kernel; ι≃id)
  open UMN.UniformMomentN lem₁ using (pw; pw-cong; pw≤1; Meas-pw; M; M≤1; Fpow; I-pow; moment-N)
  open UMN.AlgN A (UMN.UniformMomentN.R lem₁) using (#)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)

  ----------------------------------------------------------------------------
  -- the statistic θⁿ and all moments of the uniform distribution

  powH : ℕ → Hom S AQ CutQ
  powH n = record
    { map = record { to = λ x → pw (proj₁ x) n ; cong = λ e → pw-cong e n }
    ; map-random = λ {β} f → Meas-pw {λ r → proj₁ (β ⟨$⟩ r)} (LS f) n }

  powT : ℕ → STest AQ
  powT n = record
    { pos = powH n ; neg = constH 0# ; bound = 1
    ; pos-bdd = λ x → ≤-trans (pw≤1 (proj₂ x) n) (≤-reflexive (sym (+-identityʳ 1#)))
    ; neg-bdd = λ _ → 0-least }

  -- the value of θⁿ at a point
  valpow : ∀ m a → valT (powT m) a ≃ ι (b1 (pw≤1 (proj₂ a) m))
  valpow m a = mk≃ 0# (SubSemiring.Is-0 finite) refl

  -- E[Uⁿ] = ∫ uⁿ du
  E-at-uniform-pow : ∀ n → E-at uniform (powT n) ≃ ι (b1 (M≤1 n))
  E-at-uniform-pow n = E-at-ι uniform (powT n) (b1 (M≤1 n))
    (trans (J-irrel fairCoin _ (LS (Fpow n))) (trans (J-fun fairCoin (Fpow n)) (I-pow n))) (zeroJ uniform)

  -- k-fold sums in the signed values
  nsum : ℕ → Sg → Sg
  nsum zero x = 0S
  nsum (suc k) x = x +S nsum k x

  rep : ℕ → ∣A∣ → ∣A∣
  rep zero x = 0#
  rep (suc k) x = x + rep k x

  repB : ∀ k {x} → Bnd x → Bnd (rep k x)
  repB zero fx = SubSemiring.Is-0 finite
  repB (suc k) fx = SubSemiring.Is-+ finite fx (repB k fx)

  nsum-ι : ∀ k {x} (fx : Bnd x) → nsum k (ι fx) ≃ ι (repB k fx)
  nsum-ι zero fx = ≃-refl
  nsum-ι (suc k) fx = ≃-trans (+S-cong ≃-refl (nsum-ι k fx)) (≃-sym (ι-+ fx (repB k fx)))

  nsum-cong : ∀ k {x y} → x ≃ y → nsum k x ≃ nsum k y
  nsum-cong zero e = ≃-refl
  nsum-cong (suc k) e = +S-cong e (nsum-cong k e)

  rep-# : ∀ k x → rep k x ≈ # k * x
  rep-# zero x = sym (OmegaSemiring.zeroˡ A x)
  rep-# (suc k) x = trans (+-cong refl (rep-# k x))
    (solve 2 (λ p x′ → x′ :+ p :* x′ := (con 1 :+ p) :* x′) refl (# k) x)

  -- (n+1) ∫ uⁿ du = 1
  moment-E : ∀ n → nsum (suc n) (E-at uniform (powT n)) ≃ ι (SubSemiring.Is-1 finite)
  moment-E n = ≃-trans (nsum-cong (suc n) (E-at-uniform-pow n)) (≃-trans (nsum-ι (suc n) (b1 (M≤1 n)))
    (ι-cong _ _ (trans (rep-# (suc n) (M n)) (moment-N n))))

  ----------------------------------------------------------------------------
  -- n+1 flips, conditionally independent given θ

  -- (θ , x) ↦ the law of (x , the flips of K at θ)
  flipPairN : ∀ {F : QBS S} → Hom S AQ (TQ F) → Hom S (_×Q_ S AQ BoolQ) (TQ (_×Q_ S BoolQ F))
  flipPairN {F} K = _∘H_ S (σH BoolQ F) (pairQ S {_×Q_ S AQ BoolQ} {BoolQ} {TQ F} (sndQ S {AQ} {BoolQ})
    (_∘H_ S K (fstQ S {AQ} {BoolQ})))

  -- one more flip in front: θ ↦ the first flip, then the flips of K given it
  nextK : ∀ {F : QBS S} → Hom S AQ (TQ F) → Hom S AQ (TQ (_×Q_ S BoolQ F))
  nextK {F} K = _∘H_ S (joinH (_×Q_ S BoolQ F)) (_∘H_ S (TH (flipPairN K)) (_∘H_ S (σH AQ BoolQ)
    (pairQ S {AQ} {AQ} {TQ BoolQ} (idH S) coinKernel)))

  -- the outcomes of n+1 flips, and their law at θ
  Fl : ℕ → QBS S
  Fl zero = BoolQ
  Fl (suc n) = _×Q_ S BoolQ (Fl n)

  Kn : ∀ n → Hom S AQ (TQ (Fl n))
  Kn zero = coinKernel
  Kn (suc n) = nextK (Kn n)

  -- the all-heads test
  AH : ∀ n → STest (Fl n)
  AH zero = indT
  AH (suc n) = indT ⊗T AH n

  -- θᵐ · θ = θᵐ⁺¹
  pow-succ : ∀ m a → valT (powT m) a *S ι (b1 (proj₂ a)) ≃ valT (powT (suc m)) a
  pow-succ m a = ≃-trans (*S-cong (valpow m a) ≃-refl) (≃-trans (≃-sym (ι-* (b1 (pw≤1 (proj₂ a) m)) (b1 (proj₂ a))))
    (≃-trans (ι-cong _ _ (*-comm (pw (proj₁ a) m) (proj₁ a))) (≃-sym (valpow (suc m) a))))

  -- one step: after the first flip x, the rest has all heads with probability θᵐ
  flipN-pow : ∀ {F} (K : Hom S AQ (TQ F)) (T : STest F) m → (∀ a → E-at (lawAt K a) T ≃ valT (powT m) a) →
    ∀ p → valT (precompT (flipPairN K) (expT (indT ⊗T T))) p ≃ valT (powT m ⊗T indT) p
  flipN-pow K T m hK (a , x) = ≃-trans (E-at-expT (σPre (x , lawAt K a)) (indT ⊗T T))
    (≃-trans (E-at-σ x (lawAt K a) indT T) (≃-trans (*S-cong ≃-refl (hK a)) (*S-comm (valT indT x) (valT (powT m) a))))

  -- prepending a flip multiplies by θ
  nextK-E : ∀ {F} (K : Hom S AQ (TQ F)) (T : STest F) m → (∀ a → E-at (lawAt K a) T ≃ valT (powT m) a) →
    ∀ a → E-at (lawAt (nextK K) a) (indT ⊗T T) ≃ valT (powT (suc m)) a
  nextK-E K T m hK a = ≃-trans (E-at-join (mapPre (flipPairN K) (σPre (a , lawAt coinKernel a))) (indT ⊗T T))
    (≃-trans (E-at-map (flipPairN K) (σPre (a , lawAt coinKernel a)) (expT (indT ⊗T T)))
    (≃-trans (E-at-cong (σPre (a , lawAt coinKernel a)) _ (powT m ⊗T indT) (flipN-pow K T m hK))
    (≃-trans (E-at-σ a (lawAt coinKernel a) (powT m) indT)
      (≃-trans (*S-cong ≃-refl (E-at-kernel a)) (pow-succ m a)))))

  -- E[1_{Hⁿ⁺¹} | θ] = θⁿ⁺¹
  E-at-Kn : ∀ n a → E-at (lawAt (Kn n) a) (AH n) ≃ valT (powT (suc n)) a
  E-at-Kn zero a = ≃-trans (E-at-kernel a) (≃-trans (ι-cong _ (b1 (pw≤1 (proj₂ a) 1)) (sym (*-identityʳ (proj₁ a))))
    (≃-sym (valpow 1 a)))
  E-at-Kn (suc n) = nextK-E (Kn n) (AH n) (suc n) (E-at-Kn n)

  ----------------------------------------------------------------------------
  -- the uniform prior: (n+2) P(Hⁿ⁺¹) = 1

  -- the marginal of the n+1 flips, with the bias integrated out against the uniform prior
  margN : ∀ n → Pre (Fl n)
  margN n = joinPre (mapPre (Kn n) uniform)

  -- P(Hⁿ⁺¹) = ∫ uⁿ⁺¹ du
  E-at-margN : ∀ n → E-at (margN n) (AH n) ≃ E-at uniform (powT (suc n))
  E-at-margN n = ≃-trans (E-at-join (mapPre (Kn n) uniform) (AH n))
    (≃-trans (E-at-map (Kn n) uniform (expT (AH n)))
    (E-at-cong uniform _ (powT (suc n)) (λ a → ≃-trans (E-at-expT (lawAt (Kn n) a) (AH n)) (E-at-Kn n a))))

  -- multiplied out: (n+2) copies of P(Hⁿ⁺¹) add up to one
  heads-prob : ∀ n → nsum (suc (suc n)) (E-at (margN n) (AH n)) ≃ ι (SubSemiring.Is-1 finite)
  heads-prob n = ≃-trans (nsum-cong _ (E-at-margN n)) (moment-E (suc n))

  ----------------------------------------------------------------------------
  -- Laplace's rule of succession

  -- the probability of n heads in n flips: 1 for n = 0
  HP : ℕ → Sg
  HP zero = ι (SubSemiring.Is-1 finite)
  HP (suc k) = E-at (margN k) (AH k)

  HP-one : ∀ n → nsum (suc n) (HP n) ≃ ι (SubSemiring.Is-1 finite)
  HP-one zero = ≃-trans (nsum-ι 1 (SubSemiring.Is-1 finite)) (ι-cong _ _ (+-identityʳ 1#))
  HP-one (suc k) = heads-prob k

  -- (n+2) P(Hⁿ⁺¹) = (n+1) P(Hⁿ): P(next head | n heads) = (n+1)/(n+2)
  succession : ∀ n → nsum (suc (suc n)) (HP (suc n)) ≃ nsum (suc n) (HP n)
  succession n = ≃-trans (HP-one (suc n)) (≃-sym (HP-one n))
