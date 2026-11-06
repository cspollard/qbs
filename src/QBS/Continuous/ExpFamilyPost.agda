{-# OPTIONS --safe --without-K #-}

-- Continuous conjugate updating and Bayesian sufficiency (plan 07, item 60; completing Phase A).
-- For parameter space `Θ : QBS S`, base measure `μ_Θ : Pre (XW Θ)`, natural parameter tests
-- `η : Fin k → SgT Θ`, and log-partition test `A : SgT Θ`:
--   * `Param k = Vec k × ℕ`, natural conjugate hyperparameters (χ, ν);
--   * `priorTest p : SgT Θ`, conjugate exponent test `dotT k χ η − scaleT (scaleA ν 1S) A`;
--   * `priorWeight p = expWT (priorTest p) : Hom S Θ WQ`;
--   * `priorPre p = reweightPre (priorWeight p) μ_Θ : Pre (XW Θ)`;
--   * `likTest N T : SgT Θ`, likelihood exponent test `dotT k (sumV T) η − scaleT (scaleA N 1S) A`;
--   * `likWeight N T = expWT (likTest N T) : Hom S Θ WQ`;
--   * `update-weight`: prior weight times likelihood weight equals updated prior weight when tests are finite;
--   * `posterior-update`: reweighting `priorPre p` by `likWeight N T` yields `priorPre (updateSample p T)`
--     (`ExpFamAlg.updateSample`, `ExpWeight.expW-+`);
--   * `posterior-sufficient`: datasets with equal sufficient statistics `sumV T₁ ≈V sumV T₂` yield
--     equivalent posteriors under any conjugate prior (`ExpFamAlg.·-sumV`, `ExpWeight.expWT-cong`).
-- Route: `ExpFamAlg` over `Signed.signedRing` for algebra; `ExpWeight` for weights and multiplicativity;
-- `SFiniteReweight` for posterior updating.
module QBS.Continuous.ExpFamilyPost where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as Nat
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_; Func)
open import Relation.Binary.Bundles using (Setoid)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Analysis.ExpFamAlg using (module ExpFamAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.ExpFamily using (module ExpFamily)

module ExpFamilyPost (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A-ring = Lebesgue.A lem
  open OmegaSemiring A-ring using (_≈_; _*_; _+_; 1#; 0#; refl; sym; trans; *-cong; +-cong;
    *-identityˡ; *-identityʳ; *-comm; *-assoc)
  open Weights lem using (WQ; constW)
  open Bounded A-ring using (Sg; signedRing; _+S_; 0S; -S_; 1S; _≃_; finite; Bnd)
  open SubSemiring finite using (Is-+)
  open SgLinAlg signedRing using (Vec; _·_; Σ; _≈V_; _+V_; Σ-cong)
  open ExpFamAlg signedRing using (Param; updateSample; sumV; sumV-cong; ·-sumV; scaleA; scaleA-cong; scaleA-+)
  open SignedTest lem₁ using (SgT; _+T_; -T_; scaleT; constT; FinT; at⁺; at⁻; _≐_; ≐-refl; ≐-sym; fromW; _∘T_)
  open SFinite lem using (module C; XW; ∫ᴹ; ∫ᴹ-cong; _≈ᴹ_)
  open C using (Pre)
  open SFiniteReweight lem using (reweightPre; ∫ᴹ-reweight; mulH)
  open ExpWeight lem₁ using (expW; expWT; expW-+; expW-cong; expWT-cong; atSg)
  open ExpFamily lem₁ using (dotT)

  FinT-+ : ∀ {X : QBS S} {f g : SgT X} → FinT f → FinT g → FinT (f +T g)
  FinT-+ hf hg x = Is-+ (proj₁ (hf x)) (proj₁ (hg x)) , Is-+ (proj₂ (hf x)) (proj₂ (hg x))

  module Posteriors
      {Θ : QBS S}
      (μ_Θ : Pre (XW Θ))
      {k : ℕ}
      (η : Fin k → SgT Θ)
      (A-stat : SgT Θ) where

    private
      CarrierΘ = Setoid.Carrier (QBS.Carrier Θ)

    -- Prior exponent test: ⟨χ, η⟩ − ν A
    priorTest : Param k → SgT Θ
    priorTest (χ , ν) = dotT k χ η +T (-T (scaleT (scaleA ν 1S) A-stat))

    -- Prior weight morphism
    priorWeight : Param k → Hom S Θ WQ
    priorWeight p = expWT (priorTest p)

    -- Conjugate prior measure
    priorPre : Param k → Pre (XW Θ)
    priorPre p = reweightPre (priorWeight p) μ_Θ

    -- Likelihood exponent test for sample statistics T : Fin N → Vec k
    likTest : ∀ {N} (T : Fin N → Vec k) → SgT Θ
    likTest {N} T = dotT k (sumV T) η +T (-T (scaleT (scaleA N 1S) A-stat))

    -- Likelihood weight morphism
    likWeight : ∀ {N} (T : Fin N → Vec k) → Hom S Θ WQ
    likWeight T = expWT (likTest T)

    -- Updating lemma: prior weight times likelihood weight ≈ updated prior weight
    update-weight : ∀ {N} (p : Param k) (T : Fin N → Vec k) →
      (finP : FinT (priorTest p)) (finL : FinT (likTest T)) (finU : FinT (priorTest (updateSample p T))) →
      priorTest p +T likTest T ≐ priorTest (updateSample p T) →
      ∀ (θ : CarrierΘ) →
      (Func.to (Hom.map (priorWeight p)) θ) * (Func.to (Hom.map (likWeight T)) θ) ≈
      Func.to (Hom.map (priorWeight (updateSample p T))) θ
    update-weight {N} p T finP finL finU eq θ =
      trans (sym (expW-+ (atSg (priorTest p) finP θ) (atSg (likTest T) finL θ)))
        (expWT-cong (FinT-+ finP finL) finU eq {θ})

    -- Posterior update theorem
    posterior-update : ∀ {N} (p : Param k) (T : Fin N → Vec k) →
      (∀ θ → (Func.to (Hom.map (priorWeight p)) θ) * (Func.to (Hom.map (likWeight T)) θ) ≈
             Func.to (Hom.map (priorWeight (updateSample p T))) θ) →
      _≈ᴹ_ {Θ} (reweightPre (likWeight T) (priorPre p)) (priorPre (updateSample p T))
    posterior-update p T h f =
      trans (∫ᴹ-reweight (likWeight T) (priorPre p) f)
        (trans (∫ᴹ-reweight (priorWeight p) μ_Θ (mulH (likWeight T) f))
          (trans (∫ᴹ-cong μ_Θ (λ θ → trans (sym (*-assoc (Func.to (Hom.map (priorWeight p)) θ)
                                                         (Func.to (Hom.map (likWeight T)) θ)
                                                         (Func.to (Hom.map f) θ)))
                                           (*-cong (h θ) refl)))
            (sym (∫ᴹ-reweight (priorWeight (updateSample p T)) μ_Θ f))))

    -- Bayesian sufficiency
    posterior-sufficient : ∀ {N} (p : Param k) (T₁ T₂ : Fin N → Vec k) →
      FinT (likTest T₁) → FinT (likTest T₂) →
      likTest T₁ ≐ likTest T₂ →
      _≈ᴹ_ {Θ} (reweightPre (likWeight T₁) (priorPre p)) (reweightPre (likWeight T₂) (priorPre p))
    posterior-sufficient p T₁ T₂ f1 f2 eq f =
      trans (∫ᴹ-reweight (likWeight T₁) (priorPre p) f)
        (trans (∫ᴹ-cong (priorPre p) (λ θ → *-cong (expWT-cong f1 f2 eq {θ}) refl))
          (sym (∫ᴹ-reweight (likWeight T₂) (priorPre p) f)))
