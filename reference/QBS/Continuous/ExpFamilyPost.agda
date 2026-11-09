{-# OPTIONS --safe --without-K #-}

-- Continuous conjugate updating and Bayesian sufficiency: a conjugate prior times an exponential-family likelihood is again conjugate.
-- For a parameter space `Θ : QBS S` with base measure `μ_Θ : Pre (XW Θ)`, natural-parameter tests `η : Fin k → SgT Θ`
-- and log-partition test `A-stat : SgT Θ`, all finite at every θ (`FinT`: Θ lies in the natural parameter space):
--   * `priorTest (χ, ν) = ⟨χ, η⟩ − ν A`, `priorWeight p = e^{priorTest p}`, and the conjugate prior
--     `priorPre p = reweightPre (priorWeight p) μ_Θ`, with `priorPre-cong`; `priorWeight-at`: its value at θ is
--     `expW (expo χ ν η(θ) A(θ))` (`ExpFamilyPostAlg.expo`);
--   * `likTest T = priorTest (Σᵢ Tᵢ, N)` = ⟨Σᵢ Tᵢ, η⟩ − N A and `likWeight T = e^{likTest T}` for sample statistics
--     `T : Fin N → Vec k`;
--   * `update-test`: priorTest p + likTest T ≐ priorTest (updateSample p T), and `update-weight`, its weight form;
--   * `posterior-update`: reweighting `priorPre p` by `likWeight T` gives `priorPre (updateSample p T)`;
--   * `posterior-sufficient`: samples with `sumV T₁ ≈V sumV T₂` give ≈ᴹ posteriors under any conjugate prior;
--   * the data: `drawTest t = ⟨η, t⟩ − A` for one draw with statistic t, `likData t = ∏ᵢ e^{drawTest tᵢ}`, with
--     `likData-factor` (the product is `likWeight t`), `posterior-data` and `posterior-data-sufficient`; for draws
--     xᵢ in X and finite statistic tests `Tst : Fin k → SgT X`, tᵢ = `statAt Tst finT xᵢ`;
--   * `posterior-update-norm`, `posterior-sufficient-norm`: the same for the normalised posteriors
--     (`SFiniteNorm.normPre`), for any normalisers of the two sides.
-- The unnormalised statements carry the content: ≈ᴹ measures have ≈ᴹ normalisations whatever the normalisers
-- (`ExpFamilyPostAux.norm-cong`).  The posterior is the prior reweighted by the likelihood of the data, i.e. the density
-- form of Bayes' rule; identifying it with a conditional of the Bayesian joint of `Inference/CondIID` is not done (it
-- needs the family as a kernel Θ ⇒ T X and disintegration).
-- Route: every test is finite, so it is evaluated at θ to a signed value (`ExpFamilyPostAux.atSg-*`, `FinT-*`) and the
-- algebra is the ring identity `ExpFamilyPostAlg.expo-update` (or `expo-draw`) in `Signed.signedRing`; weights by
-- `ExpWeight.expW-+` and `expW-cong`; measures by `ExpFamilyPostAux.reweight-reweight` and `ProdReweight.reweight-cong`.
module QBS.Continuous.ExpFamilyPost where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as Nat
open import Data.Product.Base using (_,_)
open import Function.Bundles using (_⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Analysis.ExpFamAlg using (module ExpFamAlg)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.ExpFamily using (module ExpFamily)
open import QBS.Continuous.ExpFamilyPostAlg using (module ExpFamilyPostAlg)
open import QBS.Continuous.ExpFamilyPostAux using (module ExpFamilyPostAux)

module ExpFamilyPost (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _*_; 1#; sym; trans; *-cong)
  module CutR = SetoidReasoning (OmegaSemiring.setoid A)
  open Weights lem using (WQ)
  open Bounded A using (Sg; Sgˢ; signedRing; 1S; _≃_; _+S_; -S_; ≃-trans; ≃-sym; +S-cong; -S-cong)
  module SgR = SetoidReasoning Sgˢ
  open SgLinAlg signedRing using (Vec; _≈V_; _+V_; _·_)
  open ExpFamAlg signedRing using (Param; _≈P_; updateSample; sumV; scaleA)
  open ExpFamilyPostAlg signedRing using (expo; expo-cong; expo-update; expo-zero; expo-draw)
  open SignedTest lem₁ using (SgT; _+T_; -T_; scaleT; FinT; FinTs; _≐_)
  open SFinite lem using (module C; XW; _≈ᴹ_; ∫ᴹ)
  open C using (Pre)
  open SFiniteReweight lem using (reweightPre)
  open SFiniteNorm lem using (normPre; massP)
  open SFiniteIncl lem using (ιPre)
  open ExpWeight lem₁ using (expW; expWT; atSg; expW-cong; expW-+; expW-0)
  open ExpFamily lem₁ using (dotT; FinT-dotT)
  open ExpFamilyPostAux lem₁
    using ( FinT-+T; FinT-negT; FinT-scaleT; atSg-+; atSg-neg; atSg-scale; atSg-dot; ≐-atSg; expWT-at; mulH-at
          ; reweight-cong; reweight-reweight; prodW; prodW-zero; prodW-suc; norm-cong )
  open Hom

  -- the statistic of a point x of X, for finite statistic tests
  statAt : ∀ {X : QBS S} {k : ℕ} (Tst : Fin k → SgT X) → FinTs Tst → Setoid.Carrier (QBS.Carrier X) → Vec k
  statAt Tst finT x j = atSg (Tst j) (finT j) x

  module Posteriors
      {Θ : QBS S}
      (μ_Θ : Pre (XW Θ))
      {k : ℕ}
      (η : Fin k → SgT Θ)
      (A-stat : SgT Θ)
      (finη : FinTs η)
      (finA : FinT A-stat) where

    private
      CarrierΘ = Setoid.Carrier (QBS.Carrier Θ)

    -- the values η(θ) and A(θ)
    ηAt : CarrierΘ → Vec k
    ηAt θ j = atSg (η j) (finη j) θ

    AAt : CarrierΘ → Sg
    AAt θ = atSg A-stat finA θ

    -- prior exponent test ⟨χ, η⟩ − ν A, its weight, and the conjugate prior
    priorTest : Param k → SgT Θ
    priorTest (χ , ν) = dotT k χ η +T (-T (scaleT (scaleA ν 1S) A-stat))

    priorWeight : Param k → Hom S Θ WQ
    priorWeight p = expWT (priorTest p)

    priorPre : Param k → Pre (XW Θ)
    priorPre p = reweightPre (priorWeight p) μ_Θ

    priorTest-fin : ∀ p → FinT (priorTest p)
    priorTest-fin (χ , ν) = FinT-+T (FinT-dotT k χ η finη) (FinT-negT (FinT-scaleT (scaleA ν 1S) finA))

    -- the value of the prior exponent at θ
    priorTest-at : ∀ χ ν θ → atSg (priorTest (χ , ν)) (priorTest-fin (χ , ν)) θ ≃ expo χ ν (ηAt θ) (AAt θ)
    priorTest-at χ ν θ = ≃-trans (atSg-+ (FinT-dotT k χ η finη) (FinT-negT (FinT-scaleT (scaleA ν 1S) finA)) θ)
      (+S-cong (atSg-dot k χ finη θ)
        (≃-trans (atSg-neg (FinT-scaleT (scaleA ν 1S) finA) θ) (-S-cong (atSg-scale (scaleA ν 1S) finA θ))))

    priorWeight-at : ∀ χ ν θ → map (priorWeight (χ , ν)) ⟨$⟩ θ ≈ expW (expo χ ν (ηAt θ) (AAt θ))
    priorWeight-at χ ν θ =
      trans (expWT-at (priorTest (χ , ν)) (priorTest-fin (χ , ν)) θ) (expW-cong (priorTest-at χ ν θ))

    priorWeight-cong : ∀ {χ χ′} ν → χ ≈V χ′ → ∀ θ →
      map (priorWeight (χ , ν)) ⟨$⟩ θ ≈ map (priorWeight (χ′ , ν)) ⟨$⟩ θ
    priorWeight-cong {χ} {χ′} ν h θ = begin
      map (priorWeight (χ , ν)) ⟨$⟩ θ     ≈⟨ priorWeight-at χ ν θ ⟩
      expW (expo χ ν (ηAt θ) (AAt θ))     ≈⟨ expW-cong (expo-cong ν (ηAt θ) (AAt θ) h) ⟩
      expW (expo χ′ ν (ηAt θ) (AAt θ))    ≈⟨ sym (priorWeight-at χ′ ν θ) ⟩
      map (priorWeight (χ′ , ν)) ⟨$⟩ θ    ∎
      where open CutR

    priorPre-cong : ∀ {p q : Param k} → p ≈P q → _≈ᴹ_ {Θ} (priorPre p) (priorPre q)
    priorPre-cong {χ , ν} {χ′ , .ν} (h , refl) = reweight-cong μ_Θ (priorWeight-cong ν h)

    -- likelihood exponent test ⟨Σᵢ Tᵢ, η⟩ − N A for sample statistics T : Fin N → Vec k, and its weight
    likTest : ∀ {N} (T : Fin N → Vec k) → SgT Θ
    likTest {N} T = priorTest (sumV T , N)

    likWeight : ∀ {N} (T : Fin N → Vec k) → Hom S Θ WQ
    likWeight T = expWT (likTest T)

    -- the conjugate update, on exponents and on weights
    update-test : ∀ {N} (p : Param k) (T : Fin N → Vec k) → priorTest p +T likTest T ≐ priorTest (updateSample p T)
    update-test {N} (χ , ν) T = ≐-atSg (FinT-+T fp fl) (priorTest-fin (χ +V sumV T , ν Nat.+ N)) λ θ → begin
      atSg (priorTest (χ , ν) +T likTest T) (FinT-+T fp fl) θ   ≈⟨ atSg-+ fp fl θ ⟩
      atSg (priorTest (χ , ν)) fp θ +S atSg (likTest T) fl θ  ≈⟨ +S-cong (priorTest-at χ ν θ) (priorTest-at (sumV T) N θ) ⟩
      expo χ ν (ηAt θ) (AAt θ) +S expo (sumV T) N (ηAt θ) (AAt θ)
        ≈⟨ expo-update χ (sumV T) ν N (ηAt θ) (AAt θ) ⟩
      expo (χ +V sumV T) (ν Nat.+ N) (ηAt θ) (AAt θ)          ≈⟨ ≃-sym (priorTest-at (χ +V sumV T) (ν Nat.+ N) θ) ⟩
      atSg (priorTest (updateSample (χ , ν) T)) (priorTest-fin (χ +V sumV T , ν Nat.+ N)) θ ∎
      where fp = priorTest-fin (χ , ν)
            fl = priorTest-fin (sumV T , N)
            open SgR

    update-weight : ∀ {N} (p : Param k) (T : Fin N → Vec k) θ →
      (map (priorWeight p) ⟨$⟩ θ) * (map (likWeight T) ⟨$⟩ θ) ≈ map (priorWeight (updateSample p T)) ⟨$⟩ θ
    update-weight {N} (χ , ν) T θ = begin
      (map (priorWeight (χ , ν)) ⟨$⟩ θ) * (map (likWeight T) ⟨$⟩ θ)
        ≈⟨ *-cong (priorWeight-at χ ν θ) (priorWeight-at (sumV T) N θ) ⟩
      expW (expo χ ν e a) * expW (expo (sumV T) N e a)        ≈⟨ sym (expW-+ _ _) ⟩
      expW (expo χ ν e a +S expo (sumV T) N e a)              ≈⟨ expW-cong (expo-update χ (sumV T) ν N e a) ⟩
      expW (expo (χ +V sumV T) (ν Nat.+ N) e a)                ≈⟨ sym (priorWeight-at (χ +V sumV T) (ν Nat.+ N) θ) ⟩
      map (priorWeight (updateSample (χ , ν) T)) ⟨$⟩ θ        ∎
      where e = ηAt θ
            a = AAt θ
            open CutR

    -- posterior update and Bayesian sufficiency
    posterior-update : ∀ {N} (p : Param k) (T : Fin N → Vec k) →
      _≈ᴹ_ {Θ} (reweightPre (likWeight T) (priorPre p)) (priorPre (updateSample p T))
    posterior-update p T f = trans (reweight-reweight (likWeight T) (priorWeight p) μ_Θ f)
      (reweight-cong μ_Θ (λ θ → trans (mulH-at (priorWeight p) (likWeight T) θ) (update-weight p T θ)) f)

    posterior-sufficient : ∀ {N} (p : Param k) (T₁ T₂ : Fin N → Vec k) → sumV T₁ ≈V sumV T₂ →
      _≈ᴹ_ {Θ} (reweightPre (likWeight T₁) (priorPre p)) (reweightPre (likWeight T₂) (priorPre p))
    posterior-sufficient {N} p T₁ T₂ h = reweight-cong (priorPre p) (priorWeight-cong N h)

    -- the likelihood of data: one draw with statistic t has weight e^{⟨η(θ), t⟩ − A(θ)}; N draws, the product
    drawTest : Vec k → SgT Θ
    drawTest t = dotT k t η +T (-T A-stat)

    likData : ∀ {N} → (Fin N → Vec k) → Hom S Θ WQ
    likData {N} t = prodW N (λ i → expWT (drawTest (t i)))

    drawTest-fin : ∀ t → FinT (drawTest t)
    drawTest-fin t = FinT-+T (FinT-dotT k t η finη) (FinT-negT finA)

    drawTest-at : ∀ t θ → atSg (drawTest t) (drawTest-fin t) θ ≃ t · ηAt θ +S -S AAt θ
    drawTest-at t θ = ≃-trans (atSg-+ (FinT-dotT k t η finη) (FinT-negT finA) θ)
      (+S-cong (atSg-dot k t finη θ) (atSg-neg finA θ))

    drawWeight-at : ∀ t θ → map (expWT (drawTest t)) ⟨$⟩ θ ≈ expW (t · ηAt θ +S -S AAt θ)
    drawWeight-at t θ = trans (expWT-at (drawTest t) (drawTest-fin t) θ) (expW-cong (drawTest-at t θ))

    likData-nil : ∀ (t : Fin 0 → Vec k) θ → map (likData t) ⟨$⟩ θ ≈ map (likWeight t) ⟨$⟩ θ
    likData-nil t θ = begin
      map (likData t) ⟨$⟩ θ                  ≈⟨ prodW-zero (λ i → expWT (drawTest (t i))) θ ⟩
      1#                                     ≈⟨ sym expW-0 ⟩
      expW (Bounded.0S A)                    ≈⟨ sym (expW-cong (expo-zero (ηAt θ) (AAt θ))) ⟩
      expW (expo (sumV t) 0 (ηAt θ) (AAt θ)) ≈⟨ sym (priorWeight-at (sumV t) 0 θ) ⟩
      map (likWeight t) ⟨$⟩ θ                ∎
      where open CutR

    likData-factor : ∀ {N} (t : Fin N → Vec k) θ → map (likData t) ⟨$⟩ θ ≈ map (likWeight t) ⟨$⟩ θ
    likData-factor {zero} t θ = likData-nil t θ
    likData-factor {suc N} t θ = begin
      map (likData t) ⟨$⟩ θ                                       ≈⟨ prodW-suc N (λ i → expWT (drawTest (t i))) θ ⟩
      (map (expWT (drawTest (t zero))) ⟨$⟩ θ) * (map (likData t′) ⟨$⟩ θ)
        ≈⟨ *-cong (drawWeight-at (t zero) θ) (trans (likData-factor t′ θ) (priorWeight-at (sumV t′) N θ)) ⟩
      expW (t zero · e +S -S a) * expW (expo (sumV t′) N e a)     ≈⟨ sym (expW-+ _ _) ⟩
      expW ((t zero · e +S -S a) +S expo (sumV t′) N e a)         ≈⟨ expW-cong (expo-draw (t zero) (sumV t′) N e a) ⟩
      expW (expo (sumV t) (suc N) e a)                            ≈⟨ sym (priorWeight-at (sumV t) (suc N) θ) ⟩
      map (likWeight t) ⟨$⟩ θ                                     ∎
      where t′ = λ i → t (suc i)
            e = ηAt θ
            a = AAt θ
            open CutR

    posterior-data : ∀ {N} (p : Param k) (t : Fin N → Vec k) →
      _≈ᴹ_ {Θ} (reweightPre (likData t) (priorPre p)) (priorPre (updateSample p t))
    posterior-data p t f = trans (reweight-cong (priorPre p) (likData-factor t) f) (posterior-update p t f)

    posterior-data-sufficient : ∀ {N} (p : Param k) (t₁ t₂ : Fin N → Vec k) → sumV t₁ ≈V sumV t₂ →
      _≈ᴹ_ {Θ} (reweightPre (likData t₁) (priorPre p)) (reweightPre (likData t₂) (priorPre p))
    posterior-data-sufficient p t₁ t₂ h f = begin
      ∫ᴹ (reweightPre (likData t₁) (priorPre p)) f    ≈⟨ reweight-cong (priorPre p) (likData-factor t₁) f ⟩
      ∫ᴹ (reweightPre (likWeight t₁) (priorPre p)) f  ≈⟨ posterior-sufficient p t₁ t₂ h f ⟩
      ∫ᴹ (reweightPre (likWeight t₂) (priorPre p)) f  ≈⟨ sym (reweight-cong (priorPre p) (likData-factor t₂) f) ⟩
      ∫ᴹ (reweightPre (likData t₂) (priorPre p)) f    ∎
      where open CutR

    -- normalised posteriors, for any normalisers n, m of the two sides
    posterior-update-norm : ∀ {N} (p : Param k) (T : Fin N → Vec k) (n m : Cut)
      (hn : massP (reweightPre (likWeight T) (priorPre p)) * n ≈ 1#)
      (hm : massP (priorPre (updateSample p T)) * m ≈ 1#) →
      _≈ᴹ_ {Θ} (ιPre (normPre (reweightPre (likWeight T) (priorPre p)) n hn))
               (ιPre (normPre (priorPre (updateSample p T)) m hm))
    posterior-update-norm p T n m hn hm = norm-cong n m hn hm (posterior-update p T)

    posterior-sufficient-norm : ∀ {N} (p : Param k) (T₁ T₂ : Fin N → Vec k) (n m : Cut) → sumV T₁ ≈V sumV T₂ →
      (hn : massP (reweightPre (likWeight T₁) (priorPre p)) * n ≈ 1#)
      (hm : massP (reweightPre (likWeight T₂) (priorPre p)) * m ≈ 1#) →
      _≈ᴹ_ {Θ} (ιPre (normPre (reweightPre (likWeight T₁) (priorPre p)) n hn))
               (ιPre (normPre (reweightPre (likWeight T₂) (priorPre p)) m hm))
    posterior-sufficient-norm p T₁ T₂ n m h hn hm = norm-cong n m hn hm (posterior-sufficient p T₁ T₂ h)
