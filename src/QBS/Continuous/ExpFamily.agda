{-# OPTIONS --safe --without-K #-}

-- Continuous exponential families on quasi-Borel spaces (used by `ExpFamilyPost`).
-- For a base measure `h : Pre (XW X)`, statistics `T : Fin k → SgT X` and a natural parameter `η : Vec k`:
--   * `dotT k η T = Σⱼ ηⱼ Tⱼ`, linear in the statistics up to `ExpFamilyAux._≈T_` (`dotT-+`, `dotT-∘T`, `dotT-0`) and
--     finite when the statistics are (`FinT-dotT`);
--   * `weight k η T = e^{⟨η, T⟩}`, `partition h k η T = Z(η) = ∫ e^{⟨η, T⟩} dh`, `probPre h k η T n hn`, the
--     normalised measure for a normaliser n with Z(η) · n ≈ 1 (`probPre-mass`), and `logPartition`, A(η) = log Z(η);
--   * N draws: on `Xⁿ N X` the base `baseⁿ N h = h^{⊗N}` and the summed statistic `sumTⁿ N k T`, Σᵢ T ∘ projᵢ
--     (`sumTⁿ-proj`, with `SgMoments.sumT`); for finite statistics, the weight of the sum is the product of the weights
--     (`weight-sumTⁿ`), so Z_N(η) ≈ Z(η)ᴺ (`partition-sumTⁿ`; `product-partition` is the rectangle form), the
--     normaliser is nᴺ (`product-norm`), the law of N independent draws from P_η is the family on Xᴺ (`product-expFam`,
--     and `IID-expFam` for an iid family of random variables, `Continuous/IID`), and the log-partition is
--     N · A(η) (`logPartition-sumTⁿ`, `ExpFamAlg.scaleA`);
--   * instances: Exp(1) (`expFam-Exp1`, agreeing with `ExpDist.expW`); Exp(λ) for a rate with a reciprocal
--     (`ExpRate.expFam-Exp`, partition 1/λ, agreeing with `DensityDist.densDist` of λ e^{−λx}, hence with
--     `Inference/ExpRateDist.expDistλ`); the Gaussian family with known variance on the real line (`gaussFam`: T = x,
--     h = e^{−x²/2} dλ), whose member at η = 0 is the standard Gaussian of `RealDensity.Sym` (`gaussFam0-agree`, hence
--     `Inference/GaussReal.gaussR`).
-- Route: linearity of `dotT` from `ExpFamilyAux.scaleT-+T` by induction on k; `weight-sumTⁿ` by induction on N from
-- `ExpFamilyAux.expWT-+T` and `expWT-≈T`; `partition-sumTⁿ` from it and `FinProd.∫-rectⁿ`, and `product-norm` from
-- `ExpFamilyAlg.prodF-mul`; `product-expFam` by induction on N from `ProdReweight.prod-scale`, `prod-reweight`,
-- `reweight-cong` and `Product.prod-cong`; `logPartition-sumTⁿ` from `ExpFamilyAux.logS-∏ⁿ`; Exp(λ) from
-- `ExpRateInt.Int.∫-negExpR` and `DensityDist.∫-dens`; the Gaussian at η = 0 from `RealDensity.lebR-sym`,
-- `∫ᴹ-lebR-dens` and `Sym.∫-sym`.
-- Limits: the N-draw results take finite statistics (`FinT`) as a hypothesis, since e^{a + b} ≈ e^{a} e^{b} needs
-- bounded negative parts (`ExpWeight.expW-+`); Exp(λ) is for a rate given with reciprocal data (`ExpRateInt.Int`); the
-- Gaussian family at η ≠ 0 (completing the square) is left to a later `ExpFamilyGauss`.
module QBS.Continuous.ExpFamily where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Limits using (fstQ; sndQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC-zero; expC-cong)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Analysis.ExpFamAlg using (module ExpFamAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.IID using (module IID)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.ExpFamilyAlg using (module ExpFamilyAlg)
open import QBS.Continuous.ExpFamilyAux using (module ExpFamilyAux)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.ExpRateInt using (module ExpRateInt)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.HalfLineRate using (module HalfLineRate)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.RealDensity using (module RealDensity)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)

module ExpFamily (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; 0#; refl; sym; trans; *-cong; +-cong; *-assoc;
    *-identityˡ; *-identityʳ; *-comm; zeroˡ; zeroʳ; +-identityˡ; +-identityʳ; setoid; ≤-trans; ≤-reflexive;
    commutativeSemiring)
  open import Relation.Binary.Reasoning.Setoid setoid
  open Exp A using (natE)
  open NegExp lem using (negExp; negExp-anti; negExp-cong)
  open Weights lem using (WQ; constW)
  open Bounded A using (Sg; _≃_; Bnd; 0S; -S_; 1S; ι; signedRing; ≃-trans)
  open SgLinAlg signedRing using (Vec)
  open ExpFamAlg signedRing using (scaleA)
  open SignedTest lem₁ using (SgT; _+T_; scaleT; constT; FinT; FinTs; fromW; _∘T_; idT)
  open SignedLog lem₁ using (PosQ; logS)
  open SFinite lem using (module C; XW; ∫ᴹ; ∫ᴹ-cong; _≈ᴹ_; ∫ᴹ-η)
  open C using (Pre)
  open SFiniteReweight lem using (reweightPre; ∫ᴹ-reweight; mulH)
  open SFiniteSum lem using (scalePre; ∫ᴹ-scale)
  open SFiniteIncl lem using (ιPre)
  open FinProd lem₁ using (ΠQ; projQ; tupleQ; prodⁿ; prodT; ∏ⁿ; ∫-rectⁿ)
  open IID lem₁ using (IID)
  open SgMoments lem₁ using (sumT)
  open Independence lem₁ using (law)
  open ExpWeight lem₁ using (expWT)
  open ExpFamilyAlg commutativeSemiring using (prodF; prodF-mul; prodF-cong; prodF-one)
  open ExpFamilyAux lem₁ using (_≈T_; ≈T-refl; ≈T-sym; ≈T-trans; +T-≈T; +T-interchange; +T-0; scaleT-+T; scaleT-∘T;
    scaleT-0; scaleT-0S; FinT-+T; FinT-scaleT; FinT-constT; FinT-∘T; expWT-≈T; expWT-+T; expWT-0; reweight-cong;
    prod-reweight; prod-scale; PosQ-resp; BndQ-resp; logS-cong; PosQ-∏ⁿ; BndQ-∏ⁿ; logS-∏ⁿ)
  open Product lem using (prodPre; prod-cong; cmul)
  open ExpRateInt lem₁ using (module Int)
  open LebesgueDyadicAlg lem using (natE≈nat)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineNorm lem₁ using (∫ᴹ-leb-negExp-norm)
  open Hom
  open HalfLineRate lem₁ using (negExpRH; scaleH)
  open ExpDist lem₁ using (idW) renaming (expW to expDistW; ∫ᴹ-expW to ∫ᴹ-expDistW)
  open DensityDist lem₁ using (densDist; ∫-dens)
  open RealLine lem₁ using (RQ; lebR; copairH)
  open RealDensity lem₁ using (module Sym; lebR-sym; ∫ᴹ-lebR-dens)
  open GaussHalfLine lem₁ using (phiH)

  ----------------------------------------------------------------------------
  -- the family

  -- Linear combination of statistics ⟨η, T⟩ = Σⱼ ηⱼ Tⱼ
  dotT : ∀ {X : QBS S} (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → SgT X
  dotT zero η T = constT 0S
  dotT (suc k) η T = scaleT (η zero) (T zero) +T dotT k (λ j → η (suc j)) (λ j → T (suc j))

  -- Exponential density weight w(η) = expWT ⟨η, T⟩
  weight : ∀ {X : QBS S} (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → Hom S X WQ
  weight k η T = expWT (dotT k η T)

  -- Partition function Z(η) = ∫ᴹ h (w(η))
  partition : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → Cut
  partition h k η T = ∫ᴹ h (weight k η T)

  -- Normalised probability measure when partition * n ≈ 1#
  probPre : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut) →
    partition h k η T * n ≈ 1# → Pre (XW X)
  probPre h k η T n hn = scalePre n (reweightPre (weight k η T) h)

  probPre-mass : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut)
    (hn : partition h k η T * n ≈ 1#) → ∫ᴹ (probPre h k η T n hn) (constW 1#) ≈ 1#
  probPre-mass h k η T n hn = begin
    ∫ᴹ (probPre h k η T n hn) (constW 1#)          ≈⟨ ∫ᴹ-scale n (reweightPre (weight k η T) h) (constW 1#) ⟩
    n * ∫ᴹ (reweightPre (weight k η T) h) (constW 1#) ≈⟨ *-cong refl (∫ᴹ-reweight (weight k η T) h (constW 1#)) ⟩
    n * ∫ᴹ h (mulH (weight k η T) (constW 1#))      ≈⟨ *-cong refl (∫ᴹ-cong h (λ x → *-identityʳ _)) ⟩
    n * partition h k η T                            ≈⟨ *-comm n (partition h k η T) ⟩
    partition h k η T * n                            ≈⟨ hn ⟩
    1# ∎

  -- Signed log-partition function A(η) = logS Z(η)
  logPartition : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    (pz : PosQ (partition h k η T)) (bz : BndQ (partition h k η T)) → Sg
  logPartition h k η T pz bz = logS (partition h k η T) pz bz

  ----------------------------------------------------------------------------
  -- linearity and finiteness of ⟨η, T⟩

  dotT-+ : ∀ {X : QBS S} (k : ℕ) (η : Vec k) (f g : Fin k → SgT X) →
    dotT k η (λ j → f j +T g j) ≈T dotT k η f +T dotT k η g
  dotT-+ zero η f g = +T-0
  dotT-+ (suc k) η f g = ≈T-trans (+T-≈T (scaleT-+T (η zero) (f zero) (g zero)) (dotT-+ k η′ f′ g′))
    (+T-interchange (scaleT (η zero) (f zero)) (scaleT (η zero) (g zero)) (dotT k η′ f′) (dotT k η′ g′))
    where
      η′ = λ j → η (suc j)
      f′ = λ j → f (suc j)
      g′ = λ j → g (suc j)

  dotT-∘T : ∀ {X Y : QBS S} (k : ℕ) (η : Vec k) (T : Fin k → SgT Y) (φ : Hom S X Y) →
    dotT k η (λ j → T j ∘T φ) ≈T dotT k η T ∘T φ
  dotT-∘T zero η T φ = ≈T-refl
  dotT-∘T (suc k) η T φ = +T-≈T (scaleT-∘T (η zero) (T zero) φ) (dotT-∘T k (λ j → η (suc j)) (λ j → T (suc j)) φ)

  dotT-0 : ∀ {X : QBS S} (k : ℕ) (η : Vec k) → dotT k η (λ _ → constT {X} 0S) ≈T constT {X} 0S
  dotT-0 zero η = ≈T-refl
  dotT-0 (suc k) η = ≈T-trans (+T-≈T (scaleT-0 (η zero)) (dotT-0 k (λ j → η (suc j)))) (≈T-sym +T-0)

  -- the zero parameter gives the zero exponent, and weight 1
  dotT-0S : ∀ {X : QBS S} (k : ℕ) (T : Fin k → SgT X) → dotT k (λ _ → 0S) T ≈T constT {X} 0S
  dotT-0S zero T = ≈T-refl
  dotT-0S (suc k) T = ≈T-trans (+T-≈T (scaleT-0S (T zero)) (dotT-0S k (λ j → T (suc j)))) (≈T-sym +T-0)

  weight-0S : ∀ {X : QBS S} (k : ℕ) (T : Fin k → SgT X) x → map (weight k (λ _ → 0S) T) ⟨$⟩ x ≈ 1#
  weight-0S k T x = trans (expWT-≈T (dotT-0S k T) {x}) (expWT-0 x)

  FinT-dotT : ∀ {X : QBS S} (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → FinTs T → FinT (dotT k η T)
  FinT-dotT zero η T fin = FinT-constT 0S
  FinT-dotT (suc k) η T fin =
    FinT-+T (FinT-scaleT (η zero) (fin zero)) (FinT-dotT k (λ j → η (suc j)) (λ j → T (suc j)) (λ j → fin (suc j)))

  ----------------------------------------------------------------------------
  -- N draws

  -- Homogeneous product space Xᴺ
  Xⁿ : ∀ (N : ℕ) (X : QBS S) → QBS S
  Xⁿ N X = ΠQ N (λ _ → X)

  -- Coordinate projections
  projⁿ : ∀ {N : ℕ} {X : QBS S} (i : Fin N) → Hom S (Xⁿ N X) X
  projⁿ {N} {X} i = projQ N (λ _ → X) i

  -- The base measure h^{⊗N}
  baseⁿ : ∀ {X : QBS S} (N : ℕ) → Pre (XW X) → Pre (XW (Xⁿ N X))
  baseⁿ {X} N h = prodⁿ N (λ _ → X) (λ _ → h)

  -- Sum of statistics across coordinates: (x₀, …, x_{N−1}) ↦ Σᵢ Tⱼ(xᵢ)
  sumTⁿ : ∀ {X : QBS S} (N : ℕ) (k : ℕ) (T : Fin k → SgT X) → Fin k → SgT (Xⁿ N X)
  sumTⁿ {X} zero k T j = constT 0S
  sumTⁿ {X} (suc N) k T j = (T j ∘T (fstQ S)) +T (sumTⁿ N k T j ∘T (sndQ S))

  private
    sumT-resp : ∀ {X : QBS S} N {F G : Fin N → SgT X} → (∀ i → F i ≈T G i) → sumT N F ≈T sumT N G
    sumT-resp zero e = ≈T-refl
    sumT-resp (suc N) e = +T-≈T (e zero) (sumT-resp N (λ i → e (suc i)))

    sumT-∘T : ∀ {X Y : QBS S} N (F : Fin N → SgT Y) (φ : Hom S X Y) → sumT N (λ i → F i ∘T φ) ≈T sumT N F ∘T φ
    sumT-∘T zero F φ = ≈T-refl
    sumT-∘T (suc N) F φ = +T-≈T ≈T-refl (sumT-∘T N (λ i → F (suc i)) φ)

  -- it is Σᵢ T ∘ projᵢ
  sumTⁿ-proj : ∀ {X : QBS S} (N : ℕ) (k : ℕ) (T : Fin k → SgT X) (j : Fin k) →
    sumTⁿ N k T j ≈T sumT N (λ i → T j ∘T projⁿ {N} {X} i)
  sumTⁿ-proj zero k T j = ≈T-refl
  sumTⁿ-proj {X} (suc N) k T j = +T-≈T ≈T-refl (≈T-trans ih (≈T-trans (≈T-sym (sumT-∘T N F (sndQ S)))
    (sumT-resp N (λ i x → refl , refl))))
    where
      F = λ i → T j ∘T projⁿ {N} {X} i
      ih : _≈T_ {Xⁿ (suc N) X} (sumTⁿ N k T j ∘T sndQ S) (sumT N F ∘T sndQ S)
      ih x = sumTⁿ-proj N k T j (proj₂ x)

  FinT-sumTⁿ : ∀ {X : QBS S} (N : ℕ) (k : ℕ) (T : Fin k → SgT X) → FinTs T → FinTs (sumTⁿ N k T)
  FinT-sumTⁿ zero k T fin j = FinT-constT 0S
  FinT-sumTⁿ (suc N) k T fin j = FinT-+T (FinT-∘T (fstQ S) (fin j)) (FinT-∘T (sndQ S) (FinT-sumTⁿ N k T fin j))

  -- The partition function of N independent draws, as a rectangle: ∫ ∏ᵢ w(xᵢ) dh^{⊗N} ≈ Z(η)ᴺ
  product-partition : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    ∫ᴹ (prodⁿ N (λ _ → X) (λ _ → h)) (prodT N (λ _ → X) (λ _ → weight k η T)) ≈ ∏ⁿ N (λ _ → partition h k η T)
  product-partition h N k η T = ∫-rectⁿ N (λ _ → _) (λ _ → h) (λ _ → weight k η T)

  -- The weight of the summed statistic is the product of the weights: e^{⟨η, Σᵢ T(xᵢ)⟩} ≈ ∏ᵢ e^{⟨η, T(xᵢ)⟩}
  weight-sumTⁿ : ∀ {X : QBS S} (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → FinTs T →
    _≈H_ S (weight k η (sumTⁿ N k T)) (prodT N (λ _ → X) (λ _ → weight k η T))
  weight-sumTⁿ zero k η T fin {x} = trans (expWT-≈T (dotT-0 k η) {x}) (expWT-0 x)
  weight-sumTⁿ {X} (suc N) k η T fin {x} = trans (expWT-≈T (dotT-+ k η F G) {x})
    (trans (expWT-+T (FinT-dotT k η F fF) (FinT-dotT k η G fG) x)
    (*-cong (expWT-≈T (dotT-∘T k η T (fstQ S)) {x})
            (trans (expWT-≈T (dotT-∘T k η (sumTⁿ N k T) (sndQ S)) {x}) (weight-sumTⁿ N k η T fin {proj₂ x}))))
    where
      F = λ j → T j ∘T fstQ S
      G = λ j → sumTⁿ N k T j ∘T sndQ S
      fF = λ j → FinT-∘T (fstQ S) (fin j)
      fG = λ j → FinT-∘T (sndQ S) (FinT-sumTⁿ N k T fin j)

  -- Z_N(η) ≈ Z(η)ᴺ
  partition-sumTⁿ : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) → FinTs T →
    partition (baseⁿ N h) k η (sumTⁿ N k T) ≈ ∏ⁿ N (λ _ → partition h k η T)
  partition-sumTⁿ h N k η T fin =
    trans (∫ᴹ-cong (baseⁿ N h) (λ x → weight-sumTⁿ N k η T fin {x})) (product-partition h N k η T)

  private
    prodF-∏ⁿ : ∀ N (a : Fin N → Cut) → prodF N a ≈ ∏ⁿ N a
    prodF-∏ⁿ zero a = refl
    prodF-∏ⁿ (suc N) a = *-cong refl (prodF-∏ⁿ N (λ j → a (suc j)))

  -- the normaliser of N draws is nᴺ
  product-norm : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut) →
    FinTs T → partition h k η T * n ≈ 1# → partition (baseⁿ N h) k η (sumTⁿ N k T) * ∏ⁿ N (λ _ → n) ≈ 1#
  product-norm h N k η T n fin hn =
    trans (*-cong (trans (partition-sumTⁿ h N k η T fin) (sym (prodF-∏ⁿ N _))) (sym (prodF-∏ⁿ N _)))
    (trans (prodF-mul N (λ _ → partition h k η T) (λ _ → n)) (trans (prodF-cong N (λ _ → hn)) (prodF-one N)))

  private
    expFam-zero : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut)
      (fin : FinTs T) (hn : partition h k η T * n ≈ 1#) →
      _≈ᴹ_ {Xⁿ 0 X} (prodⁿ 0 (λ _ → X) (λ _ → probPre h k η T n hn))
        (probPre (baseⁿ 0 h) k η (sumTⁿ 0 k T) 1# (product-norm h 0 k η T n fin hn))
    expFam-zero h k η T n fin hn g = sym (trans (∫ᴹ-scale 1# (reweightPre w0 _) g)
      (trans (*-identityˡ _) (trans (∫ᴹ-reweight w0 _ g) (trans (∫ᴹ-η tt (mulH w0 g))
      (trans (trans (*-cong (weight-sumTⁿ zero k η T fin {tt}) refl) (*-identityˡ _)) (sym (∫ᴹ-η tt g)))))))
      where
        w0 = weight k η (sumTⁿ zero k T)

    weight-split : ∀ {X : QBS S} (N k : ℕ) (η : Vec k) (T : Fin k → SgT X) → FinTs T →
      _≈H_ S (mulH {Xⁿ (suc N) X} (_∘H_ S (weight k η T) (fstQ S)) (_∘H_ S (weight k η (sumTⁿ N k T)) (sndQ S)))
        (weight k η (sumTⁿ (suc N) k T))
    weight-split N k η T fin {x} =
      trans (*-cong refl (weight-sumTⁿ N k η T fin {proj₂ x})) (sym (weight-sumTⁿ (suc N) k η T fin {x}))

  -- the law of N independent draws from P_η is the family on Xᴺ with base h^{⊗N}, statistic Σᵢ T ∘ projᵢ, normaliser nᴺ
  product-expFam : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut)
    (fin : FinTs T) (hn : partition h k η T * n ≈ 1#) →
    _≈ᴹ_ {Xⁿ N X} (prodⁿ N (λ _ → X) (λ _ → probPre h k η T n hn))
      (probPre (baseⁿ N h) k η (sumTⁿ N k T) (∏ⁿ N (λ _ → n)) (product-norm h N k η T n fin hn))
  product-expFam h zero k η T n fin hn = expFam-zero h k η T n fin hn
  product-expFam {X} h (suc N) k η T n fin hn g =
    trans (prod-cong {X} {Xⁿ N X} (λ f → refl) (product-expFam h N k η T n fin hn) g)
    (trans (prod-scale n nN (reweightPre w h) (reweightPre wN hN) g) (trans (∫ᴹ-scale (n * nN) _ g)
    (trans (*-cong refl (trans (prod-reweight w wN h hN g) (reweight-cong (prodPre h hN) (λ x → weight-split N k η T fin {x}) g)))
    (sym (∫ᴹ-scale (n * nN) _ g)))))
    where
      w = weight k η T
      wN = weight k η (sumTⁿ N k T)
      hN = baseⁿ N h
      nN = ∏ⁿ N (λ _ → n)

  -- the same for an iid family of random variables X₀, …, X_{N−1} with law P_η
  IID-expFam : ∀ {Ω X : QBS S} (P : C.Pre Ω) (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) (n : Cut)
    (fin : FinTs T) (hn : partition h k η T * n ≈ 1#) (Xs : Fin N → Hom S Ω X) →
    IID P (probPre h k η T n hn) N Xs →
    _≈ᴹ_ {Xⁿ N X} (law P (tupleQ N (λ _ → X) Xs))
      (probPre (baseⁿ N h) k η (sumTⁿ N k T) (∏ⁿ N (λ _ → n)) (product-norm h N k η T n fin hn))
  IID-expFam P h N k η T n fin hn Xs iid f = trans (iid f) (product-expFam h N k η T n fin hn f)

  -- 0 < Z_N(η) < ∞ when 0 < Z(η) < ∞
  PosQ-partitionⁿ : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    FinTs T → PosQ (partition h k η T) → PosQ (partition (baseⁿ N h) k η (sumTⁿ N k T))
  PosQ-partitionⁿ h N k η T fin pz =
    PosQ-resp (sym (partition-sumTⁿ h N k η T fin)) (PosQ-∏ⁿ N {partition h k η T} pz)

  BndQ-partitionⁿ : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    FinTs T → BndQ (partition h k η T) → BndQ (partition (baseⁿ N h) k η (sumTⁿ N k T))
  BndQ-partitionⁿ h N k η T fin bz =
    BndQ-resp (sym (partition-sumTⁿ h N k η T fin)) (BndQ-∏ⁿ N {partition h k η T} bz)

  -- the log-partition of N draws is N · A(η)
  logPartition-sumTⁿ : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    (fin : FinTs T) (pz : PosQ (partition h k η T)) (bz : BndQ (partition h k η T))
    (pzN : PosQ (partition (baseⁿ N h) k η (sumTⁿ N k T))) (bzN : BndQ (partition (baseⁿ N h) k η (sumTⁿ N k T))) →
    logPartition (baseⁿ N h) k η (sumTⁿ N k T) pzN bzN ≃ scaleA N (logPartition h k η T pz bz)
  logPartition-sumTⁿ h N k η T fin pz bz pzN bzN =
    ≃-trans (logS-cong pzN bzN (PosQ-∏ⁿ N {Z} pz) (BndQ-∏ⁿ N {Z} bz) (partition-sumTⁿ h N k η T fin))
      (logS-∏ⁿ N pz bz (PosQ-∏ⁿ N {Z} pz) (BndQ-∏ⁿ N {Z} bz))
    where
      Z = partition h k η T

  ----------------------------------------------------------------------------
  -- Instance: Exp(1)

  private
    exp1-pos-step : ∀ x → ((0# * x) + (1# * 0#)) + 0# ≈ 0#
    exp1-pos-step x = trans (+-cong (trans (+-cong (zeroˡ x) (zeroʳ 1#)) (+-identityˡ 0#)) refl)
      (+-identityˡ 0#)

    exp1-neg-step : ∀ x → ((0# * 0#) + (1# * x)) + 0# ≈ x
    exp1-neg-step x = trans (+-cong (trans (+-cong (zeroˡ 0#) (*-identityˡ x)) (+-identityˡ x)) refl)
      (+-identityʳ x)

    exp1-weight-pt : ∀ x → (Func.to (Hom.map (weight 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW))) x) ≈
      (Func.to (Hom.map negExpH) x)
    exp1-weight-pt x = trans (*-cong (trans (expC-cong lem (exp1-pos-step x)) (expC-zero lem))
                                     (negExp-cong (exp1-neg-step x)))
      (*-identityˡ _)

  expFam-Exp1 : Pre (XW WQ)
  expFam-Exp1 = probPre lebPre 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW) 1# hn
    where
      hn : partition lebPre 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW) * 1# ≈ 1#
      hn = trans (*-identityʳ _) (trans (∫ᴹ-cong lebPre exp1-weight-pt) ∫ᴹ-leb-negExp-norm)

  expFam-Exp1-agree : expFam-Exp1 ≈ᴹ expDistW
  expFam-Exp1-agree f = begin
    ∫ᴹ expFam-Exp1 f                   ≈⟨ ∫ᴹ-scale 1# (reweightPre w1 lebPre) f ⟩
    1# * ∫ᴹ (reweightPre w1 lebPre) f  ≈⟨ *-identityˡ _ ⟩
    ∫ᴹ (reweightPre w1 lebPre) f       ≈⟨ ∫ᴹ-reweight w1 lebPre f ⟩
    ∫ᴹ lebPre (mulH w1 f)              ≈⟨ ∫ᴹ-cong lebPre (λ x → *-cong (exp1-weight-pt x) refl) ⟩
    ∫ᴹ lebPre (mulH negExpH f)         ≈⟨ sym (∫ᴹ-expDistW f) ⟩
    ∫ᴹ expDistW f                      ∎
    where
      w1 : Hom S WQ WQ
      w1 = weight 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW)

  ----------------------------------------------------------------------------
  -- Instance: Exp(λ), for a rate l with reciprocal c (the data of `ExpRateInt.Int`)

  module ExpRate (l c : Cut) (μ ν : ℕ) (lc : l * c ≈ 1#) (lμ : l ≤ natE (suc μ)) (cν : c ≤ natE (suc ν)) where

    lB : Bnd l
    lB = suc μ , ≤-trans lμ (≤-reflexive (natE≈nat (suc μ)))

    -- the natural parameter −λ, the density λ e^{−λx}
    rateη : Vec 1
    rateη _ = -S ι lB

    dλ : Hom S WQ WQ
    dλ = scaleH l (negExpRH l)

    private
      Wλ : Hom S WQ WQ
      Wλ = weight 1 rateη (λ _ → fromW {WQ} idW)

      rate-pos-step : ∀ x → ((0# * x) + (l * 0#)) + 0# ≈ 0#
      rate-pos-step x = trans (+-cong (trans (+-cong (zeroˡ x) (zeroʳ l)) (+-identityˡ 0#)) refl) (+-identityˡ 0#)

      rate-neg-step : ∀ x → ((0# * 0#) + (l * x)) + 0# ≈ l * x
      rate-neg-step x = trans (+-cong (trans (+-cong (zeroˡ 0#) refl) (+-identityˡ (l * x))) refl) (+-identityʳ (l * x))

      rate-weight-pt : ∀ x → map Wλ ⟨$⟩ x ≈ map (negExpRH l) ⟨$⟩ x
      rate-weight-pt x = trans (*-cong (trans (expC-cong lem (rate-pos-step x)) (expC-zero lem))
                                       (negExp-cong (rate-neg-step x))) (*-identityˡ _)

    partition-Exp : partition lebPre 1 rateη (λ _ → fromW {WQ} idW) ≈ c
    partition-Exp = trans (∫ᴹ-cong lebPre rate-weight-pt) (Int.∫-negExpR l c μ ν lc lμ cν)

    expFam-Exp-norm : partition lebPre 1 rateη (λ _ → fromW {WQ} idW) * l ≈ 1#
    expFam-Exp-norm = trans (*-cong partition-Exp refl) (trans (*-comm c l) lc)

    expFam-Exp : Pre (XW WQ)
    expFam-Exp = probPre lebPre 1 rateη (λ _ → fromW {WQ} idW) l expFam-Exp-norm

    expFam-Exp-agree : (nrm : ∫ᴹ {WQ} lebPre dλ ≈ 1#) → expFam-Exp ≈ᴹ ιPre {WQ} (densDist dλ nrm)
    expFam-Exp-agree nrm f = trans (∫ᴹ-scale l (reweightPre Wλ lebPre) f)
      (trans (*-cong refl (trans (∫ᴹ-reweight Wλ lebPre f) (∫ᴹ-cong lebPre (λ x → *-cong (rate-weight-pt x) refl))))
      (trans (sym (cmul lebPre l (mulH (negExpRH l) f)))
      (trans (∫ᴹ-cong lebPre (λ x → sym (*-assoc l _ _))) (sym (∫-dens dλ nrm f)))))

  ----------------------------------------------------------------------------
  -- Instance: the Gaussian with known variance, T = x and h = e^{−x²/2} dλ on the real line

  gaussBase : Pre (XW RQ)
  gaussBase = reweightPre {RQ} (copairH phiH phiH) lebR

  gaussFam : (η : Sg) (n : Cut) → partition gaussBase 1 (λ _ → η) (λ _ → idT) * n ≈ 1# → Pre (XW RQ)
  gaussFam η n hn = probPre gaussBase 1 (λ _ → η) (λ _ → idT) n hn

  partition-gauss0 : ∀ c → ∫ᴹ {WQ} lebPre phiH ≈ c → partition gaussBase 1 (λ _ → 0S) (λ _ → idT) ≈ c + c
  partition-gauss0 c hc = trans (∫ᴹ-reweight {RQ} dR lebR w0)
    (trans (∫ᴹ-cong {RQ} lebR {mulH {RQ} dR w0} {dR} (λ x → trans (*-cong refl (weight-0S 1 (λ _ → idT) x)) (*-identityʳ _)))
      (lebR-sym phiH c hc))
    where
      dR = copairH phiH phiH
      w0 = weight 1 (λ _ → 0S) (λ _ → idT)

  gauss0-norm : ∀ c → ∫ᴹ {WQ} lebPre phiH ≈ c → ∀ n → (c + c) * n ≈ 1# →
    partition gaussBase 1 (λ _ → 0S) (λ _ → idT) * n ≈ 1#
  gauss0-norm c hc n nn = trans (*-cong (partition-gauss0 c hc) refl) nn

  -- at η = 0 the family is the standard Gaussian of `RealDensity.Sym` (`GaussReal.gaussR` for c = Z, n = n′)
  gaussFam0-agree : ∀ c (hc : ∫ᴹ {WQ} lebPre phiH ≈ c) n (nn : (c + c) * n ≈ 1#) →
    _≈ᴹ_ {RQ} (gaussFam 0S n (gauss0-norm c hc n nn)) (ιPre {RQ} (Sym.symDist phiH c hc n nn))
  gaussFam0-agree c hc n nn f = trans (∫ᴹ-scale {RQ} n (reweightPre {RQ} w0 gaussBase) f)
    (trans (*-cong refl (trans (∫ᴹ-reweight {RQ} w0 gaussBase f) (trans (∫ᴹ-reweight {RQ} dR lebR (mulH {RQ} w0 f))
      (trans (∫ᴹ-cong {RQ} lebR {mulH {RQ} dR (mulH {RQ} w0 f)} {mulH {RQ} dR f} (λ x → *-cong refl w0f))
        (∫ᴹ-lebR-dens phiH phiH f)))))
    (sym (Sym.∫-sym phiH c hc n nn f)))
    where
      dR = copairH phiH phiH
      w0 = weight 1 (λ _ → 0S) (λ _ → idT)
      w0f : ∀ {x} → (map w0 ⟨$⟩ x) * (map f ⟨$⟩ x) ≈ map f ⟨$⟩ x
      w0f {x} = trans (*-cong (weight-0S 1 (λ _ → idT) x) refl) (*-identityˡ _)
