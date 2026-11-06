{-# OPTIONS --safe --without-K #-}

-- Continuous exponential families on quasi-Borel spaces (plan 07, item 59; enabler for `ExpFamilyPost`, `ExpFamilyKL`).
--   * `ExpFam X k`: an exponential family on `X : QBS S` with `k` statistics;
--   * `dotT η T : SgT X`, the inner product statistic `⟨η, T⟩`;
--   * `weight η : Hom S X WQ`, the density weight `expWT ⟨η, T⟩`;
--   * `partition η = ∫ᴹ h (weight η)`, the partition function Z(η);
--   * `probPre η n`, the normalised probability measure when `partition η * n ≈ 1#`;
--   * `logPartition η pz bz = logS (partition η) pz bz`, the signed log-partition A(η);
--   * `sumTⁿ T`: the sum of statistics across coordinates on `Xⁿ N X`;
--   * `product-partition`: the partition function of N independent draws from the family is `Z(η)ᴺ` (`FinProd.∫-rectⁿ`);
--   * `expFam-Exp1`: the Exp(1) distribution as a 1-parameter exponential family, agreeing with `Continuous/ExpDist`.
-- Route: `ExpWeight.expWT` for weights; `FinProd.∫-rectⁿ` for product factorisation; `ExpDist` for the instance.
module QBS.Continuous.ExpFamily where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Function.Bundles using (_⟨$⟩_; Func)

open import QBS.Core
open import QBS.Limits using (1Q; fstQ; sndQ)
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.ExpLower using (expC; expC-zero; expC-cong)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ExpWeight using (module ExpWeight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.ExpDist using (module ExpDist)

module ExpFamily (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _*_; _+_; 1#; 0#; refl; sym; trans; *-cong; +-cong;
    *-identityˡ; *-identityʳ; *-comm; *-assoc; zeroˡ; zeroʳ; +-identityˡ; +-identityʳ)
  open NegExp lem using (negExp; negExp-anti)
  open Weights lem using (WQ; constW)
  open Bounded A using (Sg; signedRing; _+S_; 0S; -S_; 1S; ι; finite)
  open SgLinAlg signedRing using (Vec; _·_; Σ; _≈V_; _+V_)
  open SignedTest lem₁ using (SgT; _+T_; scaleT; constT; FinT; _≐_; fromW; _∘T_)
  open SignedLog lem₁ using (PosQ; logS)
  open SFinite lem using (module C; XW; ∫ᴹ; ∫ᴹ-cong; _≈ᴹ_)
  open C using (Pre)
  open SFiniteReweight lem using (reweightPre; ∫ᴹ-reweight; mulH)
  open SFiniteSum lem using (scalePre; ∫ᴹ-scale)
  open SFiniteNorm lem using (normPre; massP; ∫-normPre)
  open SFiniteIncl lem using (ιPre)
  open FinProd lem₁ using (ΠQ; projQ; prodⁿ; prodT; ∏ⁿ; ∫-rectⁿ; prodⁿ-cong)
  open ExpWeight lem₁ using (expW; expWT; expW-pos; expW-bnd; log-expW; expWT-cong)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineNorm lem₁ using (∫ᴹ-leb-negExp-norm)
  open ExpDist lem₁ using (expDist; massP-expW; ∫-expDist; idW) renaming (expW to expDistW; ∫ᴹ-expW to ∫ᴹ-expDistW)

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
  probPre-mass h k η T n hn =
    trans (∫ᴹ-scale n (reweightPre (weight k η T) h) (constW 1#))
      (trans (*-cong refl (∫ᴹ-reweight (weight k η T) h (constW 1#)))
        (trans (*-cong refl (∫ᴹ-cong h (λ x → *-identityʳ _)))
          (trans (*-comm n (partition h k η T)) hn)))

  -- Signed log-partition function A(η) = logS Z(η)
  logPartition : ∀ {X : QBS S} (h : Pre (XW X)) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    (pz : PosQ (partition h k η T)) (bz : BndQ (partition h k η T)) → Sg
  logPartition h k η T pz bz = logS (partition h k η T) pz bz

  -- Homogeneous product space Xᴺ
  Xⁿ : ∀ (N : ℕ) (X : QBS S) → QBS S
  Xⁿ N X = ΠQ N (λ _ → X)

  -- Coordinate projections
  projⁿ : ∀ {N : ℕ} {X : QBS S} (i : Fin N) → Hom S (Xⁿ N X) X
  projⁿ {N} {X} i = projQ N (λ _ → X) i

  -- Sum of statistics across coordinates
  sumTⁿ : ∀ {X : QBS S} (N : ℕ) (k : ℕ) (T : Fin k → SgT X) → Fin k → SgT (Xⁿ N X)
  sumTⁿ {X} zero k T j = constT 0S
  sumTⁿ {X} (suc N) k T j = (T j ∘T (fstQ S)) +T (sumTⁿ N k T j ∘T (sndQ S))

  -- The product family theorem:
  -- The partition function of N independent draws has base measure h^{\otimes N} and partition Z(η)ᴺ
  product-partition : ∀ {X : QBS S} (h : Pre (XW X)) (N : ℕ) (k : ℕ) (η : Vec k) (T : Fin k → SgT X) →
    ∫ᴹ (prodⁿ N (λ _ → X) (λ _ → h)) (prodT N (λ _ → X) (λ _ → weight k η T)) ≈ ∏ⁿ N (λ _ → partition h k η T)
  product-partition h N k η T = ∫-rectⁿ N (λ _ → _) (λ _ → h) (λ _ → weight k η T)

  -- Instance: Exp(1) distribution
  private
    negExp-cong : ∀ {x y} → x ≈ y → negExp x ≈ negExp y
    negExp-cong e = negExp-anti (proj₂ e) , negExp-anti (proj₁ e)

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
  expFam-Exp1-agree f =
    trans (∫ᴹ-scale 1# (reweightPre (weight 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW)) lebPre) f)
      (trans (*-identityˡ _)
        (trans (∫ᴹ-reweight (weight 1 (λ _ → -S 1S) (λ _ → fromW {WQ} idW)) lebPre f)
          (trans (∫ᴹ-cong lebPre (λ x → *-cong (exp1-weight-pt x) refl))
            (sym (∫ᴹ-expDistW f)))))
