{-# OPTIONS --safe --without-K #-}

-- The core of Chebyshev's inequality about any centre c ≃ E g (helper for `Inference/WeakLaw`; plan 05 item 50).
--   * `Ex-dev`: E (g − c)² ≃ Var g when c ≃ E g (`SignedVar.Ex-cen`, then the ring identity of `Var-cen`);
--   * `chebyshev-at`: if e² χ + (g − c)²⁻ ≤ (g − c)²⁺ pointwise, then e² ∫χ + Var⁻ ≤ Var⁺ (i.e. e² ∫χ ≤ᵛ Var g).
-- Route: `SignedExpect.Ex-mono` on fromW (e² χ) and (g − c)², with `Product.cmul` and `Dominated.prob-mass`, then
-- `Ex-dev` and `WeakLawAlg.cong-≤`.  The centre is arbitrary so that the weak law may use c = n μ ≃ E Sₙ.
module QBS.Inference.WeakLawCheb where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.Product using (module Product)
open import QBS.Continuous.Dominated using (module Dominated)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Inference.WeakLawAlg using (module WeakLawAlg)

module WeakLawCheb (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; +-identityʳ; ≤-trans; ≤-reflexive)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; 1S; ≃-refl; ≃-trans; +S-cong; -S-cong; *S-cong; *S-congˡ; *S-congʳ)
  open Bounded.Sg A using (pos; neg)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open Product (lemOf lem₁) using (cmul)
  open Dominated lem₁ using (prob-mass)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; _*T_; fromW)
  open SignedExpect lem₁ using (Ex; Ex-mono)
  open SignedVar lem₁ using (Int₂; Var; cen; Int-cen; Ex-cen)
  open SignedVarAlg lem₁ using (two-c; R-cen)
  open WeakLawAlg lem₁ using (cong-≤)
  open QBS
  open Hom

  module _ {Ω : QBS S} (P : C.Pre Ω) where

    -- E (g − c)² ≃ Var g when c ≃ E g
    Ex-dev : ∀ (g : SgT Ω) (ij : Int₂ P g) c → c ≃ Ex {Ω} (ιPre {Ω} P) g (proj₁ ij) →
      Ex {Ω} (ιPre {Ω} P) (cen P g c *T cen P g c) (Int-cen P g c ij) ≃ Var P g ij
    Ex-dev g ij c ec = ≃-trans (Ex-cen P g c ij) (≃-trans (+S-cong (+S-cong ≃-refl (-S-cong (*S-cong
      (*S-congʳ (1S +S 1S) ec) ≃-refl))) (*S-cong ec ec)) (≃-trans (+S-cong (+S-cong ≃-refl (-S-cong
      (*S-congˡ _ (two-c _)))) ≃-refl) (R-cen _ _)))

    chebyshev-at : ∀ (g : SgT Ω) (ij : Int₂ P g) (χ : Hom S Ω WQ) e c → c ≃ Ex {Ω} (ιPre {Ω} P) g (proj₁ ij) →
      (∀ ω → (e * e) * (map χ ⟨$⟩ ω) + at⁻ (cen P g c *T cen P g c) ω ≤ at⁺ (cen P g c *T cen P g c) ω) →
      (e * e) * ∫ᴹ {Ω} (ιPre {Ω} P) χ + neg (Var P g ij) ≤ pos (Var P g ij)
    chebyshev-at g ij χ e c ec hyp = cong-≤ (≤-trans (≤-reflexive (+-cong (sym (cmul (ιPre {Ω} P) (e * e) χ)) refl))
      (≤-trans mono (≤-reflexive (trans (+-cong refl (prob-mass {Ω} P 0#)) (+-identityʳ _))))) (Ex-dev g ij c ec)
      where
        f = fromW {Ω} (mulH {Ω} (constW {Ω} (e * e)) χ)
        mono = Ex-mono {Ω} (ιPre {Ω} P) f (cen P g c *T cen P g c) (λ ω → ≤-trans (hyp ω) (≤-reflexive (sym (+-identityʳ _))))
