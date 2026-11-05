{-# OPTIONS --safe --without-K #-}

-- Gaussian vectors (plan 05, item 53).  On a probability P on Ω:
--   * for an iid family Zs : Fin n → Ω ⇒ Y with law μ and a signed test f with mean m and variance v under μ, the
--     coordinates f ∘ Zᵢ (`IIDLaw.obs`) form a random vector (`RV-iid`, `Continuous/RandomVector`) with mean vector
--     (m, …, m) (`mean-iid`), covariance v I (`cov-iid`) and E Σᵢ (f ∘ Zᵢ)² ≃ n (v + m²) (`norm2-iid`); the affine image
--     A Z + b has mean A (m, …, m) + b and covariance A (v I) Aᵀ (`aff-mean`, `aff-cov`);
--   * the standard normal `γ = N(0, 1)` (`GaussShift.gaussμ` at s = 1, μ = 0) has mean 0 and second moment 1
--     (`γ-em`, `γ-es`), so iid N(0, 1) coordinates idT ∘ Zᵢ have mean 0, covariance I and E ‖Z‖² ≃ n (`gauss-mean`,
--     `gauss-cov`, `gauss-norm2`), and N(b, A Aᵀ) is the random vector A Z + b: mean b, covariance A Aᵀ (`gaussV-mean`,
--     `gaussV-cov`);
--   * the canonical N(0, Iₙ): `Nⁿ n = γ^{⊗n}` on RQⁿ (`FinProdProb.prodPⁿ`), whose coordinates are iid N(0, 1)
--     (`std-iid`), with mean 0, covariance I and E ‖Z‖² ≃ n (`std-mean`, `std-cov`, `std-norm2`).
-- Route: `RV-iid`, `mean-iid` from `IID.IID-moments` (each coordinate has the moments of f under μ); `cov-iid` on the
-- diagonal by `RandomVector.cov-diag` and the variance, off the diagonal by `RandomVector.cov-indep` with
-- `IID.IID-indep`; `norm2-iid` by `SgSample.Ex-sumG`; `aff-mean`, `aff-cov` from `RandomVector.mean-aff`, `cov-aff` and
-- `mean-iid`, `cov-iid` under `SgLinAlg.Σ-cong`.  `γ-em`, `γ-es` from `GaussVar.Ex-id` and `Var-gaussμ`; the Gaussian
-- statements instantiate the general ones (1 v ≃ v, 0 + x ≃ x, `SgLinAlg.idM-*Mv`); the canonical ones are the
-- Gaussian ones at P = Nⁿ n with `FinProdProb.proj-iid`.  The ring-level lemmas (`idM` entries, congruences, variance
-- from the second moment) are in `GaussVectorAlg`.
module QBS.Inference.GaussVector where

open import Algebra using (CommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.FinProdProb using (module FinProdProb)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.IID using (module IID)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Inference.GaussShift using (module GaussShift)
open import QBS.Inference.GaussVar using (module GaussVar)
open import QBS.Inference.IIDLaw using (module IIDLaw)
open import QBS.Inference.GaussVectorAlg using (module GaussVectorAlg)

module GaussVector (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#; 1#; *-identityˡ)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; 0S; 1S; finite; signedRing; ≃-refl; ≃-trans; ≃-sym; +S-cong; *S-cong
    ; -S-cong; *S-identityˡ; +S-identityˡ; ι-*)
  module SR = CommutativeRing signedRing
  open SubSemiring finite using (Is-0; Is-1)
  open SgLinAlg signedRing using (Vec; Mat; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ; idM)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open RealLine lem₁ using (RQ)
  open SignedTest lem₁ using (SgT; _*T_; idT)
  open SignedExpect lem₁ using (Int; Ex)
  open SignedVar lem₁ using (Var)
  open SgMoments lem₁ using (natS; sumT; Moments)
  open SgSample lem₁ using (Int-sum; Ex-sumG)
  open FinProd lem₁ using (ΠQ; projQ)
  open FinProdProb lem₁ using (prodPⁿ; proj-iid)
  open ProdBridge lem₁ using (ι-mass)
  open IID lem₁ using (IID; IID-moments; IID-indep)
  open RandomVector lem₁ using (RV; meanV; covM; affT; RV-aff; cov-diag; cov-indep; mean-aff; cov-aff)
  open GaussVectorAlg signedRing
  open GaussShift lem₁ using (gaussμ)
  open GaussVar lem₁ using (Int-id; Int-sq; Ex-id; Var-gaussμ)
  open IIDLaw lem₁ using (obs)

  -- iid coordinates
  module _ {Ω : QBS S} (P : C.Pre Ω) {Y : QBS S} (μ : C.Pre (XW Y)) (h : ∫ᴹ {Y} μ (constW {Y} 1#) ≈ 1#)
    (f : SgT Y) (m v : Sg) (i : Int {Y} μ f) (j : Int {Y} μ (f *T f))
    (em : Ex {Y} μ f i ≃ m) (es : Ex {Y} μ (f *T f) j ≃ v +S m *S m) where

    private
      E = ιPre {Ω} P

    -- the moments of the coordinates
    mom : ∀ n Zs → IID P μ n Zs → Moments P n (obs f n Zs) m v
    mom n Zs d = IID-moments P μ n Zs f m v d h i j em es

    RV-iid : ∀ n Zs → IID P μ n Zs → RV P n (obs f n Zs)
    RV-iid n Zs d = proj₁ (mom n Zs d)

    mean-iid : ∀ n Zs (d : IID P μ n Zs) → meanV P n (obs f n Zs) (RV-iid n Zs d) ≈V (λ _ → m)
    mean-iid n Zs d k = proj₁ (proj₂ (mom n Zs d)) k

    -- the variance of a coordinate
    var-ent : ∀ n Zs (d : IID P μ n Zs) k →
      Ex {Ω} E (obs f n Zs k *T obs f n Zs k) (proj₂ (RV-iid n Zs d k))
        +S SR.-_ (Ex {Ω} E (obs f n Zs k) (proj₁ (RV-iid n Zs d k))
        *S Ex {Ω} E (obs f n Zs k) (proj₁ (RV-iid n Zs d k))) ≃ v
    var-ent n Zs d k = ≃-trans (+S-cong (proj₁ (proj₂ (proj₂ (mom n Zs d))) k)
      (-S-cong (*S-cong (mean-iid n Zs d k) (mean-iid n Zs d k)))) (var-cancel v m)

    cov-ent : ∀ n Zs (d : IID P μ n Zs) k l → Dec (k ≡ l) →
      covM P n (obs f n Zs) (RV-iid n Zs d) k l ≃ v *S idM k l
    cov-ent n Zs d k .k (yes refl) = ≃-trans (≃-trans (cov-diag P n (obs f n Zs) (RV-iid n Zs d) k) (var-ent n Zs d k))
      (≃-sym (≃-trans (*S-cong ≃-refl (idM-diag k)) (SR.*-identityʳ v)))
    cov-ent n Zs d k l (no ne) = ≃-trans (cov-indep P n (λ _ → Y) Zs (λ _ → f) (IID-indep P μ n Zs d h)
      (RV-iid n Zs d) k l ne) (≃-sym (≃-trans (*S-cong ≃-refl (idM-off k l ne)) (SR.zeroʳ v)))

    cov-iid : ∀ n Zs (d : IID P μ n Zs) → covM P n (obs f n Zs) (RV-iid n Zs d) ≈M (λ k l → v *S idM k l)
    cov-iid n Zs d k l = cov-ent n Zs d k l (k ≟ l)

    norm2-iid : ∀ n Zs (d : IID P μ n Zs) → Ex {Ω} E (sumT n (λ k → obs f n Zs k *T obs f n Zs k))
      (Int-sum P n (λ k → obs f n Zs k *T obs f n Zs k) (λ k → proj₂ (RV-iid n Zs d k))) ≃ natS n *S (v +S m *S m)
    norm2-iid n Zs d = Ex-sumG P n (λ k → obs f n Zs k *T obs f n Zs k) (v +S m *S m)
      (λ k → proj₂ (RV-iid n Zs d k)) (λ k → proj₁ (proj₂ (proj₂ (mom n Zs d))) k)

    -- the affine image A Z + b
    aff-mean : ∀ {p} n Zs (d : IID P μ n Zs) (M : Mat p n) (b : Vec p) →
      meanV P p (affT P M b (obs f n Zs)) (RV-aff P M b (obs f n Zs) (RV-iid n Zs d)) ≈V (M *Mv (λ _ → m)) +V b
    aff-mean n Zs d M b k = ≃-trans (mean-aff P M b (obs f n Zs) (RV-iid n Zs d) k)
      (+S-cong (*Mv-cong M (mean-iid n Zs d) k) ≃-refl)

    aff-cov : ∀ {p} n Zs (d : IID P μ n Zs) (M : Mat p n) (b : Vec p) →
      covM P p (affT P M b (obs f n Zs)) (RV-aff P M b (obs f n Zs) (RV-iid n Zs d)) ≈M (M *M (λ k l → v *S idM k l)) *M (M ᵀ)
    aff-cov n Zs d M b = ≈M-trans (cov-aff P M b (obs f n Zs) (RV-iid n Zs d))
      (*M-cong (*M-cong (λ _ _ → ≃-refl) (cov-iid n Zs d)) (λ _ _ → ≃-refl))

  -- the standard normal N(0, 1)
  γ : C.Pre RQ
  γ = gaussμ 1# 1# (*-identityˡ 1#) Is-1 Is-1 0# Is-0

  γ-mass : ∫ᴹ {RQ} (ιPre {RQ} γ) (constW {RQ} 1#) ≈ 1#
  γ-mass = ι-mass {RQ} γ

  γ-i : Int {RQ} (ιPre {RQ} γ) idT
  γ-i = Int-id 1# 1# (*-identityˡ 1#) Is-1 Is-1 0# Is-0

  γ-j : Int {RQ} (ιPre {RQ} γ) (idT *T idT)
  γ-j = Int-sq 1# 1# (*-identityˡ 1#) Is-1 Is-1 0# Is-0

  γ-var : Var {RQ} γ idT (γ-i , γ-j) ≃ 1S
  γ-var = ≃-trans (Var-gaussμ 1# 1# (*-identityˡ 1#) Is-1 Is-1 0# Is-0) (≃-trans (ι-* {1#} {1#} Is-1 Is-1) (*S-identityˡ 1S))

  γ-em : Ex {RQ} (ιPre {RQ} γ) idT γ-i ≃ 0S
  γ-em = Ex-id 1# 1# (*-identityˡ 1#) Is-1 Is-1 0# Is-0

  γ-es : Ex {RQ} (ιPre {RQ} γ) (idT *T idT) γ-j ≃ 1S +S 0S *S 0S
  γ-es = second-moment {e = Ex {RQ} (ιPre {RQ} γ) idT γ-i} γ-var γ-em

  -- iid N(0, 1) coordinates, and N(b, A Aᵀ)
  module _ {Ω : QBS S} (P : C.Pre Ω) where

    private
      Rγ : ∀ n Zs → IID P (ιPre {RQ} γ) n Zs → RV P n (obs idT n Zs)
      Rγ = RV-iid P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es

    gauss-mean : ∀ n Zs (d : IID P (ιPre {RQ} γ) n Zs) → meanV P n (obs idT n Zs) (Rγ n Zs d) ≈V (λ _ → 0S)
    gauss-mean n Zs d = mean-iid P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n Zs d

    gauss-cov : ∀ n Zs (d : IID P (ιPre {RQ} γ) n Zs) → covM P n (obs idT n Zs) (Rγ n Zs d) ≈M idM
    gauss-cov n Zs d k l = ≃-trans (cov-iid P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n Zs d k l)
      (*S-identityˡ (idM k l))

    gauss-norm2 : ∀ n Zs (d : IID P (ιPre {RQ} γ) n Zs) → Ex {Ω} (ιPre {Ω} P) (sumT n (λ k → obs idT n Zs k *T obs idT n Zs k))
      (Int-sum P n (λ k → obs idT n Zs k *T obs idT n Zs k) (λ k → proj₂ (Rγ n Zs d k))) ≃ natS n
    gauss-norm2 n Zs d = ≃-trans (norm2-iid P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n Zs d)
      (≃-trans (*S-cong ≃-refl (≃-trans (+S-cong ≃-refl (SR.zeroˡ 0S)) (SR.+-identityʳ 1S))) (SR.*-identityʳ (natS n)))

    gaussV-mean : ∀ {p} n Zs (d : IID P (ιPre {RQ} γ) n Zs) (M : Mat p n) (b : Vec p) →
      meanV P p (affT P M b (obs idT n Zs)) (RV-aff P M b (obs idT n Zs) (Rγ n Zs d)) ≈V b
    gaussV-mean n Zs d M b k = ≃-trans (aff-mean P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n Zs d M b k)
      (≃-trans (+S-cong (*Mv-0 M k) ≃-refl) (+S-identityˡ (b k)))

    gaussV-cov : ∀ {p} n Zs (d : IID P (ιPre {RQ} γ) n Zs) (M : Mat p n) (b : Vec p) →
      covM P p (affT P M b (obs idT n Zs)) (RV-aff P M b (obs idT n Zs) (Rγ n Zs d)) ≈M M *M (M ᵀ)
    gaussV-cov n Zs d M b = ≈M-trans (aff-cov P (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n Zs d M b)
      (*M-cong (λ k l → ≃-trans (*M-cong {M = M} (λ _ _ → ≃-refl) (λ k l → *S-identityˡ (idM k l)) k l) (*M-idM M k l))
        (λ _ _ → ≃-refl))

  -- the canonical N(0, Iₙ) on RQⁿ
  Nⁿ : ∀ n → C.Pre (ΠQ n (λ _ → RQ))
  Nⁿ n = prodPⁿ n (λ _ → RQ) (λ _ → γ)

  std-iid : ∀ n → IID (Nⁿ n) (ιPre {RQ} γ) n (projQ n (λ _ → RQ))
  std-iid n = proj-iid {RQ} γ n

  std-mean : ∀ n → meanV (Nⁿ n) n (obs idT n (projQ n (λ _ → RQ)))
    (RV-iid (Nⁿ n) (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n (projQ n (λ _ → RQ)) (std-iid n)) ≈V (λ _ → 0S)
  std-mean n = gauss-mean (Nⁿ n) n (projQ n (λ _ → RQ)) (std-iid n)

  std-cov : ∀ n → covM (Nⁿ n) n (obs idT n (projQ n (λ _ → RQ)))
    (RV-iid (Nⁿ n) (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n (projQ n (λ _ → RQ)) (std-iid n)) ≈M idM
  std-cov n = gauss-cov (Nⁿ n) n (projQ n (λ _ → RQ)) (std-iid n)

  std-norm2 : ∀ n → Ex {ΠQ n (λ _ → RQ)} (ιPre {ΠQ n (λ _ → RQ)} (Nⁿ n))
    (sumT n (λ k → obs idT n (projQ n (λ _ → RQ)) k *T obs idT n (projQ n (λ _ → RQ)) k))
    (Int-sum (Nⁿ n) n (λ k → obs idT n (projQ n (λ _ → RQ)) k *T obs idT n (projQ n (λ _ → RQ)) k)
      (λ k → proj₂ (RV-iid (Nⁿ n) (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n (projQ n (λ _ → RQ)) (std-iid n) k)))
    ≃ natS n
  std-norm2 n = gauss-norm2 (Nⁿ n) n (projQ n (λ _ → RQ)) (std-iid n)
