{-# OPTIONS --safe --without-K #-}

-- The law of a Gaussian vector as a measure on RQᵐ, with the affine rule Cov(AZ+b) = A Cov Z Aᵀ (plan 05 item 55).  On a probability P on Ω:
--   * `coordT n i = idT ∘ projᵢ`, the coordinates on RQⁿ, and the law of A Z + b for any map Z : Ω ⇒ RQⁿ whose coordinates
--     form a random vector (`affLaw`, the push-forward along `RealAffine.affRH A b ∘ Z`): its coordinates are a random vector
--     (`affLaw-RV`) with mean A mean(Z) + b (`affLaw-mean`) and covariance A Cov(Z) Aᵀ (`affLaw-cov`), the affine rule of
--     `RandomVector` (`mean-aff`, `cov-aff`) read on the law;
--   * the Gaussian N(b, A Aᵀ) = `Nᴬ A b`, the law of A Z + b under Z ∼ N(0, Iₙ) (`GaussVector.Nⁿ`, Z the identity of RQⁿ): a
--     probability measure on RQᵐ (`Nᴬ-mass`) whose coordinates have mean b and covariance A Aᵀ (`Nᴬ-RV`, `Nᴬ-mean`,
--     `Nᴬ-cov`), matching `GaussVector.gaussV-mean`/`gaussV-cov`, which compute the same moments on the Ω side.
-- Route: `affLaw-*`: `RandomVectorLaw.RV-law`, `mean-law`, `cov-law` at h = affRH A b ∘ Z and X = coordT m, then
-- `RealAffine.idT-affRH` (≐ is symmetric) with `RandomVectorLaw.RV-≐` (coordT is a pull-back of `idT`), `mean-≐`, `cov-≐`
-- to replace the coordinates by `affT`, and `RandomVector.RV-aff`, `mean-aff`, `cov-aff`.  `Nᴬ-*` repeat the same chain at
-- P = Nⁿ n, h = affRH A b (not `affLaw-*` at Z = idH: comparing the two laws is far too slow), ending in
-- `GaussVector.gaussV-mean`/`gaussV-cov` on the Ω side (`mean-chain`, `cov-chain` are abstract in the laws so that no
-- covariance term is ever compared; unify only through the lemmas); `Nᴬ-mass` is `ProdBridge.ι-mass`.
module QBS.Inference.GaussVectorLaw where

open import Data.Nat.Base using (ℕ)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Fin.Base using (Fin)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product.Base using (proj₁)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.RealLine using (module RealLine)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.FinProd using (module FinProd)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.RandomVector using (module RandomVector)
open import QBS.Continuous.RealAffine using (module RealAffine)
open import QBS.Inference.GaussVector using (module GaussVector)
open import QBS.Inference.GaussVectorAlg using (module GaussVectorAlg)
open import QBS.Inference.IIDLaw using (module IIDLaw)
open import QBS.Continuous.RandomVectorLaw using (module RandomVectorLaw)

module GaussVectorLaw (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; 0#; 1#; refl)
  open Bounded A using (_≃_; signedRing; ≃-trans; ≃-refl; +S-cong; +S-identityˡ; *S-identityˡ)
  open SgLinAlg signedRing using (Vec; Mat; _≈V_; _≈M_; _+V_; _*Mv_; _*M_; _ᵀ; idM)
  open GaussVectorAlg signedRing using (*Mv-cong; *Mv-0; *M-cong; *M-idM; ≈M-trans)
  open Weights (lemOf lem₁) using (constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Bounded A using (0S; 1S)
  open RealLine lem₁ using (RQ)
  open SignedTest lem₁ using (SgT; _∘T_; _≐_; ≐-sym; idT; at⁺; at⁻)
  open FinProd lem₁ using (ΠQ; projQ)
  open ProdBridge lem₁ using (ι-mass)
  open RandomVector lem₁ using (RV; meanV; covM; affT; RV-aff; mean-aff; cov-aff)
  open RandomVectorLaw lem₁ using (RV-≐; mean-≐; cov-≐; RV-law; mean-law; cov-law)
  open RealAffine lem₁ using (RQⁿ; affRH; idT-affRH; zero-id)
  open IIDLaw lem₁ using (obs)
  open GaussVector lem₁ using (Nⁿ; std-iid; std-mean; std-cov; RV-iid; gaussV-mean; gaussV-cov; γ; γ-mass; γ-i; γ-j; γ-em; γ-es)
  open QBS
  open Hom

  -- the coordinates idT ∘ projᵢ on RQⁿ
  coordT : ∀ n → Fin n → SgT (RQⁿ n)
  coordT n i = _∘T_ {RQⁿ n} {RQ} idT (projQ n (λ _ → RQ) i)

  ----------------------------------------------------------------------------
  -- the law of A Z + b on RQᵐ

  module _ {Ω : QBS S} (P : C.Pre Ω) {m n} (M : Mat m n) (b : Vec m) (Z : Hom S Ω (RQⁿ n))
    (r : RV P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z)) where

    affLaw : C.Pre (RQⁿ m)
    affLaw = C.mapPre {Ω} {RQⁿ m} (_∘H_ S (affRH M b) Z) P

    private
      hh : Hom S Ω (RQⁿ m)
      hh = _∘H_ S (affRH M b) Z

      XZ : Fin n → SgT Ω
      XZ i = _∘T_ {Ω} {RQⁿ n} (coordT n i) Z

      CH : Fin m → SgT Ω
      CH k = _∘T_ {Ω} {RQⁿ m} (coordT m k) hh

      ee : ∀ k → _≐_ {Ω} (CH k) (affT P M b XZ k)
      ee k = idT-affRH P M b Z k

      zc : ∀ k x → at⁻ (CH k) x ≈ 0# ⊎ at⁺ (CH k) x ≈ 0#
      zc k x = [ inj₂ , inj₁ ]′ (zero-id (map (projQ m (λ _ → RQ) k) ⟨$⟩ (map hh ⟨$⟩ x)))

      rr : RV P m CH
      rr = RV-≐ P {X = affT P M b XZ} {Y = CH} (λ k → ≐-sym {Ω} {CH k} {affT P M b XZ k} (ee k)) zc (RV-aff P M b XZ r)

    affLaw-RV : RV affLaw m (coordT m)
    affLaw-RV = RV-law P hh m (coordT m) rr

    affLaw-mean : meanV affLaw m (coordT m) affLaw-RV ≈V (M *Mv meanV P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z) r) +V b
    affLaw-mean k = ≃-trans (mean-law P hh m (coordT m) rr k)
      (≃-trans (mean-≐ P {X = CH} {Y = affT P M b XZ} ee rr (RV-aff P M b XZ r) k) (mean-aff P M b XZ r k))

    affLaw-cov : covM affLaw m (coordT m) affLaw-RV ≈M (M *M covM P n (λ i → _∘T_ {Ω} {RQⁿ n} (coordT n i) Z) r) *M (M ᵀ)
    affLaw-cov i j = ≃-trans (cov-law P hh m (coordT m) rr i j)
      (≃-trans (cov-≐ P {X = CH} {Y = affT P M b XZ} ee rr (RV-aff P M b XZ r) i j) (cov-aff P M b XZ r i j))

  ----------------------------------------------------------------------------
  -- the Gaussian N(b, A Aᵀ)

  -- the law of A Z + b for Z ∼ N(0, Iₙ), a probability measure on RQᵐ
  Nᴬ : ∀ {m n} → Mat m n → Vec m → C.Pre (RQⁿ m)
  Nᴬ {m} {n} M b = C.mapPre {RQⁿ n} {RQⁿ m} (affRH M b) (Nⁿ n)

  Nᴬ-mass : ∀ {m n} (M : Mat m n) b → ∫ᴹ {RQⁿ m} (ιPre {RQⁿ m} (Nᴬ M b)) (constW {RQⁿ m} 1#) ≈ 1#
  Nᴬ-mass {m} {n} M b = ι-mass {RQⁿ m} (Nᴬ M b)

  -- the coordinates of A Z + b along the identity, directly on RQᵐ, against the observations idT ∘ projᵢ of N(0, Iₙ)
  CHN : ∀ {m n} → Mat m n → Vec m → Fin m → SgT (RQⁿ n)
  CHN {m} {n} M b k = _∘T_ {RQⁿ n} {RQⁿ m} (coordT m k) (affRH M b)

  eN : ∀ {m n} (M : Mat m n) b k → _≐_ {RQⁿ n} (CHN M b k) (affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ))) k)
  eN {m} {n} M b k x = idT-affRH (Nⁿ n) M b (idH S {RQⁿ n}) k x

  RYN : ∀ {m n} (M : Mat m n) b → RV (Nⁿ n) m (affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ))))
  RYN {m} {n} M b = RV-aff (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ)))
    (RV-iid (Nⁿ n) (ιPre {RQ} γ) γ-mass idT 0S 1S γ-i γ-j γ-em γ-es n (projQ n (λ _ → RQ)) (std-iid n))

  rrN : ∀ {m n} (M : Mat m n) b → RV (Nⁿ n) m (CHN M b)
  rrN {m} {n} M b = RV-≐ (Nⁿ n) {X = affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ)))} {Y = CHN M b}
    (λ k → ≐-sym {RQⁿ n} {CHN M b k} {affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ))) k} (eN M b k))
    (λ k x → [ inj₂ , inj₁ ]′ (zero-id (map (projQ m (λ _ → RQ) k) ⟨$⟩ (map (affRH M b) ⟨$⟩ x)))) (RYN M b)

  Nᴬ-RV : ∀ {m n} (M : Mat m n) b → RV (Nᴬ M b) m (coordT m)
  Nᴬ-RV {m} {n} M b = RV-law (Nⁿ n) (affRH M b) m (coordT m) (rrN M b)

  -- the moment chains, abstract in the laws
  mean-chain : ∀ {Ω : QBS S} (P : C.Pre Ω) {m} (CH Y : Fin m → SgT Ω) (rr : RV P m CH) (e : ∀ k → _≐_ {Ω} (CH k) (Y k))
    {ry : RV P m Y} {Q : C.Pre (RQⁿ m)} {rq : RV Q m (coordT m)} {v : Vec m} →
    meanV Q m (coordT m) rq ≈V meanV P m CH rr → meanV P m Y ry ≈V v → meanV Q m (coordT m) rq ≈V v
  mean-chain P CH Y rr e {ry} h1 h2 k = ≃-trans (h1 k) (≃-trans (mean-≐ P {X = CH} {Y = Y} e rr ry k) (h2 k))

  cov-chain : ∀ {Ω : QBS S} (P : C.Pre Ω) {m} (CH Y : Fin m → SgT Ω) (rr : RV P m CH) (e : ∀ k → _≐_ {Ω} (CH k) (Y k))
    {ry : RV P m Y} {Q : C.Pre (RQⁿ m)} {rq : RV Q m (coordT m)} {D : Mat m m} →
    covM Q m (coordT m) rq ≈M covM P m CH rr → covM P m Y ry ≈M D → covM Q m (coordT m) rq ≈M D
  cov-chain P CH Y rr e {ry} h1 h2 i j = ≃-trans (h1 i j) (≃-trans (cov-≐ P {X = CH} {Y = Y} e rr ry i j) (h2 i j))

  Nᴬ-mean : ∀ {m n} (M : Mat m n) b → meanV (Nᴬ M b) m (coordT m) (Nᴬ-RV M b) ≈V b
  Nᴬ-mean {m} {n} M b = mean-chain (Nⁿ n) (CHN M b) (affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ)))) (rrN M b)
    (eN M b) {RYN M b} {v = b}
    (mean-law (Nⁿ n) (affRH M b) m (coordT m) (rrN M b)) (gaussV-mean (Nⁿ n) n (projQ n (λ _ → RQ)) (std-iid n) M b)

  Nᴬ-cov : ∀ {m n} (M : Mat m n) b → covM (Nᴬ M b) m (coordT m) (Nᴬ-RV M b) ≈M M *M (M ᵀ)
  Nᴬ-cov {m} {n} M b = cov-chain (Nⁿ n) (CHN M b) (affT (Nⁿ n) M b (obs idT n (projQ n (λ _ → RQ)))) (rrN M b) (eN M b) {RYN M b}
    (cov-law (Nⁿ n) (affRH M b) m (coordT m) (rrN M b)) (gaussV-cov (Nⁿ n) n (projQ n (λ _ → RQ)) (std-iid n) M b)
