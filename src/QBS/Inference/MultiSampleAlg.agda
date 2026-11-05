{-# OPTIONS --safe --without-K #-}

-- Observations of iid random vectors, transported along their law (plan 05, item 54; helper for `MultiSample`).  For a
-- probability law ν on Y, observations Xs : Fin n → Ω ⇒ Y iid with law ν under a probability P on Ω, and signed tests
-- u, v on Y with finite second moments (`Obs`, with `Pair` for the two tests):
--   * `Tint`, `Tint₂`, `Tex`, `Tcov`: integrability and expectations of u ∘ Xₖ and (u v) ∘ Xₖ are those of u and u v
--     under ν; `Toff`: E[(u ∘ Xₖ)(v ∘ Xₗ)] ≃ E u · E v for k ≢ l (independence);
--   * `Pair.bil-ex`: E[(Σₖ u ∘ Xₖ)(Σₗ v ∘ Xₗ)] ≃ n e + (n² − n) E u E v, with e = E[u v] under ν;
--   * `Pair.cov-sum-eq`: the covariance of the two sums is n (e − E u E v); `Pair.ss-eq`: the expectation of
--     n Σₖ (u ∘ Xₖ)(v ∘ Xₖ) − (Σₖ u ∘ Xₖ)(Σₗ v ∘ Xₗ) is (n² − n)(e − E u E v).
-- Route: `Tint`, `Tex` by `IID.IID-law`, `SignedTransport.Int-map`, `Ex-map` and `IID.Int-≈`, `Ex-≈` (the mass of ν by
-- `ProdBridge.ι-mass`); `Toff` by `Independence.Indep-pair`, `Ex-indep` with `IID.IID-indep`; the double sum by
-- `RandomVectorSum.ExBil` and `MultiSampleRing.dbl` (diagonal `Tcov`, off the diagonal `Toff`); the sample
-- cross-product by `SgSample.Ex-sumG` and `MultiSampleRing.ss-final`.
module QBS.Inference.MultiSampleAlg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
open import QBS.Continuous.SignedVar using (module SignedVar)
open import QBS.Continuous.SignedVarAlg using (module SignedVarAlg)
open import QBS.Continuous.SignedTransport using (module SignedTransport)
open import QBS.Continuous.SgMoments using (module SgMoments)
open import QBS.Continuous.SgSample using (module SgSample)
open import QBS.Continuous.IID using (module IID)
open import QBS.Continuous.Independence using (module Independence)
open import QBS.Continuous.ProdBridge using (module ProdBridge)
open import QBS.Continuous.RandomVectorDefs using (module RandomVectorDefs)
open import QBS.Continuous.RandomVectorSum using (module RandomVectorSum)
open import QBS.Inference.MultiSampleRing using (module MRing)

module MultiSampleAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (refl)
  open Bounded A using (Sg; _≃_; _+S_; _*S_; -S_; signedRing; ≃-refl; ≃-trans; ≃-sym; +S-cong; -S-cong; *S-cong; *S-congʳ)
  open SFinite (lemOf lem₁) using (_≈ᴹ_; mapM; module C)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SignedTest lem₁ using (SgT; _∘T_; _+T_; _*T_; -T_; scaleT)
  open SignedExpect lem₁ using (Int; Ex; Ex-irr; Ex-cong; Ex-+; Ex-neg; Ex-scale; Int-+; Int-neg; Int-scale)
  open SignedVar lem₁ using (Int₂)
  open SignedVarAlg lem₁ using (Int-via)
  open SignedTransport lem₁ using (Int-map; Ex-map)
  open SgMoments lem₁ using (natS; sumT)
  open SgSample lem₁ using (Int-sum; Ex-sumG)
  open IID lem₁ using (IID; IID-law; IID-indep; Int-≈; Ex-≈; ≈ᴹ-sym)
  open Independence lem₁ using (Indep-pair; Int-indep; Ex-indep)
  open ProdBridge lem₁ using (ι-mass)
  open RandomVectorSum lem₁ using (ExBil)
  open RandomVectorDefs lem₁ using () renaming (module Defs to RDefs)
  module MR = MRing signedRing

  -- n in the ring is `natS n`
  nat-eq : ∀ n → MR.nt n ≃ natS n
  nat-eq zero = ≃-refl
  nat-eq (suc n) = +S-cong ≃-refl (nat-eq n)

  module Obs {Ω : QBS S} (P : C.Pre Ω) {Y : QBS S} (ν : C.Pre Y) n (Xs : Fin n → Hom S Ω Y)
    (D : IID P (ιPre {Y} ν) n Xs) where

    private
      E = ιPre {Ω} P

    open RDefs {Ω} P using (Int-mul)
    module RY = RDefs {Y} ν

    law-k : ∀ k → _≈ᴹ_ {Y} (mapM {Ω} {Y} (Xs k) E) (ιPre {Y} ν)
    law-k k = IID-law {Ω} P {Y} (ιPre {Y} ν) n Xs D (ι-mass {Y} ν) k

    -- integrals under ν and under P of the observations
    Tint : ∀ k (f : SgT Y) → Int {Y} (ιPre {Y} ν) f → Int {Ω} E (f ∘T Xs k)
    Tint k f i = Int-map (Xs k) E f (Int-≈ {Y} (≈ᴹ-sym {Y} (law-k k)) i)

    Tex : ∀ k (f : SgT Y) (i : Int {Y} (ιPre {Y} ν) f) → Ex {Ω} E (f ∘T Xs k) (Tint k f i) ≃ Ex {Y} (ιPre {Y} ν) f i
    Tex k f i = ≃-trans (≃-sym (Ex-map (Xs k) E f ℓ)) (Ex-≈ {Y} (law-k k) f ℓ i)
      where ℓ = Int-≈ {Y} (≈ᴹ-sym {Y} (law-k k)) i

    Tint₂ : ∀ k (f : SgT Y) → Int₂ {Y} ν f → Int₂ {Ω} P (f ∘T Xs k)
    Tint₂ k f (i , j) = Tint k f i ,
      Int-via {Ω} E ((f ∘T Xs k) *T (f ∘T Xs k)) ((f *T f) ∘T Xs k) (Tint k (f *T f) j) (λ x → refl)

    Tcov : ∀ k (u v : SgT Y) (j : Int {Y} (ιPre {Y} ν) (u *T v)) (q : Int {Ω} E ((u ∘T Xs k) *T (v ∘T Xs k))) →
      Ex {Ω} E ((u ∘T Xs k) *T (v ∘T Xs k)) q ≃ Ex {Y} (ιPre {Y} ν) (u *T v) j
    Tcov k u v j q = ≃-trans (Ex-cong {Ω} E _ ((u *T v) ∘T Xs k) q (Tint k (u *T v) j) (λ x → refl)) (Tex k (u *T v) j)

    Toff : ∀ k l → k ≢ l → ∀ (u v : SgT Y) (iu : Int {Y} (ιPre {Y} ν) u) (iv : Int {Y} (ιPre {Y} ν) v)
      (q : Int {Ω} E ((u ∘T Xs k) *T (v ∘T Xs l))) →
      Ex {Ω} E ((u ∘T Xs k) *T (v ∘T Xs l)) q ≃ Ex {Y} (ιPre {Y} ν) u iu *S Ex {Y} (ιPre {Y} ν) v iv
    Toff k l ne u v iu iv q = ≃-trans (Ex-irr {Ω} E _ q (Int-indep {Ω} P (Xs k) (Xs l) dd u v (Tint k u iu) (Tint l v iv)))
      (≃-trans (Ex-indep {Ω} P (Xs k) (Xs l) dd u v (Tint k u iu) (Tint l v iv)) (*S-cong (Tex k u iu) (Tex l v iv)))
      where dd = Indep-pair {Ω} P n (λ _ → Y) Xs (IID-indep {Ω} P {Y} (ιPre {Y} ν) n Xs D (ι-mass {Y} ν)) k l ne

    module Pair (u v : SgT Y) (ru : Int₂ {Y} ν u) (rv : Int₂ {Y} ν v) where

      iAB : ∀ k l → Int {Ω} E ((u ∘T Xs k) *T (v ∘T Xs l))
      iAB k l = Int-mul (u ∘T Xs k) (v ∘T Xs l) (Tint₂ k u ru) (Tint₂ l v rv)

      -- E[u v], E u, E v under ν
      e eu ev : Sg
      e = Ex {Y} (ιPre {Y} ν) (u *T v) (RY.Int-mul u v ru rv)
      eu = Ex {Y} (ιPre {Y} ν) u (proj₁ ru)
      ev = Ex {Y} (ιPre {Y} ν) v (proj₁ rv)

      diag : ∀ k → Ex {Ω} E ((u ∘T Xs k) *T (v ∘T Xs k)) (iAB k k) ≃ e
      diag k = Tcov k u v _ (iAB k k)

      bil = ExBil {Ω} P n n (λ k → u ∘T Xs k) (λ k → v ∘T Xs k) iAB

      bil-ex : Ex {Ω} E (sumT n (λ k → u ∘T Xs k) *T sumT n (λ k → v ∘T Xs k)) (proj₁ bil) ≃
        natS n *S e +S (natS n *S natS n +S -S natS n) *S (eu *S ev)
      bil-ex = ≃-trans (proj₂ bil) (MR.dbl n (natS n) (λ i j → Ex {Ω} E ((u ∘T Xs i) *T (v ∘T Xs j)) (iAB i j)) e (eu *S ev)
        (nat-eq n) diag (λ i j ne → Toff i j ne u v (proj₁ ru) (proj₁ rv) (iAB i j)))

      -- the covariance of the two sums
      cov-sum-eq : ∀ (q : Int {Ω} E (sumT n (λ k → u ∘T Xs k) *T sumT n (λ k → v ∘T Xs k))) (a b : Sg) →
        a ≃ natS n *S eu → b ≃ natS n *S ev →
        Ex {Ω} E (sumT n (λ k → u ∘T Xs k) *T sumT n (λ k → v ∘T Xs k)) q +S -S (a *S b) ≃ natS n *S (e +S -S (eu *S ev))
      cov-sum-eq q a b ea eb = ≃-trans (+S-cong (≃-trans (Ex-irr {Ω} E _ q (proj₁ bil)) bil-ex) (-S-cong (*S-cong ea eb)))
        (MR.cov-final (natS n) e eu ev)

      -- the cross-product test n Σₖ (u ∘ Xₖ)(v ∘ Xₖ) − (Σₖ u ∘ Xₖ)(Σₗ v ∘ Xₗ)
      iQ : Int {Ω} E (sumT n (λ k → (u ∘T Xs k) *T (v ∘T Xs k)))
      iQ = Int-sum P n (λ k → (u ∘T Xs k) *T (v ∘T Xs k)) (λ k → iAB k k)

      Int-X : Int {Ω} E (scaleT (natS n) (sumT n (λ k → (u ∘T Xs k) *T (v ∘T Xs k))) +T
        (-T (sumT n (λ k → u ∘T Xs k) *T sumT n (λ k → v ∘T Xs k))))
      Int-X = Int-+ {Ω} E (Int-scale {Ω} E (natS n) iQ) (Int-neg {Ω} E (proj₁ bil))

      ss-eq : ∀ q → Ex {Ω} E (scaleT (natS n) (sumT n (λ k → (u ∘T Xs k) *T (v ∘T Xs k))) +T
        (-T (sumT n (λ k → u ∘T Xs k) *T sumT n (λ k → v ∘T Xs k))))  q ≃
        (natS n *S natS n +S -S natS n) *S (e +S -S (eu *S ev))
      ss-eq q = ≃-trans (Ex-irr {Ω} E _ q Int-X)
        (≃-trans (Ex-+ {Ω} E _ _ (Int-scale {Ω} E (natS n) iQ) (Int-neg {Ω} E (proj₁ bil)))
        (≃-trans (+S-cong (≃-trans (Ex-scale {Ω} E (natS n) _ iQ) (*S-congʳ (natS n) sq))
          (≃-trans (Ex-neg {Ω} E _ (proj₁ bil)) (-S-cong bil-ex))) (MR.ss-final (natS n) e (eu *S ev))))
        where sq = Ex-sumG {Ω} P n (λ k → (u ∘T Xs k) *T (v ∘T Xs k)) e (λ k → iAB k k) diag
