{-# OPTIONS --safe --without-K #-}

-- Moving signed expectations along maps, scalings, and from the probability-monad API (plan 03, "Signed layer").
--   * `Ex-map`: the expectation against a pushforward `mapM h p` is the expectation of the composite f ∘ h (with
--     integrability both ways, `Int-map`, `Int-unmap`);
--   * `Ex-scalePre`: against c · p (c finite) it is c times the expectation;
--   * the bridge from `Inference/ExpectationInt`: an integrable test `t : ITest P` of the probability monad gives a
--     signed test `ofITest t` with `E-atᴵ P t ≃ Ex (ιPre P) (ofITest t) _` (`Ex-ofITest`), and back (`toITest`,
--     `E-atᴵ-toITest`), so results stated with `E-atᴵ` (`GaussReal.var-gaussR`, `GaussAffine.var-affI`,
--     `ExpDistVar.var-expDist`) carry over by one lemma.
-- Route: `SFinite.∫ᴹ-map`, `SFiniteSum.∫ᴹ-scale`; the bridge by unfolding `∫ᴹ (ιPre P) f` (weight 1 times f, `ψ`) to
-- the pulled-back `J` of `ExpectationInt.toSF` (`SignedTest.toW-pt`, `J-cong`).
--   Skeleton: holes first.
module QBS.Continuous.SignedTransport where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_×_; _,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
import QBS.Inference.ExpectationInt as EI

module SignedTransport (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _*S_; ι)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; mapM; module C)
  open SFiniteSum (lemOf lem₁) using (scalePre)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; posT; negT; _∘T_; toW)
  open SignedExpect lem₁ using (Int; Ex)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open QBS
  open Hom

  module _ {X Y : QBS S} where

    Int-map : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) → Int {X} (mapM {Y} {X} h p) f → Int {Y} p (f ∘T h)
    Int-map = ?

    Int-unmap : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) → Int {Y} p (f ∘T h) → Int {X} (mapM {Y} {X} h p) f
    Int-unmap = ?

    Ex-map : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) (i : Int {X} (mapM {Y} {X} h p) f) →
      Ex {X} (mapM {Y} {X} h p) f i ≃ Ex {Y} p (f ∘T h) (Int-map h p f i)
    Ex-map = ?

  module _ {X : QBS S} where

    Int-scalePre : ∀ {c} → Bnd c → (p : C.Pre (XW X)) (f : SgT X) → Int {X} p f → Int {X} (scalePre {X} c p) f
    Int-scalePre = ?

    Ex-scalePre : ∀ {c} (bc : Bnd c) (p : C.Pre (XW X)) (f : SgT X) (i : Int {X} p f) →
      Ex {X} (scalePre {X} c p) f (Int-scalePre bc p f i) ≃ ι bc *S Ex {X} p f i
    Ex-scalePre = ?

    -- from and to the expectation API of the probability monad
    ofITest : ∀ {P : Pre X} → ITest P → SgT X
    ofITest t = toW (ITest.pos t) , toW (ITest.neg t)

    Int-ofITest : ∀ (P : Pre X) (t : ITest P) → Int {X} (ιPre {X} P) (ofITest t)
    Int-ofITest = ?

    Ex-ofITest : ∀ (P : Pre X) (t : ITest P) → E-atᴵ P t ≃ Ex {X} (ιPre {X} P) (ofITest t) (Int-ofITest P t)
    Ex-ofITest = ?

    toITest : ∀ (P : Pre X) (f : SgT X) → Int {X} (ιPre {X} P) f → ITest P
    toITest = ?

    E-atᴵ-toITest : ∀ (P : Pre X) (f : SgT X) (i : Int {X} (ιPre {X} P) f) → E-atᴵ P (toITest P f i) ≃ Ex {X} (ιPre {X} P) f i
    E-atᴵ-toITest = ?
