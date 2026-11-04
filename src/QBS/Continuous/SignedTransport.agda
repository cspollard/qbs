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
-- the pulled-back `J` of `ExpectationInt.toSF` (`∫ι`, by `J-cong` and `*-identityˡ`; `J-irrel` for the `Meas` proofs).
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
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedExpect using (module SignedExpect)
import QBS.Inference.ExpectationInt as EI
open import QBS.Analysis.Signed using (SubSemiring)

module SignedTransport (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-identityˡ; commutativeSemiring)
    renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; Sg; _≃_; _*S_; ι; mk≃; finite)
  open SubSemiring finite using (Is-*; Is-0)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open Lebesgue (lemOf lem₁) using (J; J-cong; J-irrel)
  open Weights (lemOf lem₁) using (WQ)
  open SignedTests (lemOf lem₁) using (CutQ)
  open SFinite (lemOf lem₁) using (XW; ∫ᴹ; ∫ᴹ-map; ψ; mψ; mapM; module C)
  open SFiniteSum (lemOf lem₁) using (scalePre; ∫ᴹ-scale)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open Continuous A (lemOf lem₁) probClass using (Pre)
  open SignedTest lem₁ using (SgT; posT; negT; _∘T_; toW; toCut)
  open SignedExpect lem₁ using (Int; Ex; bnd≈)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open QBS
  open Hom

  scale-alg : ∀ c a b → c * a + (c * b + 0# * a) + 0# ≈ (c * a + 0# * b) + c * b + 0#
  scale-alg c a b = solve 3 (λ c a b → c :* a :+ (c :* b :+ con 0 :* a) :+ con 0 := (c :* a :+ con 0 :* b) :+ c :* b :+ con 0)
    refl c a b

  module _ {X Y : QBS S} where

    Int-map : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) → Int {X} (mapM {Y} {X} h p) f → Int {Y} p (f ∘T h)
    Int-map h p f (i⁺ , i⁻) = bnd≈ {X} (sym (∫ᴹ-map h p (posT f))) i⁺ , bnd≈ {X} (sym (∫ᴹ-map h p (negT f))) i⁻

    Int-unmap : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) → Int {Y} p (f ∘T h) → Int {X} (mapM {Y} {X} h p) f
    Int-unmap h p f (i⁺ , i⁻) = bnd≈ {X} (∫ᴹ-map h p (posT f)) i⁺ , bnd≈ {X} (∫ᴹ-map h p (negT f)) i⁻

    Ex-map : ∀ (h : Hom S Y X) (p : C.Pre (XW Y)) (f : SgT X) (i : Int {X} (mapM {Y} {X} h p) f) →
      Ex {X} (mapM {Y} {X} h p) f i ≃ Ex {Y} p (f ∘T h) (Int-map h p f i)
    Ex-map h p f i = mk≃ 0# Is-0 (+-cong (+-cong (∫ᴹ-map h p (posT f)) (sym (∫ᴹ-map h p (negT f)))) refl)

  module _ {X : QBS S} where

    Int-scalePre : ∀ {c} → Bnd c → (p : C.Pre (XW X)) (f : SgT X) → Int {X} p f → Int {X} (scalePre {X} c p) f
    Int-scalePre {c} bc p f (i⁺ , i⁻) =
      bnd≈ {X} (∫ᴹ-scale {X} c p (posT f)) (Is-* {_} {_} bc i⁺) , bnd≈ {X} (∫ᴹ-scale {X} c p (negT f)) (Is-* {_} {_} bc i⁻)

    Ex-scalePre : ∀ {c} (bc : Bnd c) (p : C.Pre (XW X)) (f : SgT X) (i : Int {X} p f) →
      Ex {X} (scalePre {X} c p) f (Int-scalePre bc p f i) ≃ ι bc *S Ex {X} p f i
    Ex-scalePre {c} bc p f i = mk≃ 0# Is-0 (trans (+-cong (+-cong (∫ᴹ-scale {X} c p (posT f)) refl) refl)
      (trans (scale-alg c (∫ᴹ {X} p (posT f)) (∫ᴹ {X} p (negT f)))
        (+-cong (+-cong refl (sym (∫ᴹ-scale {X} c p (negT f)))) refl)))

    -- from and to the expectation API of the probability monad
    ofITest : ∀ {P : Pre X} → ITest P → SgT X
    ofITest t = toW (ITest.pos t) , toW (ITest.neg t)

    -- against a probability measure the weighted integral is the pulled-back `J` (the weight is 1)
    ∫ι : ∀ (P : Pre X) (f : Hom S X WQ) →
      ∫ᴹ {X} (ιPre {X} P) f ≈ J (Pre.m P) (λ r → map f ⟨$⟩ (Pre.α P ⟨$⟩ r)) (map-random f (Pre.α-random P))
    ∫ι P f = J-cong (Pre.m P) (mψ {X} (ιPre {X} P) f) (map-random f (Pre.α-random P)) (λ r → *-identityˡ _)

    ∫ιW : ∀ (P : Pre X) (g : Hom S X CutQ) →
      ∫ᴹ {X} (ιPre {X} P) (toW g) ≈ J (Pre.m P) (λ r → map g ⟨$⟩ (Pre.α P ⟨$⟩ r)) (map-random g (Pre.α-random P))
    ∫ιW P g = trans (∫ι P (toW g)) (J-irrel (Pre.m P) _ _)

    Int-ofITest : ∀ (P : Pre X) (t : ITest P) → Int {X} (ιPre {X} P) (ofITest t)
    Int-ofITest P t = bnd≈ {X} (∫ιW P (ITest.pos t)) (ITest.pos-int t) , bnd≈ {X} (∫ιW P (ITest.neg t)) (ITest.neg-int t)

    Ex-ofITest : ∀ (P : Pre X) (t : ITest P) → E-atᴵ P t ≃ Ex {X} (ιPre {X} P) (ofITest t) (Int-ofITest P t)
    Ex-ofITest P t = mk≃ 0# Is-0 (+-cong (+-cong (sym (∫ιW P (ITest.pos t))) (∫ιW P (ITest.neg t))) refl)

    toITest : ∀ (P : Pre X) (f : SgT X) → Int {X} (ιPre {X} P) f → ITest P
    toITest P f (i⁺ , i⁻) = record
      { pos = toCut (posT f) ; neg = toCut (negT f)
      ; pos-int = bnd≈ {X} (sym (∫ι P (posT f))) i⁺ ; neg-int = bnd≈ {X} (sym (∫ι P (negT f))) i⁻ }

    E-atᴵ-toITest : ∀ (P : Pre X) (f : SgT X) (i : Int {X} (ιPre {X} P) f) → E-atᴵ P (toITest P f i) ≃ Ex {X} (ιPre {X} P) f i
    E-atᴵ-toITest P f i = mk≃ 0# Is-0 (+-cong (+-cong (sym (∫ι P (posT f))) (∫ι P (negT f))) refl)
