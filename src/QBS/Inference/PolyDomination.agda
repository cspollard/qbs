{-# OPTIONS --safe --without-K #-}

-- Polynomial growth gives integrability, by `Inference/Domination`.
--   * under the exponential `densDist negExpH expNrm`: if `g⁺ x, g⁻ x ≤ c · (1 + xᵏ)` with `c` finite, then
--     `expI k c cB g⁺ g⁻ dom⁺ dom⁻` is an `ITest`.  The bound is `Bnd (∫ e^{−x} (1 + xᵏ)) = Bnd (0! + k!)`
--     (`Inference/ExpMomentN.pow-integral`);
--   * under the half-normal (`Inference/HalfNormal`, any `n` with `Z · n ≈ 1#`): the same for even degree, as
--     `hnI g⁺ g⁻ m c cB dom⁺ dom⁻`, with growth `c · (1 + x^{ev m})` (`ev m = 2m`).  The bound is
--     `∫ φ (1 + x²ᵐ) = Z + (2m−1)‼ Z` (`Continuous/GaussMoment.even-moment`), and `n · c · (Z + (2m−1)‼ Z) ≈ c · (1 + (2m−1)‼)`
--     whatever the value of `Z`, so `Bnd n` is not needed.  Odd degrees `k` would need `xᵏ ≤ 1 + x^{2k}`, a case split
--     on `x ≤ 1` that lower reals do not provide, so they are covered only through an even bound;
--   * validation: `powD-dom n` re-derives `ExpMomentN.powD n` (and `E-atᴵ-powD-dom n : E[Xⁿ] ≃ n!`) with the bound `xⁿ ≤ 1 + xⁿ`,
--     and `sqI-dom` re-derives `HalfNormal.WithInverse.sqI` from `x² ≤ 1 + x²`.
module QBS.Inference.PolyDomination where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
import Level as L

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.PolyExpCert using (module AlgP)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.DensityDist using (module DensityDist)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)
open import QBS.Continuous.ExpDistSq using (module ExpDistSq)
open import QBS.Continuous.GaussHalfLine using (module GaussHalfLine)
open import QBS.Continuous.GaussMoment using (module GaussMoment)
open import QBS.Continuous.GaussInverse using (module GaussInverse)
open import QBS.Inference.DensityExpectation using (module DensityExpectation)
open import QBS.Inference.ExpMomentN using (module ExpMomentN)
open import QBS.Inference.HalfNormal using (module HalfNormal)
open import QBS.Inference.Domination using (module Domination)
import QBS.Inference.ExpectationInt as EI

-- the one algebraic fact of the half-normal bound, over an abstract ω-semiring
module AlgD (A : OmegaSemiring (L.suc L.zero)) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  hn-alg : ∀ n c Z D → Z * n ≈ 1# → n * (c * (Z + D * Z)) ≈ c * (1# + D)
  hn-alg n c Z D nZ = trans
    (solve 4 (λ n′ c′ Z′ D′ → n′ :* (c′ :* (Z′ :+ D′ :* Z′)) := c′ :* ((con 1 :+ D′) :* (Z′ :* n′))) refl n c Z D)
    (*-cong refl (trans (*-cong refl nZ) (*-identityʳ _)))

module PolyDomination (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
    using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; ≤-trans; ≤-reflexive; +-cong; *-cong; +-comm; *-mono)
  open OmegaSemiring A using (*-identityˡ; *-identityʳ; distribˡ; 0-least; ≤-+ʳ)
  open AlgP A R using (pw)
  open AlgD A using (hn-alg)
  open Exp A using (natE)
  open Bounded A using (Bnd; finite; _≃_; mk≃; _−_[_,_]; ≃-trans)
  open SubSemiring using (Is-resp; Is-0; Is-1; Is-+; Is-*)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (∫ᴹ; ∫ᴹ-cong)
  open SFiniteReweight (lemOf lem₁) using (mulH)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open DensityDist lem₁ using (densDist)
  open HalfLineMomentFact lem₁ using (fact)
  open ExpDistSq lem₁ using (sqW)
  open GaussHalfLine lem₁ using (phiH; gMomH)
  open GaussMoment lem₁ using (Z; ev; dfac; even-moment; ∫-gMom0)
  open GaussInverse lem₁ using (Z-inv)
  open DensityExpectation lem₁ using (expNrm; zero-integral)
  open ExpMomentN lem₁ using (powH; pow-integral; factB; natB)
  open Domination lem₁
    using (addH; ∫ᴹ-add; ∫ᴹ-dom; dens-dom; densI-dom; E-atᴵ-dom; Bnd-≤; Bnd-add; Bnd-scale)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ)
  open Hom

  -- `a ≤ b` gives `a ≤ 1 · (1 + b)`
  ≤-1+ : ∀ {a b} → a ≤ b → a ≤ 1# * (1# + b)
  ≤-1+ {a} {b} h = ≤-trans h (≤-trans (≤-trans ≤-+ʳ (≤-reflexive (+-comm b 1#))) (≤-reflexive (sym (*-identityˡ _))))

  ----------------------------------------------------------------------------
  -- the exponential distribution

  -- the test `x ↦ 1 + xᵏ`
  onePlusPow : ℕ → Hom S WQ WQ
  onePlusPow k = addH (powH 0) (powH k)

  ∫-onePlusPow : ∀ k → ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (onePlusPow k)) ≈ fact 0 + fact k
  ∫-onePlusPow k = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH (onePlusPow k)}
    {addH (mulH {WQ} negExpH (powH 0)) (mulH {WQ} negExpH (powH k))} (λ x → distribˡ _ _ _))
    (trans (∫ᴹ-add lebPre (mulH {WQ} negExpH (powH 0)) (mulH {WQ} negExpH (powH k)))
      (+-cong (pow-integral 0) (pow-integral k)))

  expB : ∀ k → Bnd (∫ᴹ {WQ} lebPre (mulH {WQ} negExpH (onePlusPow k)))
  expB k = Is-resp finite (sym (∫-onePlusPow k)) (Is-+ finite (factB 0) (factB k))

  expI : ∀ k c → Bnd c → (g⁺ g⁻ : Hom S WQ WQ) →
    (∀ x → map g⁺ ⟨$⟩ x ≤ c * (1# + pw k x)) → (∀ x → map g⁻ ⟨$⟩ x ≤ c * (1# + pw k x)) → ITest (densDist negExpH expNrm)
  expI k c cB g⁺ g⁻ dom⁺ dom⁻ = densI-dom negExpH expNrm g⁺ g⁻ (onePlusPow k) c cB (expB k) dom⁺ dom⁻

  -- validation: `ExpMomentN.powD n`
  powD-dom : ℕ → ITest (densDist negExpH expNrm)
  powD-dom n = expI n 1# (Is-1 finite) (powH n) (constW 0#) (λ x → ≤-1+ (≤-reflexive refl)) (λ x → 0-least)

  E-atᴵ-powD-dom : ∀ n → E-atᴵ (densDist negExpH expNrm) (powD-dom n)
    ≃ (fact n − 0# [ factB n , Is-0 finite ])
  E-atᴵ-powD-dom n = ≃-trans (E-atᴵ-dom negExpH expNrm (powH n) (constW 0#) (onePlusPow n) 1# (Is-1 finite) (expB n)
      (λ x → ≤-1+ (≤-reflexive refl)) (λ x → 0-least))
    (mk≃ 0# (Is-0 finite) (+-cong (+-cong (pow-integral n) (sym (zero-integral negExpH expNrm))) refl))

  ----------------------------------------------------------------------------
  -- the half-normal distribution

  dfacB : ∀ m → Bnd (dfac m)
  dfacB zero = Is-1 finite
  dfacB (suc m) = Is-* finite (natB (suc (ev m))) (dfacB m)

  module HNDom (n : ∣A∣) (nZ : Z * n ≈ 1#) where
    open HalfNormal lem₁ using (toC; module WithInverse)
    open WithInverse n nZ using (halfNormal; J-hn; sqI)

    -- the test `x ↦ 1 + x^{ev m}`
    evB : ℕ → Hom S WQ WQ
    evB m = addH (powH 0) (powH (ev m))

    eqB : ∀ m x → map (mulH {WQ} phiH (evB m)) ⟨$⟩ x ≈ map (addH (gMomH 0) (gMomH (ev m))) ⟨$⟩ x
    eqB m x = trans (distribˡ _ _ _) (+-cong (*-comm′ _ _) (*-comm′ _ _))
      where *-comm′ = OmegaSemiring.*-comm A

    ∫-evB : ∀ m → ∫ᴹ {WQ} lebPre (mulH {WQ} phiH (evB m)) ≈ Z + dfac m * Z
    ∫-evB m = trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} phiH (evB m)} {addH (gMomH 0) (gMomH (ev m))} (eqB m))
      (trans (∫ᴹ-add lebPre (gMomH 0) (gMomH (ev m))) (+-cong ∫-gMom0 (even-moment m)))

    -- finiteness of `n ∫ φ g` from `g ≤ c (1 + x^{ev m})`
    hnB : ∀ (g : Hom S WQ WQ) m c → Bnd c → (∀ x → map g ⟨$⟩ x ≤ c * (1# + pw (ev m) x)) →
      Bnd (n * ∫ᴹ {WQ} lebPre (mulH {WQ} phiH g))
    hnB g m c cB dom = Bnd-≤ (≤-trans (*-mono n (∫ᴹ-dom lebPre (mulH {WQ} phiH g) (mulH {WQ} phiH (evB m)) c
        (dens-dom phiH g (evB m) c dom)))
      (≤-reflexive (trans (*-cong refl (*-cong refl (∫-evB m))) (hn-alg n c Z (dfac m) nZ))))
      (Bnd-scale cB (Bnd-add (Is-1 finite) (dfacB m)))

    hnI : ∀ (g⁺ g⁻ : Hom S WQ WQ) m c → Bnd c →
      (∀ x → map g⁺ ⟨$⟩ x ≤ c * (1# + pw (ev m) x)) → (∀ x → map g⁻ ⟨$⟩ x ≤ c * (1# + pw (ev m) x)) → ITest halfNormal
    hnI g⁺ g⁻ m c cB dom⁺ dom⁻ = record
      { pos = toC g⁺ ; neg = toC g⁻
      ; pos-int = Is-resp finite (sym (J-hn g⁺)) (hnB g⁺ m c cB dom⁺)
      ; neg-int = Is-resp finite (sym (J-hn g⁻)) (hnB g⁻ m c cB dom⁻) }

    -- validation: the second moment `HalfNormal.WithInverse.sqI`
    sqI-dom : ITest halfNormal
    sqI-dom = hnI sqW (constW 0#) 1 1# (Is-1 finite)
      (λ x → ≤-1+ (≤-reflexive (sym (*-cong refl (*-identityʳ x))))) (λ x → 0-least)

  -- the canonical instance
  module HNZ = HNDom (proj₁ Z-inv) (proj₂ Z-inv)
