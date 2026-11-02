{-# OPTIONS --safe --without-K #-}

-- Two independent exponential draws, through the product law `E-atᴵ-⊗` of `Inference/ExpectationIntProduct`.
-- With `expPair = expDist ⊗ᵖ expDist` and the integrable tests `idI` (the mean, `Inference/ExpDistMean`), `sqI` (the
-- second moment, `Inference/ExpDistVar`) and the constant test `oneI`, the statistics `X = idI ⊗I oneI`, `Y = oneI ⊗I idI`
-- (the coordinates), `X·Y = idI ⊗I idI`, `X² = sqI ⊗I oneI` and `Y² = oneI ⊗I sqI` have
--   * `E[X·Y] ≃ 1` (independence: `1 * 1`);
--   * `E[X + Y] ≃ 2` (linearity of `E-atᴵ`, with `E X ≃ E Y ≃ 1`);
--   * `E[X² + Y² + 2·X·Y] ≃ 6 = 2 + 2 + 2·1`, the second moment of the sum `(X + Y)²`.
-- Values are signed lower reals (`Sg`), with no division, so the numerals are the sums `1S +S 1S`, ….
module QBS.Inference.ExpDistPair where

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Inference.ExpDistMean using (module ExpDistMean)
open import QBS.Inference.ExpDistVar using (module ExpDistVar)
import QBS.Inference.ExpectationInt as EI
import QBS.Inference.ExpectationProduct as EP
import QBS.Inference.ExpectationIntProduct as EIP
import QBS.Inference.Expectation as EX

module ExpDistPair (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A using (_+_; _*_; 0#; 1#; refl)
  open Bounded A using (Sg; _≃_; mk≃; ≃-refl; ≃-trans; _+S_; _*S_; +S-cong; *S-cong; 1S; *S-identityˡ; *S-identityʳ;
    _−_[_,_]; finite)
  open SubSemiring using (Is-0; Is-1; Is-+)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (OmegaSemiring.commutativeSemiring A)
    using (solve; _:+_; _:*_; _:=_; con)
  open Weights (lemOf lem₁) using (WQ)
  open ExpDist lem₁ using (expDist)
  open ExpDistMean lem₁ using (idI; E-atᴵ-idI)
  open ExpDistVar lem₁ using (sqI; E-atᴵ-sqI; two-fin)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ; fromSTest; E-atᴵ-fromSTest; _+I_; E-atᴵ-+; scaleI; E-atᴵ-scale)
  open EP.ExpectationProduct lem₁ using (_⊗ᵖ_)
  open EIP.ExpectationIntProduct lem₁ using (_⊗I_; E-atᴵ-⊗)
  open EX.Expectation lem₁ using (constT; E-at-const)
  open Continuous A (lemOf lem₁) probClass using (Pre)

  expPair : Pre (_×Q_ S WQ WQ)
  expPair = expDist ⊗ᵖ expDist

  -- the constant test 1
  oneI : ∀ {X : QBS S} (p : Pre X) → ITest p
  oneI p = fromSTest p (constT 1S)

  E-atᴵ-oneI : ∀ {X : QBS S} (p : Pre X) → E-atᴵ p (oneI p) ≃ 1S
  E-atᴵ-oneI p = ≃-trans (E-atᴵ-fromSTest p (constT 1S)) (E-at-const p 1S)

  -- the numeral 2, and 6 = 2 + 2 + 2
  twoS sixS : Sg
  twoS = (1# + 1#) − 0# [ two-fin , Is-0 finite ]
  sixS = ((1# + 1#) + (1# + 1#) + (1# + 1#)) − 0# [ Is-+ finite (Is-+ finite two-fin two-fin) two-fin , Is-0 finite ]

  -- the coordinates, their product and their squares, as tests on `expPair`
  X Y XY Xsq Ysq : ITest expPair
  X = idI ⊗I oneI expDist
  Y = oneI expDist ⊗I idI
  XY = idI ⊗I idI
  Xsq = sqI ⊗I oneI expDist
  Ysq = oneI expDist ⊗I sqI

  E-X : E-atᴵ expPair X ≃ 1S
  E-X = ≃-trans (E-atᴵ-⊗ expDist expDist idI (oneI expDist))
    (≃-trans (*S-cong E-atᴵ-idI (E-atᴵ-oneI expDist)) (*S-identityˡ 1S))

  E-Y : E-atᴵ expPair Y ≃ 1S
  E-Y = ≃-trans (E-atᴵ-⊗ expDist expDist (oneI expDist) idI)
    (≃-trans (*S-cong (E-atᴵ-oneI expDist) E-atᴵ-idI) (*S-identityˡ 1S))

  -- independence: `E[X·Y] ≃ 1`
  E-XY : E-atᴵ expPair XY ≃ 1S
  E-XY = ≃-trans (E-atᴵ-⊗ expDist expDist idI idI) (≃-trans (*S-cong E-atᴵ-idI E-atᴵ-idI) (*S-identityˡ 1S))

  one+one : (1S +S 1S) ≃ twoS
  one+one = mk≃ 0# (Is-0 finite) (solve 0 ((con 1 :+ con 1) :+ con 0 :+ con 0
    := (con 1 :+ con 1) :+ (con 0 :+ con 0) :+ con 0) refl)

  -- linearity: `E[X + Y] ≃ 2`
  E-X+Y : E-atᴵ expPair (X +I Y) ≃ twoS
  E-X+Y = ≃-trans (E-atᴵ-+ expPair X Y) (≃-trans (+S-cong E-X E-Y) one+one)

  E-Xsq : E-atᴵ expPair Xsq ≃ twoS
  E-Xsq = ≃-trans (E-atᴵ-⊗ expDist expDist sqI (oneI expDist))
    (≃-trans (*S-cong E-atᴵ-sqI (E-atᴵ-oneI expDist)) (*S-identityʳ twoS))

  E-Ysq : E-atᴵ expPair Ysq ≃ twoS
  E-Ysq = ≃-trans (E-atᴵ-⊗ expDist expDist (oneI expDist) sqI)
    (≃-trans (*S-cong (E-atᴵ-oneI expDist) E-atᴵ-sqI) (*S-identityˡ twoS))

  -- `(X + Y)² = X² + Y² + 2·X·Y`, with expectation `2 + 2 + 2·1`
  XYsq : ITest expPair
  XYsq = (Xsq +I Ysq) +I scaleI twoS XY

  six-arith : ((twoS +S twoS) +S (twoS *S 1S)) ≃ sixS
  six-arith = mk≃ 0# (Is-0 finite) (solve 0
    ((((con 1 :+ con 1) :+ (con 1 :+ con 1)) :+ ((con 1 :+ con 1) :* con 1 :+ con 0 :* con 0)) :+ con 0 :+ con 0
    := (((con 1 :+ con 1) :+ (con 1 :+ con 1)) :+ (con 1 :+ con 1)) :+
         ((con 0 :+ con 0) :+ ((con 1 :+ con 1) :* con 0 :+ con 0 :* con 1)) :+ con 0) refl)

  E-XYsq : E-atᴵ expPair XYsq ≃ sixS
  E-XYsq = ≃-trans (E-atᴵ-+ expPair (Xsq +I Ysq) (scaleI twoS XY))
    (≃-trans (+S-cong (≃-trans (E-atᴵ-+ expPair Xsq Ysq) (+S-cong E-Xsq E-Ysq))
                      (≃-trans (E-atᴵ-scale expPair twoS XY) (*S-cong ≃-refl E-XY)))
      six-arith)
