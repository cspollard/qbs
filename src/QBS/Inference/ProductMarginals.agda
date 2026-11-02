{-# OPTIONS --safe --without-K #-}

-- Marginals of the product measure `p ⊗ᵖ q` (`Inference/ExpectationProduct`), and the sum of two exponential draws.
--
--   * `fst-marginal`, `snd-marginal`: `mapPre fstQ (p ⊗ᵖ q) ≈ᵖ p` and `mapPre sndQ (p ⊗ᵖ q) ≈ᵖ q`.  The tower law
--     (`∫-map`, `∫-join`, `∫-map`) reduces `∫ (p ⊗ᵖ q) h` to `∫ p (x ↦ ∫ (σPre (x , q)) h)`,
--     `∫-σ` to `∫ q (h (x , –))`, and a probability measure integrates a constant `c` to `c` (`const-I`);
--   * `E-atᴵ-cong`: integrable tests whose parts agree pointwise have `≃` expectations;
--   * `fstI`, `sndI`: the coordinates as integrable tests on `expPair` (`Inference/ExpDistPair`), obtained from `idI` by
--     the marginal law (`transportI`) and `precompI`, with `E-fstI : E-atᴵ expPair fstI ≃ 1` and `E-sndI` likewise;
--   * `sumSqI : ITest expPair`, the pointwise statistic `(x , y) ↦ (x + y)²` built from addition and multiplication of
--     cuts, whose parts are pointwise those of `XYsq` (`pos-pw`, `neg-pw`); hence
--     `E-atᴵ-sumSqI : E[(X + Y)²] ≃ 6`, and
--     `var-sum : E[(X + Y)²] − (E[X + Y])² ≃ 2`, in the form of `ExpDistVar.var-expDist`.
module QBS.Inference.ProductMarginals where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; fstQ; sndQ)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.ExpDist using (module ExpDist)
open import QBS.Inference.ExpDistMean using (module ExpDistMean)
open import QBS.Inference.ExpDistVar using (module ExpDistVar)
import QBS.Inference.ExpectationInt as EI
import QBS.Inference.ExpectationProduct as EP
import QBS.Inference.ExpectationIntProduct as EIP
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpDistPair as EDP
open import Algebra using (CommutativeSemiring)

-- the arithmetic, over an abstract commutative semiring
module Alg {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R

  -- `(a·a·1 + 0·0) + (1·(b·b) + 0·0) + (2·(a·b + 0·0) + 0·(a·0 + 0·b)) = (a + b)·(a + b)`
  pos-eq : ∀ a b → (((a * a) * 1# + 0# * 0#) + (1# * (b * b) + 0# * 0#)) +
    ((1# + 1#) * (a * b + 0# * 0#) + 0# * (a * 0# + 0# * b)) ≈ (a + b) * (a + b)
  pos-eq = solve 2 (λ a b → (((a :* a) :* con 1 :+ con 0 :* con 0) :+ (con 1 :* (b :* b) :+ con 0 :* con 0)) :+
    ((con 1 :+ con 1) :* (a :* b :+ con 0 :* con 0) :+ con 0 :* (a :* con 0 :+ con 0 :* b))
    := (a :+ b) :* (a :+ b)) refl

  -- `(a·a·0 + 0·1) + (1·0 + 0·(b·b)) + (2·(a·0 + 0·b) + 0·(a·b + 0·0)) = 0`
  neg-eq : ∀ a b → (((a * a) * 0# + 0# * 1#) + (1# * 0# + 0# * (b * b))) +
    ((1# + 1#) * (a * 0# + 0# * b) + 0# * (a * b + 0# * 0#)) ≈ 0#
  neg-eq = solve 2 (λ a b → (((a :* a) :* con 0 :+ con 0 :* con 1) :+ (con 1 :* con 0 :+ con 0 :* (b :* b))) :+
    ((con 1 :+ con 1) :* (a :* con 0 :+ con 0 :* b) :+ con 0 :* (a :* b :+ con 0 :* con 0)) := con 0) refl

  -- `6 + (2·0 + 0·2) + 0 + 0 = (2 + (0 + (2·2 + 0·0))) + 0`, the arithmetic of `6 − 2·2 = 2`
  var-eq : ((((1# + 1#) + (1# + 1#)) + (1# + 1#)) + ((1# + 1#) * 0# + 0# * (1# + 1#))) + 0# + 0# ≈
    ((1# + 1#) + (0# + ((1# + 1#) * (1# + 1#) + 0# * 0#))) + 0#
  var-eq = solve 0
    (((((con 1 :+ con 1) :+ (con 1 :+ con 1)) :+ (con 1 :+ con 1)) :+
        ((con 1 :+ con 1) :* con 0 :+ con 0 :* (con 1 :+ con 1))) :+ con 0 :+ con 0
    := ((con 1 :+ con 1) :+ (con 0 :+ ((con 1 :+ con 1) :* (con 1 :+ con 1) :+ con 0 :* con 0))) :+ con 0) refl

module ProductMarginals (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-cong)
  open Integration A using (Measure; IsProb; I; I-cong; I-scale; probClass)
  open Measurable A using (Fun; Fun-const)
  open OmegaSemiring A using (_≈_; _+_; _*_; 0#; 1#; refl; sym; trans; *-cong; +-cong; *-identityʳ; ≤-refl;
    commutativeSemiring)
  open Alg commutativeSemiring
  open Meas (lemOf lem₁) using (Meas-⊗)
  open Bounded A using (_≃_; mk≃; ≃-trans; ≃-sym; _+S_; _*S_; -S_; 1S; +S-cong; -S-cong;
    *S-cong; finite)
  open SubSemiring using (Is-resp; Is-0)
  open SignedTests (lemOf lem₁) using (CutQ)
  open Weights (lemOf lem₁) using (WQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; _≈ᵖ_; ∫; mapPre; ∫ᶠ; ∫-map; ∫-join)
  open Strength A (lemOf lem₁) probClass using (σPre; ∫-σ)
  open ExpDist lem₁ using (expDist)
  open ExpDistMean lem₁ using (idI; E-atᴵ-idI; idC; zeroC)
  open ExpDistVar lem₁ using (two-fin)
  open EI.ExpectationInt lem₁ using (ITest; E-atᴵ; precompI; transportI; E-atᴵ-map; E-respᴵ; _+I_; E-atᴵ-+)
  open EP.ExpectationProduct lem₁ using (σq; _⊗ᵖ_)
  open EIP.ExpectationIntProduct lem₁ using (_⊗I_)
  open EX.Expectation lem₁ using (addH)
  open EDP.ExpDistPair lem₁ using (expPair; oneI; X; Y; XYsq; E-X+Y; E-XYsq; twoS; sixS)
  open Pre
  open ITest
  open QBS using (∣_∣)

  ----------------------------------------------------------------------------
  -- marginals

  -- a probability measure integrates a constant to that constant
  const-I : ∀ (n : Measure) → IsProb n → ∀ c {h} (f : Fun h) → (∀ r → h r ≈ c) → I n h f ≈ c
  const-I n pn c f e = trans (I-scale n c (Fun-const 1# ≤-refl) f (λ r → trans (e r) (sym (*-identityʳ c))))
    (trans (*-cong refl pn) (*-identityʳ c))

  fst-marginal : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) → _≈ᵖ_ {X} (mapPre (fstQ S {X} {Y}) (p ⊗ᵖ q)) p
  fst-marginal {X} {Y} p q g = trans (∫-map (fstQ S {X} {Y}) (p ⊗ᵖ q) g) (trans (∫-join (mapPre (σq q) p) h)
    (trans (∫-map (σq q) p (∫ᶠ h)) (I-cong (m p) (λ r → pw (α p ⟨$⟩ r)) _ _)))
    where
    h = _∘H_ S g (fstQ S {X} {Y})
    pw : ∀ x → ∫ (σPre {X} {Y} (x , q)) h ≈ proj₁ (Hom.map g ⟨$⟩ x)
    pw x = trans (∫-σ x q h) (const-I (m q) (ok q) _ _ (λ _ → refl))

  snd-marginal : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) → _≈ᵖ_ {Y} (mapPre (sndQ S {X} {Y}) (p ⊗ᵖ q)) q
  snd-marginal {X} {Y} p q g = trans (∫-map (sndQ S {X} {Y}) (p ⊗ᵖ q) g) (trans (∫-join (mapPre (σq q) p) h)
    (trans (∫-map (σq q) p (∫ᶠ h)) (const-I (m p) (ok p) (∫ q g) _ (λ r → pw (α p ⟨$⟩ r)))))
    where
    h = _∘H_ S g (sndQ S {X} {Y})
    pw : ∀ x → ∫ (σPre {X} {Y} (x , q)) h ≈ ∫ q g
    pw x = trans (∫-σ x q h) (I-cong (m q) (λ _ → refl) _ _)

  ----------------------------------------------------------------------------
  -- tests with the same parts pointwise

  E-atᴵ-cong : ∀ {X : QBS S} (p : Pre X) (g h : ITest p) →
    (∀ x → Hom.map (pos g) ⟨$⟩ x ≈ Hom.map (pos h) ⟨$⟩ x) →
    (∀ x → Hom.map (neg g) ⟨$⟩ x ≈ Hom.map (neg h) ⟨$⟩ x) →
    E-atᴵ p g ≃ E-atᴵ p h
  E-atᴵ-cong p g h ep en = mk≃ 0# (Is-0 finite)
    (+-cong (+-cong (J-cong (m p) (Hom.map-random (pos g) (α-random p)) (Hom.map-random (pos h) (α-random p))
                      (λ r → ep (α p ⟨$⟩ r)))
                    (sym (J-cong (m p) (Hom.map-random (neg g) (α-random p)) (Hom.map-random (neg h) (α-random p))
                      (λ r → en (α p ⟨$⟩ r))))) refl)

  ----------------------------------------------------------------------------
  -- the coordinates of the exponential pair

  -- the marginal law, as an equality of measures on `WQ`
  fst-eq : _≈ᵖ_ {WQ} expDist (mapPre (fstQ S {WQ} {WQ}) expPair)
  fst-eq g = sym (fst-marginal expDist expDist g)

  snd-eq : _≈ᵖ_ {WQ} expDist (mapPre (sndQ S {WQ} {WQ}) expPair)
  snd-eq g = sym (snd-marginal expDist expDist g)

  fstI sndI : ITest expPair
  fstI = precompI (fstQ S {WQ} {WQ}) expPair (transportI {p = expDist} fst-eq idI)
  sndI = precompI (sndQ S {WQ} {WQ}) expPair (transportI {p = expDist} snd-eq idI)

  E-fstI : E-atᴵ expPair fstI ≃ 1S
  E-fstI = ≃-trans (≃-sym (E-atᴵ-map (fstQ S {WQ} {WQ}) expPair (transportI {p = expDist} fst-eq idI)))
    (≃-trans (≃-sym (E-respᴵ fst-eq idI)) E-atᴵ-idI)

  E-sndI : E-atᴵ expPair sndI ≃ 1S
  E-sndI = ≃-trans (≃-sym (E-atᴵ-map (sndQ S {WQ} {WQ}) expPair (transportI {p = expDist} snd-eq idI)))
    (≃-trans (≃-sym (E-respᴵ snd-eq idI)) E-atᴵ-idI)

  ----------------------------------------------------------------------------
  -- the pointwise statistic (x , y) ↦ (x + y)²

  -- x + y, as a `CutQ`-valued test on pairs
  sumC : Hom S (_×Q_ S WQ WQ) CutQ
  sumC = addH (_∘H_ S idC (fstQ S {WQ} {WQ})) (_∘H_ S idC (sndQ S {WQ} {WQ}))

  -- (x + y)·(x + y)
  sumSqC : Hom S (_×Q_ S WQ WQ) CutQ
  sumSqC = record
    { map = record
        { to = λ z → (Hom.map sumC ⟨$⟩ z) * (Hom.map sumC ⟨$⟩ z)
        ; cong = λ e → *-cong (Func.cong (Hom.map sumC) e) (Func.cong (Hom.map sumC) e) }
    ; map-random = λ r → Meas-⊗ (Hom.map-random sumC r) (Hom.map-random sumC r) }

  -- the parts of `XYsq` are pointwise those of `sumSqI`
  pos-pw : ∀ r → Hom.map (pos XYsq) ⟨$⟩ (α expPair ⟨$⟩ r) ≈ Hom.map sumSqC ⟨$⟩ (α expPair ⟨$⟩ r)
  pos-pw r = pos-eq (proj₁ (α expPair ⟨$⟩ r)) (proj₂ (α expPair ⟨$⟩ r))

  neg-pw : ∀ r → Hom.map (neg XYsq) ⟨$⟩ (α expPair ⟨$⟩ r) ≈ 0#
  neg-pw r = neg-eq (proj₁ (α expPair ⟨$⟩ r)) (proj₂ (α expPair ⟨$⟩ r))

  zeroP : Hom S (_×Q_ S WQ WQ) CutQ
  zeroP = _∘H_ S zeroC (fstQ S {WQ} {WQ})

  sumSqI : ITest expPair
  sumSqI = record
    { pos = sumSqC ; neg = zeroP
    ; pos-int = Is-resp finite (J-cong (m expPair) (Hom.map-random (pos XYsq) (α-random expPair))
        (Hom.map-random sumSqC (α-random expPair)) pos-pw) (pos-int XYsq)
    ; neg-int = Is-resp finite (J-cong (m expPair) (Hom.map-random (neg XYsq) (α-random expPair))
        (Hom.map-random zeroP (α-random expPair)) neg-pw) (neg-int XYsq) }

  -- the second moment of the sum: `E[(X + Y)²] ≃ 6`
  E-atᴵ-sumSqI : E-atᴵ expPair sumSqI ≃ sixS
  E-atᴵ-sumSqI = ≃-trans (E-atᴵ-cong expPair sumSqI XYsq (λ z → sym (pos-eq (proj₁ z) (proj₂ z)))
    (λ z → sym (neg-eq (proj₁ z) (proj₂ z)))) E-XYsq

  ----------------------------------------------------------------------------
  -- the variance of the sum

  -- `6 − 2·2 = 2`
  var-arith : (sixS +S (-S (twoS *S twoS))) ≃ twoS
  var-arith = mk≃ 0# (Is-0 finite) var-eq

  -- the variance of `X + Y`: `E[(X + Y)²] − (E[X + Y])² ≃ 2`
  var-sum : (E-atᴵ expPair sumSqI +S (-S (E-atᴵ expPair (X +I Y) *S E-atᴵ expPair (X +I Y)))) ≃ twoS
  var-sum = ≃-trans (+S-cong E-atᴵ-sumSqI (-S-cong (*S-cong E-X+Y E-X+Y))) var-arith
