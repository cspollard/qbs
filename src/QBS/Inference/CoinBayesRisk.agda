{-# OPTIONS --safe --without-K #-}

-- The decision-theoretic bridge: Bayes risk of two estimators of a coin's bias, under a uniform prior on θ
-- (`plans/03-bayesian-frequentist.md`, 3e).  One flip X ~ Bernoulli(θ), θ ~ Uniform[0,1].
--
-- The Bayes risk of an estimator θ̂ is r(θ̂) = E[(θ̂ − θ)²] over the joint law of (θ, X): the expectation `E-at joint` of the
-- signed test `(θ̂ − θ)² = θ̂² − 2θθ̂ + θ²` (`Inference/Expectation`: `+T`, `scaleT`, `⊗T`), expanded into products
-- `f(θ)·g(X)`.  The joint is `joint = joinPre (mapPre K uniform)`, where `K θ = σ (θ , coinKernel θ)` is the law of (θ, flip at θ)
-- (`Inference/CoinUniformPrior`).  Every product statistic is computed by the one-sided independence law `E-at-σ`, the kernel
-- `E-at-kernel : E[X | θ] = θ`, and the moments ∫θ = ½ = h and ∫θ² = ⅓ = m of the uniform prior (3m = 1).
--
--   * the frequentist estimator θ̂ = X (indicator of heads; unbiased, with risk θ − θ² at θ).  X² = X, so the squared error
--     is the test `X − 2·θX + θ²`, with expectation h − 2m + m.  `risk-X : 6·r ≃ 1`, i.e. r = ½ − ⅓ = ⅙;
--   * the Bayes estimator θ̂ = posterior mean = (X + 1)/3 (⅔ on heads, ⅓ on tails; risk (3θ² − 3θ + 1)/9 at θ).  The scaled
--     statistic 3θ̂ = X + 1, with (3θ̂ − 3θ)² = 3X + 1 + 9θ² − 6θX − 6θ, has risk `riskP9 = 9r` (`risk-P9 : 2·(9r) ≃ 1`), and
--     `riskP = (⅓·⅓)·riskP9` is the risk of θ̂ itself: `risk-P : 18·r ≃ 1`, i.e. r = 1/18;
--   * the comparison `18·r(X) ≃ 3` against `18·r(θ̂) ≃ 1` (`risk-X18`, `risk-P`): the posterior mean has Bayes risk 1/18 ≤ ⅙, the
--     Bayes-optimality of the posterior mean under squared error (the frequentist estimator X is admissible but not Bayes).
-- Values are signed lower reals (`Sg`); the statements are multiplied out (no division), with n·r the n-fold sum.
module QBS.Inference.CoinBayesRisk where

open import Algebra using (CommutativeRing; IsCommutativeRing)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; pairQ)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.UniformMoment using (module UniformMoment)
import QBS.Analysis.Omega as Ω
import QBS.BoolQ as BQ
import QBS.Inference.BoolDist as BD
open import QBS.Continuous.SignedTests using (module SignedTests)
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.ExpectationProduct as EP
import QBS.Inference.ExpectationExamples as EE
import QBS.Inference.Sampler as SM
import QBS.Inference.CoinUniformPrior as CUP
import QBS.Analysis.Archimedean as Archimedean
import QBS.Analysis.LowerRealsArch as LRA

open BQ.BoolOn S

-- the arithmetic, over an abstract commutative ring
module Alg {c ℓ} (R : CommutativeRing c ℓ) where
  open CommutativeRing R
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
  open SetoidReasoning setoid

  two three : Carrier
  two = 1# + 1#
  three = two + 1#

  six eighteen : Carrier → Carrier
  six t = ((t + t) + (t + t)) + (t + t)
  eighteen t = (six t + six t) + six t

  -- `10 + ... ≈ 1` from `u + 1 ≈ 0`
  u1 : (- 1#) + 1# ≈ 0#
  u1 = -‿inverseˡ 1#

  -- `6·(h + 2u·m + m) = 3·(h + h) + 4u·(3m) + 2·(3m)`
  exX : ∀ h m u → six ((h + (two * u) * m) + m) ≈
    ((three * (h + h) + ((two * two) * u) * ((m + m) + m)) + two * ((m + m) + m))
  exX = solve 3 (λ h m u → let t = (h :+ ((con 1 :+ con 1) :* u) :* m) :+ m in
    ((t :+ t) :+ (t :+ t)) :+ (t :+ t) :=
    (((con 1 :+ con 1) :+ con 1) :* (h :+ h) :+ (((con 1 :+ con 1) :* (con 1 :+ con 1)) :* u) :* ((m :+ m) :+ m))
      :+ (con 1 :+ con 1) :* ((m :+ m) :+ m)) refl

  finX : ∀ u → u + 1# ≈ 0# → (three * 1# + ((two * two) * u) * 1#) + two * 1# ≈ 1#
  finX u e = begin
    (three * 1# + ((two * two) * u) * 1#) + two * 1# ≈⟨ lin u ⟩
    1# + (two * two) * (u + 1#) ≈⟨ +-cong refl (*-cong refl e) ⟩
    1# + (two * two) * 0# ≈⟨ z ⟩
    1# ∎
    where
    lin : ∀ u → (three * 1# + ((two * two) * u) * 1#) + two * 1# ≈ 1# + (two * two) * (u + 1#)
    lin = solve 1 (λ u → (((con 1 :+ con 1) :+ con 1) :* con 1 :+ (((con 1 :+ con 1) :* (con 1 :+ con 1)) :* u) :* con 1)
      :+ (con 1 :+ con 1) :* con 1 := con 1 :+ ((con 1 :+ con 1) :* (con 1 :+ con 1)) :* (u :+ con 1)) refl
    z : 1# + (two * two) * 0# ≈ 1#
    z = solve 0 (con 1 :+ ((con 1 :+ con 1) :* (con 1 :+ con 1)) :* con 0 := con 1) refl

  -- the risk of `X`: `6·r = 1` from `h + h = 1`, `3m = 1`
  riskX-arith : ∀ h m → h + h ≈ 1# → (m + m) + m ≈ 1# → six ((h + (two * (- 1#)) * m) + m) ≈ 1#
  riskX-arith h m hh mm = trans (exX h m (- 1#))
    (trans (+-cong (+-cong (*-cong refl hh) (*-cong refl mm)) (*-cong refl mm)) (finX (- 1#) u1))

  -- `9r = ((3h + 1) + 9m) + (-6)m + (-6)h`, with `-6 = 6·(-1)`; twice it is `11 + 10u`
  exP : ∀ h m u → let R9 = ((((three * h + 1#) + (three * three) * m) + ((three * two) * u) * m) + ((three * two) * u) * h) in
    R9 + R9 ≈ (((three * (h + h) + two * 1#) + (three * two) * ((m + m) + m)) +
      ((two * two) * u) * ((m + m) + m)) + ((three * two) * u) * (h + h)
  exP = solve 3 (λ h m u → let t = ((((((con 1 :+ con 1) :+ con 1) :* h :+ con 1) :+
                                       (((con 1 :+ con 1) :+ con 1) :* ((con 1 :+ con 1) :+ con 1)) :* m) :+
                                     ((((con 1 :+ con 1) :+ con 1) :* (con 1 :+ con 1)) :* u) :* m) :+
                                   ((((con 1 :+ con 1) :+ con 1) :* (con 1 :+ con 1)) :* u) :* h) in
    t :+ t := (((((con 1 :+ con 1) :+ con 1) :* (h :+ h) :+ (con 1 :+ con 1) :* con 1) :+
      (((con 1 :+ con 1) :+ con 1) :* (con 1 :+ con 1)) :* ((m :+ m) :+ m)) :+
      (((con 1 :+ con 1) :* (con 1 :+ con 1)) :* u) :* ((m :+ m) :+ m)) :+
      ((((con 1 :+ con 1) :+ con 1) :* (con 1 :+ con 1)) :* u) :* (h :+ h)) refl

  finP : ∀ u → u + 1# ≈ 0# →
    (((three * 1# + two * 1#) + (three * two) * 1#) + ((two * two) * u) * 1#) + ((three * two) * u) * 1# ≈ 1#
  finP u e = begin
    (((three * 1# + two * 1#) + (three * two) * 1#) + ((two * two) * u) * 1#) + ((three * two) * u) * 1#
      ≈⟨ lin u ⟩
    1# + (three * three + 1#) * (u + 1#) ≈⟨ +-cong refl (*-cong refl e) ⟩
    1# + (three * three + 1#) * 0# ≈⟨ z ⟩
    1# ∎
    where
    lin : ∀ u → (((three * 1# + two * 1#) + (three * two) * 1#) + ((two * two) * u) * 1#) + ((three * two) * u) * 1#
      ≈ 1# + (three * three + 1#) * (u + 1#)
    lin = solve 1 (λ u → let t2 = con 1 :+ con 1 ; t3 = t2 :+ con 1 in
      ((((t3 :* con 1 :+ t2 :* con 1) :+ (t3 :* t2) :* con 1) :+ ((t2 :* t2) :* u) :* con 1) :+ ((t3 :* t2) :* u) :* con 1)
      := con 1 :+ (t3 :* t3 :+ con 1) :* (u :+ con 1)) refl
    z : 1# + (three * three + 1#) * 0# ≈ 1#
    z = solve 0 (con 1 :+ ((((con 1 :+ con 1) :+ con 1) :* ((con 1 :+ con 1) :+ con 1)) :+ con 1) :* con 0 := con 1) refl

  -- `2·(9r) = 1`
  riskP9-arith : ∀ h m → h + h ≈ 1# → (m + m) + m ≈ 1# →
    let R9 = ((((three * h + 1#) + (three * three) * m) + ((three * two) * (- 1#)) * m) + ((three * two) * (- 1#)) * h)
    in R9 + R9 ≈ 1#
  riskP9-arith h m hh mm = trans (exP h m (- 1#)) (trans
    (+-cong (+-cong (+-cong (+-cong (*-cong refl hh) refl) (*-cong refl mm)) (*-cong refl mm)) (*-cong refl hh))
    (finP (- 1#) u1))

  -- scaling by `⅓·⅓`: `18·(c·c·R) = (3c)(3c)·(R + R)`
  riskP-arith : ∀ c r → (c + c) + c ≈ 1# → r + r ≈ 1# → eighteen ((c * c) * r) ≈ 1#
  riskP-arith c r cc rr = begin
    eighteen ((c * c) * r) ≈⟨ ex c r ⟩
    (((c + c) + c) * ((c + c) + c)) * (r + r) ≈⟨ *-cong (*-cong cc cc) rr ⟩
    (1# * 1#) * 1# ≈⟨ one ⟩
    1# ∎
    where
    ex : ∀ c r → eighteen ((c * c) * r) ≈ (((c + c) + c) * ((c + c) + c)) * (r + r)
    ex = solve 2 (λ c r → let t = ((((c :* c) :* r) :+ ((c :* c) :* r)) :+ (((c :* c) :* r) :+ ((c :* c) :* r))) :+
                                  (((c :* c) :* r) :+ ((c :* c) :* r)) in
      (t :+ t) :+ t := (((c :+ c) :+ c) :* ((c :+ c) :+ c)) :* (r :+ r)) refl
    one : (1# * 1#) * 1# ≈ 1#
    one = solve 0 ((con 1 :* con 1) :* con 1 := con 1) refl

module CoinBayesRisk (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open Ω.OmegaSemiring A using (_≈_; _+_; 0#; 1#; refl)
  open Bounded A using (Sg; _≃_; mk≃; ≃-trans; ≃-sym; ≃-refl; _+S_; _*S_; +S-cong; *S-cong; *S-identityˡ;
    *S-identityʳ; ι; ι-+; ι-*; finite; -S_; 0S; 1S; isCommutativeRing)
  open SubSemiring using (Is-0; Is-1; Is-+)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre; joinPre; TQ)
  open Strength A (lemOf lem₁) probClass using (σPre; σH)
  open Archimedean.Arch (LRA.lowerRealsArch (lemOf lem₁)) using () renaming (half+half to hh)
  open Uniform lem₁ using (uniform)
  open UniformMoment lem₁ using (m≤1; second-moment)
  open SM.Sampler lem₁ using (lawAt)
  open ER.ExpectationResp lem₁ using (E-at)
  open EX.Expectation lem₁ using (valT; precompT; expT; constT; scaleT; _+T_; E-at-join; E-at-map; E-at-expT; E-at-+;
    E-at-scale; E-at-const)
  open EP.ExpectationProduct lem₁ using (E-at-cong; _⊗T_; E-at-σ)
  open EE.ExpectationExamples lem₁ using (idT; sqT; E-at-uniform-id; E-at-uniform-sq; b1; fh; ι-cong)
  open CUP.CoinUniformPrior lem₁ using (coinKernel; E-at-kernel; ι≃id)
  open SignedTests (lemOf lem₁) using (STest)
  open BD.BoolDist lem₁ using (indT)

  -- Opaque copies of the ring operations of `Sg`: the lemmas of `Alg` are applied to `ring′`, and since the operations are
  -- abstract the unifier never unfolds the arithmetic of lower reals (each is `≃`-equal to the original).
  abstract
    infixl 6 _⊞_
    infixl 7 _⊠_
    _⊞_ _⊠_ : Sg → Sg → Sg
    _⊞_ = _+S_
    _⊠_ = _*S_

    ⊟_ : Sg → Sg
    ⊟_ = -S_

    isCR : IsCommutativeRing _≃_ _⊞_ _⊠_ ⊟_ 0S 1S
    isCR = isCommutativeRing

    ⊞-≃ : ∀ a b → (a ⊞ b) ≃ (a +S b)
    ⊞-≃ a b = ≃-refl

    ⊠-≃ : ∀ a b → (a ⊠ b) ≃ (a *S b)
    ⊠-≃ a b = ≃-refl

  ring′ : CommutativeRing _ _
  ring′ = record { Carrier = Sg ; _≈_ = _≃_ ; _+_ = _⊞_ ; _*_ = _⊠_ ; -_ = ⊟_ ; 0# = 0S ; 1# = 1S ; isCommutativeRing = isCR }

  open Alg ring′

  -- the original operations, converted
  ⊞-cong′ : ∀ {a b x y} → a ≃ x → b ≃ y → (a +S b) ≃ (x ⊞ y)
  ⊞-cong′ ea eb = ≃-trans (+S-cong ea eb) (≃-sym (⊞-≃ _ _))

  ⊠-cong′ : ∀ {a b x y} → a ≃ x → b ≃ y → (a *S b) ≃ (x ⊠ y)
  ⊠-cong′ ea eb = ≃-trans (*S-cong ea eb) (≃-sym (⊠-≃ _ _))

  ----------------------------------------------------------------------------
  -- the joint law of (θ, X)

  J : QBS S
  J = _×Q_ S AQ BoolQ

  -- θ ↦ the law of (θ , a flip at θ)
  K : Hom S AQ (TQ J)
  K = _∘H_ S (σH AQ BoolQ) (pairQ S {AQ} {AQ} {TQ BoolQ} (idH S) coinKernel)

  joint : Pre J
  joint = joinPre (mapPre K uniform)

  -- a product statistic `g(θ)·h(X)`: its expectation is the uniform expectation of `θ ↦ g(θ)·E[h | θ]`
  E-joint : ∀ (g : STest AQ) (h : STest BoolQ) (f : STest AQ) →
    (∀ a → valT g a *S E-at (lawAt coinKernel a) h ≃ valT f a) → E-at joint (g ⊗T h) ≃ E-at uniform f
  E-joint g h f pw = ≃-trans (E-at-join (mapPre K uniform) (g ⊗T h)) (≃-trans (E-at-map K uniform (expT (g ⊗T h)))
    (E-at-cong uniform _ f (λ a → ≃-trans (E-at-expT (σPre (a , lawAt coinKernel a)) (g ⊗T h))
      (≃-trans (E-at-σ a (lawAt coinKernel a) g h) (pw a)))))

  ----------------------------------------------------------------------------
  -- the pieces: X, θ·X, θ² and θ

  oneA : STest AQ
  oneA = constT 1S

  oneB : STest BoolQ
  oneB = constT 1S

  X1 Xθ θ² θ1 : STest J
  X1 = oneA ⊗T indT
  Xθ = idT ⊗T indT
  θ² = sqT ⊗T oneB
  θ1 = idT ⊗T oneB

  val-one : ∀ (Y : QBS S) (y : QBS.∣ Y ∣) → valT (constT {Y} 1S) y ≃ 1S
  val-one Y y = mk≃ 0# (Is-0 finite) refl

  pw-X1 : ∀ a → valT oneA a *S E-at (lawAt coinKernel a) indT ≃ valT idT a
  pw-X1 a = ≃-trans (*S-cong (val-one AQ a) (E-at-kernel a)) (≃-trans (*S-identityˡ _) (ι≃id a))

  pw-Xθ : ∀ a → valT idT a *S E-at (lawAt coinKernel a) indT ≃ valT sqT a
  pw-Xθ a = ≃-trans (*S-cong (≃-sym (ι≃id a)) (E-at-kernel a))
    (≃-trans (≃-sym (ι-* (b1 (proj₂ a)) (b1 (proj₂ a)))) (mk≃ 0# (Is-0 finite) refl))

  pw-θ² : ∀ a → valT sqT a *S E-at (lawAt coinKernel a) oneB ≃ valT sqT a
  pw-θ² a = ≃-trans (*S-cong ≃-refl (E-at-const (lawAt coinKernel a) 1S)) (*S-identityʳ _)

  pw-θ1 : ∀ a → valT idT a *S E-at (lawAt coinKernel a) oneB ≃ valT idT a
  pw-θ1 a = ≃-trans (*S-cong ≃-refl (E-at-const (lawAt coinKernel a) 1S)) (*S-identityʳ _)

  fm : _
  fm = b1 m≤1

  E-X1 : E-at joint X1 ≃ ι fh
  E-X1 = ≃-trans (E-joint oneA indT idT pw-X1) E-at-uniform-id

  E-Xθ : E-at joint Xθ ≃ ι fm
  E-Xθ = ≃-trans (E-joint idT indT sqT pw-Xθ) E-at-uniform-sq

  E-θ² : E-at joint θ² ≃ ι fm
  E-θ² = ≃-trans (E-joint sqT oneB sqT pw-θ²) E-at-uniform-sq

  E-θ1 : E-at joint θ1 ≃ ι fh
  E-θ1 = ≃-trans (E-joint idT oneB idT pw-θ1) E-at-uniform-id

  -- h + h = 1 and 3m = 1
  h2 : ι fh ⊞ ι fh ≃ 1S
  h2 = ≃-trans (⊞-≃ _ _) (≃-trans (≃-sym (ι-+ fh fh)) (ι-cong (Is-+ finite fh fh) (Is-1 finite) hh))

  m3 : (ι fm ⊞ ι fm) ⊞ ι fm ≃ 1S
  m3 = ≃-trans (⊞-≃ _ _) (≃-trans (+S-cong (⊞-≃ _ _) ≃-refl) (≃-trans (+S-cong (≃-sym (ι-+ fm fm)) ≃-refl)
    (≃-trans (≃-sym (ι-+ (Is-+ finite fm fm) fm))
    (ι-cong (Is-+ finite (Is-+ finite fm fm) fm) (Is-1 finite) second-moment))))

  six-cong : ∀ {x y} → x ≃ y → six x ≃ six y
  six-cong e = +-cong (+-cong (+-cong e e) (+-cong e e)) (+-cong e e)
    where open CommutativeRing ring′ using (+-cong)

  eighteen-cong : ∀ {x y} → x ≃ y → eighteen x ≃ eighteen y
  eighteen-cong e = +-cong (+-cong (six-cong e) (six-cong e)) (six-cong e)
    where open CommutativeRing ring′ using (+-cong)

  ----------------------------------------------------------------------------
  -- the frequentist estimator θ̂ = X

  cX : Sg
  cX = two ⊠ (⊟ 1S)

  cXθ : STest J
  cXθ = scaleT cX Xθ

  -- (X − θ)² = X − 2·θX + θ²  (X² = X)
  errX : STest J
  errX = (X1 +T cXθ) +T θ²

  eX1 : E-at joint cXθ ≃ cX ⊠ ι fm
  eX1 = ≃-trans (E-at-scale joint cX Xθ) (⊠-cong′ (≃-refl {cX}) E-Xθ)

  eX2 : E-at joint (X1 +T cXθ) ≃ ι fh ⊞ cX ⊠ ι fm
  eX2 = ≃-trans (E-at-+ joint X1 cXθ) (⊞-cong′ E-X1 eX1)

  -- the Bayes risk of X
  riskX : Sg
  riskX = E-at joint errX

  riskX-eq : riskX ≃ ((ι fh ⊞ cX ⊠ ι fm) ⊞ ι fm)
  riskX-eq = ≃-trans (E-at-+ joint (X1 +T cXθ) θ²) (⊞-cong′ eX2 E-θ²)

  -- r(X) = ½ − ⅓ = ⅙
  risk-X : six riskX ≃ 1S
  risk-X = ≃-trans (six-cong riskX-eq) (riskX-arith (ι fh) (ι fm) h2 m3)

  ----------------------------------------------------------------------------
  -- the Bayes estimator θ̂ = (X + 1)/3

  n6 : Sg
  n6 = (three ⊠ two) ⊠ (⊟ 1S)

  c3 c9 cP1 cP2 : STest J
  c3 = scaleT three X1
  c9 = scaleT (three ⊠ three) θ²
  cP1 = scaleT n6 Xθ
  cP2 = scaleT n6 θ1

  -- (3θ̂ − 3θ)² = 3X + 1 + 9θ² − 6·θX − 6·θ
  errP9 : STest J
  errP9 = (((c3 +T constT 1S) +T c9) +T cP1) +T cP2

  eP1 : E-at joint c3 ≃ three ⊠ ι fh
  eP1 = ≃-trans (E-at-scale joint three X1) (⊠-cong′ (≃-refl {three}) E-X1)

  eP2 : E-at joint (c3 +T constT 1S) ≃ three ⊠ ι fh ⊞ 1S
  eP2 = ≃-trans (E-at-+ joint c3 (constT 1S)) (⊞-cong′ eP1 (E-at-const joint 1S))

  eP3 : E-at joint ((c3 +T constT 1S) +T c9) ≃ (three ⊠ ι fh ⊞ 1S) ⊞ (three ⊠ three) ⊠ ι fm
  eP3 = ≃-trans (E-at-+ joint (c3 +T constT 1S) c9) (⊞-cong′ eP2
    (≃-trans (E-at-scale joint (three ⊠ three) θ²) (⊠-cong′ (≃-refl {three ⊠ three}) E-θ²)))

  eP4 : E-at joint (((c3 +T constT 1S) +T c9) +T cP1) ≃ ((three ⊠ ι fh ⊞ 1S) ⊞ (three ⊠ three) ⊠ ι fm) ⊞ n6 ⊠ ι fm
  eP4 = ≃-trans (E-at-+ joint ((c3 +T constT 1S) +T c9) cP1) (⊞-cong′ eP3
    (≃-trans (E-at-scale joint n6 Xθ) (⊠-cong′ (≃-refl {n6}) E-Xθ)))

  -- the scaled Bayes risk 9·r of the posterior mean
  riskP9 : Sg
  riskP9 = E-at joint errP9

  riskP9-eq : riskP9 ≃ ((((three ⊠ ι fh ⊞ 1S) ⊞ (three ⊠ three) ⊠ ι fm) ⊞ n6 ⊠ ι fm) ⊞ n6 ⊠ ι fh)
  riskP9-eq = ≃-trans (E-at-+ joint (((c3 +T constT 1S) +T c9) +T cP1) cP2) (⊞-cong′ eP4
    (≃-trans (E-at-scale joint n6 θ1) (⊠-cong′ (≃-refl {n6}) E-θ1)))

  -- 2·(9r) = 1
  risk-P9 : riskP9 ⊞ riskP9 ≃ 1S
  risk-P9 = ≃-trans (CommutativeRing.+-cong ring′ riskP9-eq riskP9-eq) (riskP9-arith (ι fh) (ι fm) h2 m3)

  -- (θ̂ − θ)² = (⅓·⅓)·(3θ̂ − 3θ)²
  errP : STest J
  errP = scaleT (ι fm ⊠ ι fm) errP9

  -- the Bayes risk of the posterior mean
  riskP : Sg
  riskP = E-at joint errP

  riskP-eq : riskP ≃ (ι fm ⊠ ι fm) ⊠ riskP9
  riskP-eq = ≃-trans (E-at-scale joint (ι fm ⊠ ι fm) errP9) (≃-sym (⊠-≃ _ _))

  -- r(θ̂) = 1/18
  risk-P : eighteen riskP ≃ 1S
  risk-P = ≃-trans (eighteen-cong riskP-eq) (riskP-arith (ι fm) riskP9 m3 risk-P9)

  ----------------------------------------------------------------------------
  -- the comparison: r(X) = ⅙ = 3/18 against r(posterior mean) = 1/18

  risk-X18 : eighteen riskX ≃ three
  risk-X18 = CommutativeRing.+-cong ring′ (CommutativeRing.+-cong ring′ risk-X risk-X) risk-X
