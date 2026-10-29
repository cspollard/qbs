{-# OPTIONS --safe --without-K #-}

-- SKELETON (holes).  Every s-finite measure is a countable sum of scaled laws of probability
-- measures: the `scaled-laws` field of `StatisticalInterface`.
--
-- A measure `[α, m, w]` is split along the level sets `Bₙ = {r | n ≤ w r < n+1}` of its weight.
-- On `Bₙ` the density `dₙ = (min(w, n+1)·χ_{Bₙ}) / (n+1)` is `Meas` and `≤ 1`, so `ν ₙ = dₙ · m` is a
-- sub-probability measure of mass `cₙ`; classically either `cₙ` is invertible (then `μₙ = cₙ⁻¹ νₙ`
-- is a probability measure) or `cₙ ≈ 0` (then any `μₙ` works with weight 0).  The scaled constant is
-- `(n+1)·cₙ`, and the probe is `x ∘ α`.

-- Prob is a sub-monad of the s-finite measures (`inclusion`: weight 1), the zero measure and `score`.

module QBS.Continuous.SFiniteDecomp where

open import Level using (lift; lower)
import Level as L
open import Function.Base using (id; _∘_; const)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Axiom.Extensionality.Propositional using (Extensionality)

open import QBS.Core
open import QBS.Category
open import QBS.Limits using (_×Q_; 1Q; fstQ; sndQ; pairQ; !Q)
import QBS.Probes as Probes
open import QBS.Borel.Core using (Measurable; measurable-∘)
open import QBS.Borel.Source using (R₁; cantorSource; down)
open import QBS.Borel.Merge using (mergeC; measurable-merge₁; Cyl-rect)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.LowerReals using (Cut)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Tensor using (module Tensor)
open import QBS.Analysis.JParam using (module JParam)
open import QBS.Analysis.Tonelli using (module Tonelli)
open import QBS.Continuous.Sample
open import QBS.Continuous.Monad using (module Continuous)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteMonad using (module SFiniteMonad)
open import QBS.Continuous.SFiniteStrong using (module SFiniteStrong)
open import QBS.Continuous.SFiniteSum using (module SFiniteSum)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteCommute using (module SFiniteCommute)
open import QBS.Continuous.ProbInstance using (module ContinuousProb)
open import QBS.Statistical using (StatisticalInterface)
import Categories.Category.Cocartesian as Cocartesian
open import QBS.Colimits using (cocartesian; _+Q_; Piece; ev)
open import QBS.Analysis.Series using (module Series)
import Data.Nat.Base as ℕ
open import QBS.Continuous.Strong using (module Strength)
open import Categories.Monad.Morphism using (Monad⇒-id)
open import QBS.Analysis.JFubini using (module JFubini)
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Monad using (Monad)
open import QBS.Analysis.Density using (module Density)
open import QBS.Analysis.LevelSets using (module LevelSets)

module SFiniteDecomp (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (funext : Extensionality L.zero L.zero) where
  open JParam lem
  open Meas lem
  open Tonelli lem using (Meas-J; J-bind)
  open Weights lem using (WQ; mulW; constW; oneW; zeroW)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ)
  open Integration A
  open Measurable A
  open Tensor A lem using (constK)
  open Density lem using (densM; J-dens)
  open LevelSets lem using (LS)
  open Split funext
  open UnitInterval A using (AQ)
  open RandomSource S using () renaming (meas-id to measId)
  open SFinite lem funext
  open WitM
  open SFiniteMonad lem funext
  open SFiniteStrong lem funext
  open SFiniteSum lem funext
  open SFiniteIncl lem funext
  open Series A
  open C using (Pre; mk; Joint; sec; sec-random; sndJ; fstJ; preJ; glueJ; r₀)
  open C.Pre
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- 1. measures with a `Meas` density (sub-probability when the density is ≤ 1)

  densityM : ∀ (m : Measure) (d : R₁ → Cut) → Meas d → (∀ r → d r ≤ 1#) → Measure
  densityM m d md d≤1 = densM m d md 1#
    (≤-trans (≤-reflexive (*-identityˡ _))
     (≤-trans (J-mono m md (LS (Fun-const 1# ≤-refl)) d≤1)
      (≤-trans (≤-reflexive (J-fun m (Fun-const 1# ≤-refl)))
       (Measure.I-sub m (Fun-const 1# ≤-refl)))))

  I-densityM : ∀ (m : Measure) (d : R₁ → Cut) (md : Meas d) (d≤1 : ∀ r → d r ≤ 1#) →
    ∀ h (fh : Fun h) (mdh : Meas (λ r → d r * h r)) →
    Measure.I (densityM m d md d≤1) h fh ≈ J m (λ r → d r * h r) mdh
  I-densityM m d md d≤1 h fh mdh = ?

  -- the total mass of a (sub-probability) measure
  massM : Measure → Cut
  massM ν = Measure.I ν (const 1#) (Fun-const 1# ≤-refl)

  -- normalisation of a measure of invertible mass (classical inverse, `Analysis/LowerInverse`)
  normM : ∀ (ν : Measure) (n : Cut) → massM ν * n ≈ 1# → Σ Measure IsProb
  normM ν n h = ?

  I-normM : ∀ (ν : Measure) (n : Cut) (h : massM ν * n ≈ 1#) f (ff : Fun f) →
    Measure.I (proj₁ (normM ν n h)) f ff ≈ n * Measure.I ν f ff
  I-normM ν n h f ff = ?

  ----------------------------------------------------------------------------
  -- 2. the level-set pieces of a measure `[α, m, w]`

  natC : ℕ → Cut
  natC ℕ.zero = 0#
  natC (ℕ.suc n) = natC n + 1#

  -- Bₙ = {r | n ≤ w r < n+1} as a weight function: min(w, n+1) · χ_{Bₙ} / (n+1)
  pieceDensity : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → R₁ → Cut
  pieceDensity p n = ?

  pieceDensity-Meas : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Meas (pieceDensity p n)
  pieceDensity-Meas p n = ?

  pieceDensity≤1 : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) r → pieceDensity p n r ≤ 1#
  pieceDensity≤1 p n r = ?

  -- the weight is the sum of the pieces: w r · f ≈ Σₙ (n+1) · dₙ r · f
  pieces-sum : ∀ {X : QBS S} (p : Pre (XW X)) r (c : Cut) →
    proj₁ (α p r) * c ≈ ∑ᶠ (λ n → (natC (ℕ.suc n) * pieceDensity p n r) * c)
  pieces-sum p r c = ?

  pieceMeasure : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Measure
  pieceMeasure p n = densityM (m p) (pieceDensity p n) (pieceDensity-Meas p n) (pieceDensity≤1 p n)

  -- the integrand of the n-th piece against a test function f
  pieceψ : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) → R₁ → Cut
  pieceψ {X} p n f r = pieceDensity p n r * (map f ⟨$⟩ proj₂ (α p r))

  pieceψ-Meas : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) → Meas (pieceψ {X} p n f)
  pieceψ-Meas {X} p n f = ?   -- Meas-⊗ (pieceDensity-Meas p n) (map-random f (proj₂ (α-random p)))

  -- the integral splits over the pieces (pieces-sum, then J-∑ for the series)
  ∫ᴹ-pieces : ∀ {X : QBS S} (p : Pre (XW X)) (f : Hom S X WQ) →
    ∫ᴹ {X} p f ≈ ∑ᶠ (λ n → natC (ℕ.suc n) * J (m p) (pieceψ {X} p n f) (pieceψ-Meas {X} p n f))
  ∫ᴹ-pieces {X} p f = ?

  -- the probe of the X-component of `p`, as a morphism ℛ ⇒ X
  probeOf : ∀ {X : QBS S} → Pre (XW X) → Hom S (Probes.ℛQ S) X
  probeOf p = Probes.probe S (proj₂ (α-random p))

  -- the mass of a piece, and the piece as a probability measure (a fixed dummy when the mass is 0,
  -- `lem` decides which; `normM` otherwise)
  pieceMass : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Cut
  pieceMass p n = massM (pieceMeasure p n)

  pieceProb : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) → Σ Measure IsProb
  pieceProb p n = ?

  -- mass · (integral against the normalised piece) = integral against the piece; both sides vanish when the mass is 0
  pieceProb-int : ∀ {X : QBS S} (p : Pre (XW X)) (n : ℕ) (f : Hom S X WQ) →
    pieceMass p n * J (proj₁ (pieceProb p n)) (λ r → map f ⟨$⟩ proj₂ (α p r))
      (map-random f (proj₂ (α-random p)))
    ≈ J (m p) (pieceψ {X} p n f) (pieceψ-Meas {X} p n f)
  pieceProb-int p n f = ?

  ----------------------------------------------------------------------------
  -- 3. the decomposition

  -- the law of the probe `a` under a probability measure, as a pre-measure of the probability monad
  lawPre : ∀ {X : QBS S} → Hom S (Probes.ℛQ S) X → Σ Measure IsProb → C.Pre X
  lawPre a (μ , pμ) = mk (λ r → map a ⟨$⟩ r) (Probes.unprobe S a) μ pμ

  scaledLawsPre : ∀ {X : QBS S} (p : Pre (XW X)) →
    Σ (ℕ → Hom S (Probes.ℛQ S) X) λ a →
    Σ (ℕ → ∣ WQ ∣) λ c →
    Σ (ℕ → Σ Measure IsProb) λ μ →
      ∀ (f : Hom S X WQ) → ∫ᴹ {X} p f ≈ ∑ᶠ (λ n → ∫ᴹ {X} (scalePre {X} (c n) (ιPre {X} (lawPre (a n) (μ n)))) f)
  scaledLawsPre p = ?

  -- (the global-element form, with `law` of `ContinuousProb`, is assembled in `SFiniteStat`)
