{-# OPTIONS --safe --without-K #-}

-- Bayes' rule for s-finite measures (the general `posterior` and `bayes`), with the Beta(2,1) coin example: the posterior as an
-- actual distribution, by reweighting and normalising (`plans/03-bayesian-frequentist.md`).
--
--   * Bayes' rule in general: for a prior `p : C.Pre Θ` and a likelihood `ℓ : Θ ⇒ WQ`, the unnormalised posterior is
--     `reweightPre ℓ (ιPre p)` (`Continuous/SFiniteReweight`), of mass `∫ ℓ dp` (`massP-rw`); given `(∫ ℓ dp) * n ≈ 1`
--     the posterior `posterior ℓ p n h = normPre …` (`Continuous/SFiniteNorm`) satisfies `bayes`:
--     `∫ f d(posterior) ≈ n * ∫ ℓ·f dp`.
--   * The coin with a uniform prior on θ and one observed head: the likelihood is `likH θ = θ` (the coercion of the
--     identity of the unit interval).  `massP-post1 : massP (unnormalised) ≈ ½` is P(H) = ∫ θ dθ; with `n = 2`
--     (`half-two : ½ * 2 ≈ 1`) the posterior `post1 : C.Pre AQ` is Beta(2,1), of density 2θ.
--   * The posterior mean: `post1-mean : 3 · ∫ θ d post1 ≈ 2`, i.e. E[θ | H] = ⅔ (multiplied out, no division);
--     `E-at-post1-id` states the same through the expectation interface (`E-at` with `idT`).
--   * Sequential updating: the posterior after the data H, H, obtained by reweighting `post1` by θ and normalising
--     (`post2-seq`), equals the posterior obtained by reweighting the prior by θ² and normalising (`post2-batch`):
--     `post2-agree : post2-seq ≈ᵖ post2-batch`.  Both have `n₂ = 3·½ = 3/2` and `n = 3` respectively.
-- Values are lower reals (no subtraction or division), so the statements are multiplied out.
module QBS.Inference.CoinPosterior where

open import Algebra using (CommutativeSemiring)
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.ExpectationExamples as EE
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
open import QBS.Continuous.Monad using (module Continuous)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.UniformMoment using (module UniformMoment)

-- the semiring algebra, over an abstract commutative semiring (the solver is slow on the concrete cut semiring)
module Alg {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R
  open SetoidReasoning setoid

  -- `n·m + n·m + n·m = n·(m + m + m)`
  triple : ∀ n m → ((n * m) + (n * m)) + (n * m) ≈ n * ((m + m) + m)
  triple n m = solve 2 (λ n m → ((n :* m) :+ (n :* m)) :+ (n :* m) := n :* ((m :+ m) :+ m)) refl n m

  -- `m·(1+1+1) = m + m + m`
  three-mul : ∀ m → m * ((1# + 1#) + 1#) ≈ (m + m) + m
  three-mul m = solve 1 (λ m → m :* ((con 1 :+ con 1) :+ con 1) := (m :+ m) :+ m) refl m

  -- `(a·b)·(c·d) = (a·d)·(b·c)`
  swap4 : ∀ a b c d → (a * b) * (c * d) ≈ (a * d) * (b * c)
  swap4 a b c d = solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* d) :* (b :* c)) refl a b c d

module CoinPosterior (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J-cong; J-fun; J-irrel)
  open FairCoin lem₁ using (fairCoin)
  open OmegaSemiring A using (_≈_; _*_; _+_; 1#; refl; sym; trans; *-cong; +-cong; *-identityˡ; *-identityʳ; *-assoc;
    distribˡ; *-comm; ≤-refl; commutativeSemiring)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (module C; XW; ∫ᴹ; ∫ᴹ-cong; mψ)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteNorm (lemOf lem₁) using (massP; normPre; ∫-normPre; coeH; ∫-vs-ᴹ; ι-reflect)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open UnitInterval A using (AQ)
  open LevelSets (lemOf lem₁) using (LS)
  open Uniform lem₁ using (uniform; ∫-uniform-id)
  open UniformMoment lem₁ using (Fun-e²; second-moment) renaming (m to m2)
  open Alg commutativeSemiring
  open Bounded A using (Bnd; finite; _+S_; +S-cong; _≃_; ≃-trans; ≃-sym; ≃-refl; ι; ι-+)
  open BoundedSignedTests (lemOf lem₁) using (STest)
  open Continuous A (lemOf lem₁) (Integration.probClass A) using (Pre)
  open ER.ExpectationResp lem₁ using (E-at)
  open EE.ExpectationExamples lem₁ using (idT; E-at-ι; b1; zeroJ; ι-cong)
  open UniformMoment lem₁ using (m≤1)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- Bayes' rule in general

  -- the mass of the unnormalised posterior is the marginal likelihood `∫ ℓ dp`
  massP-rw : ∀ {Θ : QBS S} (ℓ : Hom S Θ WQ) (p : C.Pre Θ) →
    massP {Θ} (reweightPre {Θ} ℓ (ιPre {Θ} p)) ≈ ∫ᴹ {Θ} (ιPre {Θ} p) ℓ
  massP-rw {Θ} ℓ p = trans (∫ᴹ-reweight {Θ} ℓ (ιPre {Θ} p) (constW 1#))
    (∫ᴹ-cong {Θ} (ιPre {Θ} p) {mulH {Θ} ℓ (constW 1#)} {ℓ} (λ x → *-identityʳ _))

  inv-rw : ∀ {Θ : QBS S} (ℓ : Hom S Θ WQ) (p : C.Pre Θ) (n : _) → ∫ᴹ {Θ} (ιPre {Θ} p) ℓ * n ≈ 1# →
    massP {Θ} (reweightPre {Θ} ℓ (ιPre {Θ} p)) * n ≈ 1#
  inv-rw ℓ p n h = trans (*-cong (massP-rw ℓ p) refl) h

  -- the normalised posterior
  abstract
    posterior : ∀ {Θ : QBS S} (ℓ : Hom S Θ WQ) (p : C.Pre Θ) (n : _) → ∫ᴹ {Θ} (ιPre {Θ} p) ℓ * n ≈ 1# → C.Pre Θ
    posterior {Θ} ℓ p n h = normPre {Θ} (reweightPre {Θ} ℓ (ιPre {Θ} p)) n (inv-rw ℓ p n h)

    -- Bayes' rule: `∫ f d(posterior) = n · ∫ ℓ·f dp`
    bayes : ∀ {Θ : QBS S} (ℓ : Hom S Θ WQ) (p : C.Pre Θ) (n : _) (h : ∫ᴹ {Θ} (ιPre {Θ} p) ℓ * n ≈ 1#) (f : Hom S Θ WQ) →
      ∫ᴹ {Θ} (ιPre {Θ} (posterior ℓ p n h)) f ≈ n * ∫ᴹ {Θ} (ιPre {Θ} p) (mulH {Θ} ℓ f)
    bayes {Θ} ℓ p n h f = trans (∫-normPre {Θ} (reweightPre {Θ} ℓ (ιPre {Θ} p)) n (inv-rw ℓ p n h) f)
      (*-cong refl (∫ᴹ-reweight {Θ} ℓ (ιPre {Θ} p) f))

  ----------------------------------------------------------------------------
  -- the coin with a uniform prior, after one head

  -- the likelihood of one head at bias θ is θ
  likH : Hom S AQ WQ
  likH = coeH {AQ} (idH S {AQ})

  -- the marginal likelihood `P(H) = ∫ θ dθ = ½`
  mean-ι : ∫ᴹ {AQ} (ιPre {AQ} uniform) likH ≈ half
  mean-ι = trans (sym (∫-vs-ᴹ {AQ} uniform (idH S {AQ}))) ∫-uniform-id

  -- the unnormalised posterior has mass ½
  massP-post1 : massP {AQ} (reweightPre {AQ} likH (ιPre {AQ} uniform)) ≈ half
  massP-post1 = trans (massP-rw likH uniform) mean-ι

  two : _
  two = 1# + 1#

  half-two : half * two ≈ 1#
  half-two = trans (distribˡ half 1# 1#) (trans (+-cong (*-identityʳ half) (*-identityʳ half)) hh)

  half-inv : ∫ᴹ {AQ} (ιPre {AQ} uniform) likH * two ≈ 1#
  half-inv = trans (*-cong mean-ι refl) half-two

  -- the posterior Beta(2,1) after one head
  post1 : C.Pre AQ
  post1 = posterior likH uniform two half-inv

  -- `E[θ² ] = m`, with `3m = 1`
  sq-ι : ∫ᴹ {AQ} (ιPre {AQ} uniform) (mulH {AQ} likH likH) ≈ m2
  sq-ι = trans (J-cong fairCoin (mψ {AQ} (ιPre {AQ} uniform) (mulH {AQ} likH likH)) (LS Fun-e²) (λ r → *-identityˡ _))
    (J-fun fairCoin Fun-e²)

  -- the posterior mean, in the monad's weighted integral: `∫ θ d post1 = 2·m`
  post1-mean-ι : ∫ᴹ {AQ} (ιPre {AQ} post1) likH ≈ two * m2
  post1-mean-ι = trans (bayes likH uniform two half-inv likH) (*-cong refl sq-ι)

  -- three copies of `2·m` make 2
  three-two : ((two * m2) + (two * m2)) + (two * m2) ≈ two
  three-two = trans (triple two m2) (trans (*-cong refl second-moment) (*-identityʳ two))

  -- the posterior mean E[θ | H] = ⅔, multiplied out: three copies of it make 2
  post1-mean : let X = C.∫ {AQ} post1 (idH S {AQ}) in (X + X) + X ≈ two
  post1-mean = trans (+-cong (+-cong e e) e) three-two
    where e = trans (∫-vs-ᴹ {AQ} post1 (idH S {AQ})) post1-mean-ι

  ----------------------------------------------------------------------------
  -- the same through the expectation interface

  bnd-two : Bnd two
  bnd-two = SubSemiring.Is-+ finite (b1 ≤-refl) (b1 ≤-refl)

  bnd-mean : Bnd (two * m2)
  bnd-mean = SubSemiring.Is-* finite bnd-two (b1 m≤1)

  -- `E-at post1 idT = 2·m` (= ⅔)
  E-at-post1-id : E-at post1 idT ≃ ι bnd-mean
  E-at-post1-id = E-at-ι post1 idT bnd-mean
    (trans (J-irrel (C.Pre.m post1) _ (LS F)) (trans (J-fun (C.Pre.m post1) F)
      (trans (∫-vs-ᴹ {AQ} post1 (idH S {AQ})) post1-mean-ι))) (zeroJ post1)
    where F = map-random (idH S {AQ}) {C.Pre.α post1} (C.Pre.α-random post1)

  -- multiplied out, three copies of E[θ | H] make 2
  E-at-post1-id³ : let E = E-at post1 idT in (E +S E) +S E ≃ ι bnd-two
  E-at-post1-id³ = ≃-trans (+S-cong (+S-cong E-at-post1-id E-at-post1-id) E-at-post1-id)
    (≃-trans (+S-cong (≃-sym (ι-+ bnd-mean bnd-mean)) ≃-refl)
    (≃-trans (≃-sym (ι-+ (SubSemiring.Is-+ finite bnd-mean bnd-mean) bnd-mean)) (ι-cong _ _ three-two)))

  ----------------------------------------------------------------------------
  -- the data H, H: sequential and batch updating agree

  three : _
  three = (1# + 1#) + 1#

  -- the second normaliser 3/2 = 3·½
  n₂ : _
  n₂ = three * half

  -- batch: reweight the prior by θ² and normalise by 3
  inv-batch : ∫ᴹ {AQ} (ιPre {AQ} uniform) (mulH {AQ} likH likH) * three ≈ 1#
  inv-batch = trans (*-cong sq-ι refl) (trans (three-mul m2) second-moment)

  post2-batch : C.Pre AQ
  post2-batch = posterior (mulH {AQ} likH likH) uniform three inv-batch

  -- sequential: reweight the first posterior by θ again and normalise by 3/2
  inv-seq : ∫ᴹ {AQ} (ιPre {AQ} post1) likH * n₂ ≈ 1#
  inv-seq = trans (*-cong post1-mean-ι refl) (trans (swap4 two m2 three half)
    (trans (*-cong half-two' (three-mul m2)) (trans (*-cong refl second-moment) (*-identityʳ 1#))))
    where half-two' = trans (*-comm two half) half-two

  post2-seq : C.Pre AQ
  post2-seq = posterior likH post1 n₂ inv-seq

  n₂-two : n₂ * two ≈ three
  n₂-two = trans (*-assoc three half two) (trans (*-cong refl half-two) (*-identityʳ three))

  -- pointwise: θ·(θ·f) = (θ·θ)·f
  assoc-ι : ∀ f → ∫ᴹ {AQ} (ιPre {AQ} uniform) (mulH {AQ} likH (mulH {AQ} likH f))
    ≈ ∫ᴹ {AQ} (ιPre {AQ} uniform) (mulH {AQ} (mulH {AQ} likH likH) f)
  assoc-ι f = ∫ᴹ-cong {AQ} (ιPre {AQ} uniform) (λ x → sym (*-assoc _ _ _))

  -- the data H, H: updating the posterior agrees with updating the prior by the squared likelihood
  post2-agree : C._≈ᵖ_ {AQ} post2-seq post2-batch
  post2-agree = ι-reflect {AQ} (λ f → trans (bayes likH post1 n₂ inv-seq f)
    (trans (*-cong refl (bayes likH uniform two half-inv (mulH {AQ} likH f)))
    (trans (sym (*-assoc n₂ two _)) (trans (*-cong n₂-two (assoc-ι f))
    (sym (bayes (mulH {AQ} likH likH) uniform three inv-batch f))))))
