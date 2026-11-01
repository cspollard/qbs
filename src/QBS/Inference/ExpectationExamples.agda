{-# OPTIONS --safe --without-K #-}

-- Worked examples for the calculus of `E-at` (`Inference/Expectation`, `Inference/ExpectationProduct`).
--
--   * the uniform distribution (`Continuous/Uniform`) through the interface: with `idT` the identity statistic on the unit
--     interval `AQ` (positive part the inclusion `AQ → CutQ`, negative part zero, bound 1), `E-at uniform idT ≃ ι ½`
--     (`E-at-uniform-id`), reusing `UniformMean`; likewise the squared statistic `sqT`: `E-at uniform sqT ≃ ι m` with
--     `3m = 1` (`UniformMoment`, `E-at-uniform-sq`);
--   * a Bernoulli(½) distribution `bern : Pre AQ` (the first bit of the fair coin, valued in {0,1} ⊆ [0,1]), with
--     `E-at bern idT ≃ ι ½` (`E-at-bern`) from the first-bit decomposition of `Continuous/FirstBit`;
--   * independence: `E-at (bern ⊗ᵖ bern) (idT ⊗T idT) ≃ ι ½ *S ι ½` (`E-at-bern²`), and, multiplied out, four copies of
--     it add up to one (`E-at-bern²-quarter`).
--
-- Both distributions are `Pre AQ`; the two-point space `AQ ⊇ {0,1}` is used instead of a Boolean QBS, so that the indicator
-- of `true` is the identity statistic.
module QBS.Inference.ExpectationExamples where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Level using (lift; lower)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Borel.Cons using (consR; measurable-cons)
open import QBS.Borel.Core using (gen)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.FirstBit using (module FirstBit)
open import QBS.Continuous.Uniform using (module Uniform)
open import QBS.Continuous.UniformMean using (module UniformMean; module Alg)
open import QBS.Continuous.UniformMoment using (module UniformMoment)
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.Expectation as EX
import QBS.Inference.ExpectationProduct as EP

module ExpectationExamples (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-fun; J-irrel)
  open Integration A using (probClass; I; I-cong)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _*_; _+_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-refl;
    ≤-trans; ≤-reflexive; *-mono; 0-least; *-identityʳ; +-identityʳ; zeroʳ; distribʳ; commutativeSemiring)
  open Meas (lemOf lem₁) using (Meas-⊗)
  open LevelSets (lemOf lem₁) using (LS)
  open Bounded A using (Sg; Bnd; nat; _≃_; mk≃; ≃-trans; ≃-sym; _+S_; _*S_; finite; ι; ι-+; ι-*)
  open SignedIntegral (lemOf lem₁) using (J-const)
  open SignedTests (lemOf lem₁) using (CutQ; STest)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; mk)
  open Pre
  open Measurable A using (Fun; Fun-const; Fun-pre; ind)
  open Daniell lem₁ using (L-one)
  open Indicators A (lemOf lem₁) using (I-const)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open HalfOrder A (lowerRealsArch (lemOf lem₁)) using (half≤1)
  open Expansion A half hh using (expansion; Fun-expansion)
  open FairCoin lem₁ using (fairCoin)
  open FirstBit lem₁ using (firstBit-fun)
  open Uniform lem₁ using (uniform; ∫-uniform-id)
  open UniformMean lem₁ using (mean)
  open UniformMoment lem₁ using (e²; Meas-e²; Fun-e²; m≤1; second-moment) renaming (m to m2)
  open ER.ExpectationResp lem₁ using (E-at)
  open EX.Expectation lem₁ using (constH; pl)
  open EP.ExpectationProduct lem₁ using (_⊗T_; _⊗ᵖ_; E-at-⊗)
  open QBS using (∣_∣)

  pm : Integration.IsProb A fairCoin
  pm = I-const fairCoin L-one 1# ≤-refl

  ----------------------------------------------------------------------------
  -- reading off the expectation of a test whose negative part integrates to 0

  E-at-ι : ∀ {X : QBS S} (p : Pre X) (g : STest X) {a} (fa : Bnd a) →
    J (m p) (λ r → Hom.map (STest.pos g) ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random (STest.pos g) (α-random p)) ≈ a →
    J (m p) (λ r → Hom.map (STest.neg g) ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random (STest.neg g) (α-random p)) ≈ 0# →
    E-at p g ≃ ι fa
  E-at-ι p g {a} fa ep en = mk≃ 0# (SubSemiring.Is-0 finite) (+-cong (+-cong ep (sym en)) refl)

  b1 : ∀ {a} → a ≤ 1# → Bnd a
  b1 le = 1 , ≤-trans le (≤-reflexive (sym (+-identityʳ 1#)))

  -- the part 0
  zeroJ : ∀ {X : QBS S} (p : Pre X) →
    J (m p) (λ r → Hom.map (constH {X} 0#) ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random (constH {X} 0#) (α-random p)) ≈ 0#
  zeroJ p = trans (J-irrel (m p) _ _) (J-const (ok p) 0#)

  ----------------------------------------------------------------------------
  -- the identity and squaring statistics on the unit interval

  incl : Hom S AQ CutQ
  incl = record
    { map = record { to = proj₁ ; cong = λ e → e }
    ; map-random = λ f → LS f }

  sqH : Hom S AQ CutQ
  sqH = record
    { map = record { to = λ x → proj₁ x * proj₁ x ; cong = λ e → *-cong e e }
    ; map-random = λ {β} f → Meas-⊗ {λ r → proj₁ (β ⟨$⟩ r)} {λ r → proj₁ (β ⟨$⟩ r)} (LS f) (LS f) }

  idT : STest AQ
  idT = record
    { pos = incl ; neg = constH 0# ; bound = 1
    ; pos-bdd = λ x → ≤-trans (proj₂ x) (≤-reflexive (sym (+-identityʳ 1#)))
    ; neg-bdd = λ _ → 0-least }

  sqT : STest AQ
  sqT = record
    { pos = sqH ; neg = constH 0# ; bound = 1
    ; pos-bdd = λ x → ≤-trans (*-mono (proj₁ x) (proj₂ x))
        (≤-trans (≤-reflexive (*-identityʳ (proj₁ x))) (≤-trans (proj₂ x) (≤-reflexive (sym (+-identityʳ 1#)))))
    ; neg-bdd = λ _ → 0-least }

  -- E[U] = ½
  E-at-uniform-id : E-at uniform idT ≃ ι (b1 half≤1)
  E-at-uniform-id = E-at-ι uniform idT (b1 half≤1)
    (trans (J-irrel fairCoin _ (LS Fun-expansion)) (trans (J-fun fairCoin Fun-expansion) mean)) (zeroJ uniform)

  -- E[U²] = m, with 3m = 1
  E-at-uniform-sq : E-at uniform sqT ≃ ι (b1 m≤1)
  E-at-uniform-sq = E-at-ι uniform sqT (b1 m≤1)
    (trans (J-irrel fairCoin _ (LS Fun-e²)) (J-fun fairCoin Fun-e²)) (zeroJ uniform)

  ----------------------------------------------------------------------------
  -- Bernoulli(½): the first bit of the fair coin

  sel : Bool → ∣A∣
  sel true = 1#
  sel false = 0#

  bit : R₁ → ∣A∣
  bit r = sel (lower r 0)

  bit≤1 : ∀ r → bit r ≤ 1#
  bit≤1 r with lower r 0
  ... | true = ≤-refl
  ... | false = 0-least

  Fun-bit : Fun bit
  Fun-bit = ind {U = λ x → x 0 ≡ true} 1# ≤-refl (gen 0 true) on off bit≤1
    where
    on : ∀ r → lower r 0 ≡ true → bit r ≈ 1#
    on r p = OmegaSemiring.reflexive A (≡.cong sel p)
    off : ∀ r → (lower r 0 ≡ true → ⊥) → bit r ≈ 0#
    off r q with lower r 0 in e
    ... | true = ⊥-elim (q ≡.refl)
    ... | false = refl

  bernProbe : Func (RandomSource.Rˢ S) (QBS.Carrier AQ)
  bernProbe = record { to = λ r → bit r , bit≤1 r ; cong = λ e → OmegaSemiring.reflexive A (≡.cong sel (lower e 0)) }

  -- Bernoulli(½)
  bern : Pre AQ
  bern = mk bernProbe Fun-bit fairCoin L-one

  -- the integrand is 1 after `true` and 0 after `false`
  Fb : ∀ b → Fun (λ x → bit (consR b x))
  Fb b = Fun-pre {f = consR b} Fun-bit (measurable-cons b)

  I-const-bit : ∀ b → I fairCoin (λ x → bit (consR b x)) (Fb b) ≈ sel b
  I-const-bit true = trans (I-cong fairCoin {h′ = λ _ → 1#} (λ r → refl) (Fb true) (Fun-const 1# ≤-refl))
    (I-const fairCoin L-one 1# ≤-refl)
  I-const-bit false = trans (I-cong fairCoin {h′ = λ _ → 0#} (λ r → refl) (Fb false) (Fun-const 0# 0-least))
    (I-const fairCoin L-one 0# 0-least)

  -- E[B] = ½: split off the first bit (`firstBit-fun`)
  I-bit : I fairCoin bit Fun-bit ≈ half
  I-bit = trans (firstBit-fun Fun-bit) (trans (+-cong (*-cong refl (I-const-bit true)) (*-cong refl (I-const-bit false)))
    (trans (+-cong (*-identityʳ half) (zeroʳ half)) (+-identityʳ half)))

  jbit : J fairCoin bit (LS Fun-bit) ≈ half
  jbit = trans (J-fun fairCoin Fun-bit) I-bit

  E-at-bern : E-at bern idT ≃ ι (b1 half≤1)
  E-at-bern = E-at-ι bern idT (b1 half≤1) (trans (J-irrel fairCoin _ _) jbit) (zeroJ bern)

  ----------------------------------------------------------------------------
  -- two independent coins

  ι-cong : ∀ {a b} (fa : Bnd a) (fb : Bnd b) → a ≈ b → ι fa ≃ ι fb
  ι-cong fa fb e = mk≃ 0# (SubSemiring.Is-0 finite) (+-cong (+-cong e refl) refl)

  fh : Bnd half
  fh = b1 half≤1

  E-at-bern² : E-at (bern ⊗ᵖ bern) (idT ⊗T idT) ≃ ι fh *S ι fh
  E-at-bern² = ≃-trans (E-at-⊗ bern bern idT idT) (*S-cong E-at-bern E-at-bern)
    where open Bounded A using (*S-cong)

  -- ¼ multiplied out: four copies of E[B₁B₂] add up to one
  P² : Sg
  P² = E-at (bern ⊗ᵖ bern) (idT ⊗T idT)

  quarter-arith : let q = half * half in ((q + q) + (q + q)) ≈ 1#
  quarter-arith = trans (+-cong qq qq) hh
    where qq = trans (sym (distribʳ half half half)) (Alg.k commutativeSemiring half hh)

  E-at-bern²-quarter : (P² +S P²) +S (P² +S P²) ≃ ι (SubSemiring.Is-1 finite)
  E-at-bern²-quarter = ≃-trans (+S-cong (+S-cong e e) (+S-cong e e)) (≃-trans (+S-cong (+S-cong i i) (+S-cong i i))
    (≃-trans (+S-cong (≃-sym (ι-+ q′ q′)) (≃-sym (ι-+ q′ q′)))
    (≃-trans (≃-sym (ι-+ (SubSemiring.Is-+ finite q′ q′) (SubSemiring.Is-+ finite q′ q′))) (ι-cong _ _ quarter-arith))))
    where
    open Bounded A using (+S-cong)
    e = E-at-bern²
    q′ = SubSemiring.Is-* finite fh fh
    i = ≃-sym (ι-* fh fh)
