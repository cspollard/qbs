{-# OPTIONS --safe --without-K #-}

-- The variance of the uniform distribution.  With f = the binary expansion (as a signed function with zero negative
-- part), `Var f = E[f²] − (E f)²` (`Analysis/Variance`), `E f = ½` (`UniformMean`) and `3 E[f²] = 1`
-- (`UniformMoment`), so that twelve copies of `Var f` add up to one: Var = 1/12.
module QBS.Continuous.UniformVariance where

open import Level using (lift; lower)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.BinaryExpansion
open import QBS.Analysis.Signed
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Variance using (module Variance; module Arith)
open import QBS.Analysis.LowerReals using (LowerRealsOmega)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.CoinIntegral using (module Daniell; lemOf)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Continuous.FairCoin
open import QBS.Continuous.UniformMean using (module UniformMean)
open import QBS.Continuous.UniformMoment using (module UniformMoment)
open import QBS.Classical using (LEM₁)

module UniformVariance (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-fun; J-cong; J-irrel)
  open UniformMoment lem₁ using (e²; Meas-e²; Fun-e²; m; second-moment; m≤1)
  open SignedIntegral (lemOf lem₁)
  open Variance (lemOf lem₁) using (Bdd; _*SF_[_]; Var; var-formula)
  open Bounded A
  open SF
  open Integration A using (IsProb)
  open FairCoin lem₁ using (fairCoin)
  open Meas (lemOf lem₁) using (Meas; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open Indicators A (lemOf lem₁) using (I-const)
  open Daniell lem₁ using (L-one)
  open UniformMean lem₁ using (mean)
  open Measurable A using (Fun-const)
  open OmegaSemiring A using (_≈_; _≤_; 0#; 1#; _+_; _*_; refl; sym; trans; +-cong; *-cong; ≤-refl; ≤-trans; ≤-reflexive; +-identityʳ; +-identityˡ; zeroʳ; zeroˡ)
  R = lowerRealsArch (lemOf lem₁)
  open Arch R using (half) renaming (half+half to hh)
  open Expansion A half hh
  open HalfOrder A R using (half≤1)
  open Arith (OmegaSemiring.commutativeSemiring A) finite using (x4; x12; x12-cong; var-arith)

  pm : IsProb fairCoin
  pm = I-const fairCoin L-one 1# ≤-refl

  jpos : J fairCoin expansion (LS Fun-expansion) ≈ half
  jpos = trans (J-fun fairCoin Fun-expansion) mean

  jneg : J fairCoin (λ _ → 0#) (Meas-const 0#) ≈ 0#
  jneg = J-const pm 0#

  -- a signed function whose positive part integrates to `a` and negative part to 0 has integral `a`
  ι-cong : ∀ {a b} (fa : Bnd a) (fb : Bnd b) → a ≈ b → ι fa ≃ ι fb
  ι-cong {a} {b} fa fb e = mk≃ 0# (SubSemiring.Is-0 finite) (+-cong {a + 0#} {b + 0#} {0#} {0#} (+-cong {a} {b} {0#} {0#} e refl) refl)

  E-ι : ∀ {m} (f : SF m) {a} (fa : Bnd a) → J m (f⁺ f) (f⁺-meas f) ≈ a → J m (f⁻ f) (f⁻-meas f) ≈ 0# → E f ≃ ι fa
  E-ι {m} f {a} fa ep en = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong {J m (f⁺ f) (f⁺-meas f) + 0#} {a + J m (f⁻ f) (f⁻-meas f)} {0#} {0#}
      (+-cong {J m (f⁺ f) (f⁺-meas f)} {a} {0#} {J m (f⁻ f) (f⁻-meas f)} ep (sym en)) refl)

  pp-eq : ∀ x → expansion x * expansion x + 0# * 0# ≈ e² x
  pp-eq x = trans {expansion x * expansion x + 0# * 0#} {expansion x * expansion x + 0#} {e² x}
    (+-cong {expansion x * expansion x} {expansion x * expansion x} {0# * 0#} {0#} refl (zeroˡ 0#)) (+-identityʳ (expansion x * expansion x))

  nn-eq : ∀ x → expansion x * 0# + 0# * expansion x ≈ 0#
  nn-eq x = trans {expansion x * 0# + 0# * expansion x} {0# + 0#} {0#}
    (+-cong {expansion x * 0#} {0#} {0# * expansion x} {0#} (zeroʳ (expansion x)) (zeroˡ (expansion x))) (+-identityˡ 0#)

  fh : Bnd half
  fh = 1 , ≤-trans half≤1 (≤-reflexive (sym (+-identityʳ 1#)))

  fm : Bnd m
  fm = 1 , ≤-trans m≤1 (≤-reflexive (sym (+-identityʳ 1#)))

  abstract
    -- the binary expansion as a signed function: positive part `expansion`, negative part `0`
    u : SF fairCoin
    u = record
      { f⁺ = expansion ; f⁻ = λ _ → 0#
      ; f⁺-meas = LS Fun-expansion ; f⁻-meas = Meas-const 0#
      ; f⁺-int = 1 , ≤-trans (≤-reflexive jpos) (≤-trans half≤1 (≤-reflexive (sym (+-identityʳ 1#))))
      ; f⁻-int = 0 , ≤-reflexive jneg
      }

    u-bdd : Bdd u
    u-bdd = 1 , λ x → ≤-trans (expansion≤1 x) (≤-reflexive (sym (+-identityʳ 1#))) , OmegaSemiring.0-least A

    Eu : E u ≃ ι fh
    Eu = E-ι u {half} fh jpos jneg

    jpp : J fairCoin (f⁺ (u *SF u [ u-bdd ])) (f⁺-meas (u *SF u [ u-bdd ])) ≈ m
    jpp = trans (J-cong fairCoin (f⁺-meas (u *SF u [ u-bdd ])) Meas-e² pp-eq)
            (trans (J-irrel fairCoin Meas-e² (LS Fun-e²)) (J-fun fairCoin Fun-e²))

    jnn : J fairCoin (f⁻ (u *SF u [ u-bdd ])) (f⁻-meas (u *SF u [ u-bdd ])) ≈ 0#
    jnn = trans (J-cong fairCoin (f⁻-meas (u *SF u [ u-bdd ])) (Meas-const 0#) nn-eq) jneg

    Euu : E (u *SF u [ u-bdd ]) ≃ ι fm
    Euu = E-ι (u *SF u [ u-bdd ]) fm jpp jnn

  uu : SF fairCoin
  uu = u *SF u [ u-bdd ]

  varU : Sg
  varU = Var {fairCoin} pm u u-bdd

  vf : varU ≃ E uu +S (-S (E u *S E u))
  vf = var-formula {fairCoin} pm u u-bdd

  -- E u = ½ and E[u²] = ⅓, as signed values

  mean-u : E u +S E u ≃ 1S
  mean-u = ≃-trans {E u +S E u} {ι fh +S ι fh} {1S} (+S-cong {E u} {ι fh} {E u} {ι fh} Eu Eu)
    (≃-trans {ι fh +S ι fh} {ι f2h} {1S} (≃-sym {ι f2h} {ι fh +S ι fh} (ι-+ fh fh))
      (ι-cong {half + half} {1#} f2h (SubSemiring.Is-1 finite) hh))
    where f2h = SubSemiring.Is-+ finite fh fh

  moment-u : (E uu +S E uu) +S E uu ≃ 1S
  moment-u = ≃-trans {(E uu +S E uu) +S E uu} {(ι fm +S ι fm) +S ι fm} {1S}
      (+S-cong {E uu +S E uu} {ι fm +S ι fm} {E uu} {ι fm} (+S-cong {E uu} {ι fm} {E uu} {ι fm} Euu Euu) Euu)
    (≃-trans {(ι fm +S ι fm) +S ι fm} {ι f3m} {1S}
      (≃-trans {(ι fm +S ι fm) +S ι fm} {ι f2m +S ι fm} {ι f3m}
        (+S-cong {ι fm +S ι fm} {ι f2m} {ι fm} {ι fm} (≃-sym {ι f2m} {ι fm +S ι fm} (ι-+ fm fm)) ≃-refl)
        (≃-sym {ι f3m} {ι f2m +S ι fm} (ι-+ f2m fm)))
      (ι-cong {(m + m) + m} {1#} f3m (SubSemiring.Is-1 finite) second-moment))
    where
      f2m = SubSemiring.Is-+ finite fm fm
      f3m = SubSemiring.Is-+ finite f2m fm

  var-gen : ∀ (V M μ : Sg) → V ≃ M +S (-S (μ *S μ)) → (M +S M) +S M ≃ 1S → μ +S μ ≃ 1S → x12 V ≃ 1S
  var-gen V M μ e mm mu = ≃-trans {x12 V} {x12 (M +S (-S (μ *S μ)))} {1S} (x12-cong {V} {M +S (-S (μ *S μ))} e) (var-arith M μ mm mu)

  -- Var u = 1/12: twelve copies add up to one
  variance : x12 varU ≃ 1S
  variance = var-gen varU (E uu) (E u) vf moment-u mean-u
