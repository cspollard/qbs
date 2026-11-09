{-# OPTIONS --safe --without-K #-}

-- Expectations of *integrable* (possibly unbounded) signed statistics under a measure of the monad
-- (`Continuous/Monad`), extending `Inference/ExpectationResp` beyond bounded tests.
--
--   * `ITest p`: a pair of parts `pos neg : X ⇒ CutQ` whose pulled-back integrals `J (m p) (part ∘ α p)` are finite (`Bnd`);
--     `E-atᴵ p g` is the signed integral `SignedIntegral.E` of the pulled-back pair.  A bounded `STest` is an `ITest p` for every
--     `p` (`fromSTest`) and `E-atᴵ` agrees with `E-at` (`E-atᴵ-fromSTest`).
--   * `J-resp∞`: if `p ≈ᵖ q` then `J (m p) (h ∘ α p) ≈ J (m q) (h ∘ α q)` for every `h : X ⇒ CutQ`, with both sides possibly
--     infinite.  `J` is the supremum over `k` of `2ᵏ ∫ tr k ∘ h` (`Iinf`, `Analysis/Unbounded`; `J-def` in `Analysis/Lebesgue`),
--     and each truncation `tr k ∘ h` is a [0,1]-valued test (`truncHom`), to which `p ≈ᵖ q` applies.
--   * hence integrability transfers along `≈ᵖ` (`transportI`), and `E-respᴵ : p ≈ᵖ q → E-atᴵ p g ≃ E-atᴵ q (transportI {p = p} {q = q} e g)`.
--   * `E-atᴵ-η` (against `ηPre x` the value `valI x g`) and `E-atᴵ-map` (`E-atᴵ (mapPre f p) g ≃ E-atᴵ p (precompI f p g)`).
--   * linearity: `E-atᴵ p (g +I h) ≃ E-atᴵ p g +S E-atᴵ p h`, `-I`, and `scaleI c`, from `E-+`, `E-neg`, `E-scale`.
module QBS.Inference.ExpectationInt where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.Expectation as EX

module ExpectationInt (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-irrel; J-def; tr; tr-≤1; tr-cong; FunInf-Meas; Iinf; Iseq; Iseq-inc)
  open Integration A using (probClass)
  open OmegaSemiring A using (_≈_; ⨆-cong; *-cong; +-cong; 0#; refl; sym; trans)
  open Bounded A using (Sg; Bnd; _≃_; mk≃; ≃-refl; ≃-trans; _+S_; _*S_; -S_; finite; _−_[_,_])
  open SignedIntegral (lemOf lem₁) using (SF; E; E-cong; E-+; E-neg; E-scale; _+SF_; -SF_; scaleSF; J-const)
  open BoundedSignedTests (lemOf lem₁) using (CutQ; STest; pullback; J-bounded)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; _≈ᵖ_; ∫; mapPre; ηPre)
  open Pre
  open ER.ExpectationResp lem₁ using (E-at)
  open QBS using (∣_∣)
  open EX.Expectation lem₁ using (addH; mulH)
  open SF

  ----------------------------------------------------------------------------
  -- integrable tests

  record ITest {X : QBS S} (p : Pre X) : Set₁ where
    field
      pos neg : Hom S X CutQ
      pos-int : Bnd (J (m p) (λ r → Hom.map pos ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random pos (α-random p)))
      neg-int : Bnd (J (m p) (λ r → Hom.map neg ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random neg (α-random p)))
  open ITest

  -- the pulled-back signed function
  toSF : ∀ {X : QBS S} {p : Pre X} → ITest p → SF (m p)
  toSF {p = p} g = record
    { f⁺ = λ r → Hom.map (pos g) ⟨$⟩ (α p ⟨$⟩ r) ; f⁻ = λ r → Hom.map (neg g) ⟨$⟩ (α p ⟨$⟩ r)
    ; f⁺-meas = Hom.map-random (pos g) (α-random p) ; f⁻-meas = Hom.map-random (neg g) (α-random p)
    ; f⁺-int = pos-int g ; f⁻-int = neg-int g }

  E-atᴵ : ∀ {X : QBS S} (p : Pre X) → ITest p → Sg
  E-atᴵ p g = E (toSF g)

  -- bounded tests are integrable, for every measure
  fromSTest : ∀ {X : QBS S} (p : Pre X) → STest X → ITest p
  fromSTest p g = record
    { pos = STest.pos g ; neg = STest.neg g
    ; pos-int = J-bounded (ok p) (Hom.map-random (STest.pos g) (α-random p)) (STest.bound g) (λ r → STest.pos-bdd g (α p ⟨$⟩ r))
    ; neg-int = J-bounded (ok p) (Hom.map-random (STest.neg g) (α-random p)) (STest.bound g) (λ r → STest.neg-bdd g (α p ⟨$⟩ r)) }

  E-atᴵ-fromSTest : ∀ {X : QBS S} (p : Pre X) (g : STest X) → E-atᴵ p (fromSTest p g) ≃ E-at p g
  E-atᴵ-fromSTest p g = ≃-refl

  ----------------------------------------------------------------------------
  -- truncations are [0,1]-valued tests

  truncHom : ∀ {X : QBS S} → Hom S X CutQ → ℕ → Hom S X AQ
  truncHom {X} h k = record
    { map = record
        { to = λ x → tr k (Hom.map h ⟨$⟩ x) , tr-≤1 k (Hom.map h ⟨$⟩ x)
        ; cong = λ e → tr-cong k (Func.cong (Hom.map h) e) }
    ; map-random = λ {β} rβ → FunInf-Meas (Hom.map-random h rβ) k
    }

  -- equal measures give equal (possibly infinite) integrals
  J-resp∞ : ∀ {X : QBS S} {p q : Pre X} → p ≈ᵖ q → (h : Hom S X CutQ) →
    J (m p) (λ r → Hom.map h ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random h (α-random p)) ≈
      J (m q) (λ r → Hom.map h ⟨$⟩ (α q ⟨$⟩ r)) (Hom.map-random h (α-random q))
  J-resp∞ {X} {p} {q} e h = trans (J-def (m p) (Hom.map-random h (α-random p)))
    (trans (⨆-cong (Iseq-inc (m p) _ (FunInf-Meas (Hom.map-random h (α-random p))))
                   (Iseq-inc (m q) _ (FunInf-Meas (Hom.map-random h (α-random q))))
                   (λ k → *-cong refl (e (truncHom h k))))
           (sym (J-def (m q) (Hom.map-random h (α-random q)))))

  -- integrability transfers
  transportI : ∀ {X : QBS S} {p q : Pre X} → p ≈ᵖ q → ITest p → ITest q
  transportI {p = p} {q = q} e g = record
    { pos = pos g ; neg = neg g
    ; pos-int = SubSemiring.Is-resp finite (J-resp∞ {p = p} {q = q} e (pos g)) (pos-int g)
    ; neg-int = SubSemiring.Is-resp finite (J-resp∞ {p = p} {q = q} e (neg g)) (neg-int g) }

  E-respᴵ : ∀ {X : QBS S} {p q : Pre X} (e : p ≈ᵖ q) (g : ITest p) → E-atᴵ p g ≃ E-atᴵ q (transportI {p = p} {q = q} e g)
  E-respᴵ {p = p} {q} e g = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong (+-cong (J-resp∞ {p = p} {q = q} e (pos g)) (sym (J-resp∞ {p = p} {q = q} e (neg g)))) refl)

  ----------------------------------------------------------------------------
  -- linearity

  infixl 6 _+I_
  _+I_ : ∀ {X : QBS S} {p : Pre X} → ITest p → ITest p → ITest p
  g +I h = record
    { pos = addH (pos g) (pos h) ; neg = addH (neg g) (neg h)
    ; pos-int = f⁺-int (toSF g +SF toSF h) ; neg-int = f⁻-int (toSF g +SF toSF h) }

  E-atᴵ-+ : ∀ {X : QBS S} (p : Pre X) (g h : ITest p) → E-atᴵ p (g +I h) ≃ E-atᴵ p g +S E-atᴵ p h
  E-atᴵ-+ p g h = ≃-trans (E-cong {f = toSF (g +I h)} {g = toSF g +SF toSF h} (λ x → refl)) (E-+ (toSF g) (toSF h))

  -I_ : ∀ {X : QBS S} {p : Pre X} → ITest p → ITest p
  -I g = record { pos = neg g ; neg = pos g ; pos-int = neg-int g ; neg-int = pos-int g }

  E-atᴵ-neg : ∀ {X : QBS S} (p : Pre X) (g : ITest p) → E-atᴵ p (-I g) ≃ -S (E-atᴵ p g)
  E-atᴵ-neg p g = E-neg (toSF g)

  scaleI : ∀ {X : QBS S} {p : Pre X} → Sg → ITest p → ITest p
  scaleI c g = record
    { pos = addH (mulH (Sg.pos c) (pos g)) (mulH (Sg.neg c) (neg g))
    ; neg = addH (mulH (Sg.pos c) (neg g)) (mulH (Sg.neg c) (pos g))
    ; pos-int = f⁺-int (scaleSF c (toSF g)) ; neg-int = f⁻-int (scaleSF c (toSF g)) }

  E-atᴵ-scale : ∀ {X : QBS S} (p : Pre X) (c : Sg) (g : ITest p) → E-atᴵ p (scaleI c g) ≃ c *S E-atᴵ p g
  E-atᴵ-scale p c g = ≃-trans (E-cong {f = toSF (scaleI c g)} {g = scaleSF c (toSF g)} (λ x → refl)) (E-scale c (toSF g))

  ----------------------------------------------------------------------------
  -- the unit and the functoriality

  -- the integral of a part against `ηPre x` is its value at `x`
  J-η : ∀ {X : QBS S} (x : ∣ X ∣) (h : Hom S X CutQ) →
    J (m (ηPre {X} x)) (λ r → Hom.map h ⟨$⟩ (α (ηPre {X} x) ⟨$⟩ r)) (Hom.map-random h (α-random (ηPre {X} x))) ≈ Hom.map h ⟨$⟩ x
  J-η {X} x h = trans (J-irrel _ _ _) (J-const (ok (ηPre {X} x)) (Hom.map h ⟨$⟩ x))

  -- against `ηPre x`, an integrable test has the value at `x` (finite, as the integral of a constant)
  valI : ∀ {X : QBS S} (x : ∣ X ∣) → ITest (ηPre {X} x) → Sg
  valI {X} x g = (Hom.map (pos g) ⟨$⟩ x) − (Hom.map (neg g) ⟨$⟩ x) [ b⁺ , b⁻ ]
    where
    b⁺ = SubSemiring.Is-resp finite (J-η {X} x (pos g)) (pos-int g)
    b⁻ = SubSemiring.Is-resp finite (J-η {X} x (neg g)) (neg-int g)

  E-atᴵ-η : ∀ {X : QBS S} (x : ∣ X ∣) (g : ITest (ηPre {X} x)) → E-atᴵ (ηPre {X} x) g ≃ valI x g
  E-atᴵ-η {X} x g = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong (+-cong (J-η {X} x (pos g)) (sym (J-η {X} x (neg g)))) refl)

  -- precomposition with a morphism
  precompI : ∀ {X Y : QBS S} (f : Hom S Y X) (p : Pre Y) → ITest (mapPre f p) → ITest p
  precompI f p g = record
    { pos = _∘H_ S (pos g) f ; neg = _∘H_ S (neg g) f
    ; pos-int = SubSemiring.Is-resp finite (J-irrel _ _ _) (pos-int g)
    ; neg-int = SubSemiring.Is-resp finite (J-irrel _ _ _) (neg-int g) }

  E-atᴵ-map : ∀ {X Y : QBS S} (f : Hom S Y X) (p : Pre Y) (g : ITest (mapPre f p)) →
    E-atᴵ (mapPre f p) g ≃ E-atᴵ p (precompI f p g)
  E-atᴵ-map f p g = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong (+-cong (J-irrel _ _ _) (sym (J-irrel _ _ _))) refl)
