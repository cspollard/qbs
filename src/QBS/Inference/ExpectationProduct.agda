{-# OPTIONS --safe --without-K #-}

-- Independence for products: expectations against the product measure of the continuous probability monad.
--
--   * `f ⊗T g : STest (_×Q_ S X Y)`, the product of two signed tests, with positive part `f⁺g⁺ + f⁻g⁻` and negative part
--     `f⁺g⁻ + f⁻g⁺`; `valT (f ⊗T g) (x , y) ≃ valT f x *S valT g y` (`valT-⊗T`);
--   * `E-at-cong`: tests that agree pointwise up to `≃` have `≃` expectations (`cancel-bnd` of `Analysis/BoundedCancel`
--     turns the `≃` of bounded signed numbers into the pointwise equality of signed functions that `E-cong` takes);
--   * `E-at-σ`: against the strength `σPre (x , q)` (`Continuous/Strong`), `E-at (σPre (x , q)) (f ⊗T g) ≃ valT f x *S E-at q g`;
--   * the product measure `p ⊗ᵖ q = joinPre (mapPre (σH ∘ ⟨id , const q⟩) p)`, and independence
--     `E-at-⊗ : E-at (p ⊗ᵖ q) (f ⊗T g) ≃ E-at p f *S E-at q g`, from the tower law `E-at-join`, `E-at-map`, `E-at-σ`,
--     `E-at-cong` and `E-at-scale` (`Inference/Expectation`).
module QBS.Inference.ExpectationProduct where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Limits using (_×Q_; pairQ)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.Strong using (module Strength)
open import QBS.Continuous.BoundedSignedTests using (module BoundedSignedTests)
import QBS.Inference.ExpectationResp as ER
import QBS.Inference.Expectation as EX

module ExpectationProduct (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣; setoid to Aˢ) using (_≈_; _≤_; _*_; _+_; 0#; refl; sym; trans; +-cong; +-comm;
    *-mono; +-mono; ≤-trans)
  open Meas (lemOf lem₁) using (Meas-⊕; Meas-⊗)
  open Bounded A using (Sg; nat; _≃_; mk≃; ≃-refl; ≃-trans; ≃-sym; _*S_; *S-comm; *S-cong; finite)
  open Sg
  open SignedIntegral (lemOf lem₁) using (E-cong; E-scale; scaleSF)
  open BoundedSignedTests (lemOf lem₁) using (CutQ; STest)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre; TQ; joinPre)
  open Strength A (lemOf lem₁) probClass using (σPre; σH)
  open ER.ExpectationResp lem₁ using (E-at)
  open EX.Expectation lem₁ using (valT; scaleT; precompT; expT; pl; E-at-scale; E-at-map; E-at-join; E-at-expT)
  open Arch (lowerRealsArch (lemOf lem₁)) using () renaming (half to halfA; half+half to hh)
  open BoundedCancel A halfA hh using (cancel-bnd)
  open Pre using (α)
  open QBS using (∣_∣)

  ----------------------------------------------------------------------------
  -- the product of two tests

  -- a part of the product: u(x) v(y) + u'(x) v'(y)
  prodH : ∀ {X Y : QBS S} (u u′ : Hom S X CutQ) (v v′ : Hom S Y CutQ) → Hom S (_×Q_ S X Y) CutQ
  prodH u u′ v v′ = record
    { map = record
        { to = λ { (x , y) → (Hom.map u ⟨$⟩ x) * (Hom.map v ⟨$⟩ y) + (Hom.map u′ ⟨$⟩ x) * (Hom.map v′ ⟨$⟩ y) }
        ; cong = λ { (ex , ey) → +-cong (*-cong′ (Func.cong (Hom.map u) ex) (Func.cong (Hom.map v) ey))
                                        (*-cong′ (Func.cong (Hom.map u′) ex) (Func.cong (Hom.map v′) ey)) } }
    ; map-random = λ { {β} (rx , ry) → Meas-⊕
        (Meas-⊗ (Hom.map-random u rx) (Hom.map-random v ry))
        (Meas-⊗ (Hom.map-random u′ rx) (Hom.map-random v′ ry)) }
    }
    where *-cong′ = OmegaSemiring.*-cong A

  infixl 7 _⊗T_
  _⊗T_ : ∀ {X Y : QBS S} → STest X → STest Y → STest (_×Q_ S X Y)
  f ⊗T g = record
    { pos = prodH (STest.pos f) (STest.neg f) (STest.pos g) (STest.neg g)
    ; neg = prodH (STest.pos f) (STest.neg f) (STest.neg g) (STest.pos g)
    ; bound = n ℕ.+ n
    ; pos-bdd = λ { (x , y) → proj₂ (bd (STest.pos-bdd f x) (STest.pos-bdd g y) (STest.neg-bdd f x) (STest.neg-bdd g y)) }
    ; neg-bdd = λ { (x , y) → proj₂ (bd (STest.pos-bdd f x) (STest.neg-bdd g y) (STest.neg-bdd f x) (STest.pos-bdd g y)) }
    }
    where
    n = STest.bound f ℕ.* STest.bound g
    bd = λ {a b c d} (ha : a ≤ nat (STest.bound f)) (hb : b ≤ nat (STest.bound g))
                (hc : c ≤ nat (STest.bound f)) (hd : d ≤ nat (STest.bound g)) →
      SubSemiring.Is-+ finite (SubSemiring.Is-* finite (STest.bound f , ha) (STest.bound g , hb))
                              (SubSemiring.Is-* finite (STest.bound f , hc) (STest.bound g , hd))

  valT-⊗T : ∀ {X Y : QBS S} (f : STest X) (g : STest Y) (x : ∣ X ∣) (y : ∣ Y ∣) →
    valT (f ⊗T g) (x , y) ≃ valT f x *S valT g y
  valT-⊗T f g x y = ≃-refl

  ----------------------------------------------------------------------------
  -- tests that agree pointwise have the same expectation

  E-at-cong : ∀ {X : QBS S} (p : Pre X) (g h : STest X) → (∀ x → valT g x ≃ valT h x) → E-at p g ≃ E-at p h
  E-at-cong {X} p g h e = E-cong {f = pl p g} {g = pl p h} (λ r → un (e (α p ⟨$⟩ r)))
    where
    un : ∀ {u v : Sg} → u ≃ v → pos u + neg v ≈ pos v + neg u
    un {u} {v} (mk≃ k (N , kb) eq) = cancel-bnd {a = k} (N , kb) (trans (+-comm k _) (trans eq (+-comm _ k)))

  ----------------------------------------------------------------------------
  -- one-sided independence

  E-at-σ : ∀ {X Y : QBS S} (x : ∣ X ∣) (q : Pre Y) (f : STest X) (g : STest Y) →
    E-at (σPre {X} {Y} (x , q)) (f ⊗T g) ≃ valT f x *S E-at q g
  E-at-σ x q f g = ≃-trans (E-cong {f = pl (σPre (x , q)) (f ⊗T g)} {g = scaleSF (valT f x) (pl q g)} (λ r → refl))
    (E-scale (valT f x) (pl q g))

  ----------------------------------------------------------------------------
  -- the product measure and independence

  -- x ↦ σPre (x , q)
  σq : ∀ {X Y : QBS S} → Pre Y → Hom S X (TQ (_×Q_ S X Y))
  σq {X} {Y} q = _∘H_ S (σH X Y) (pairQ S {X} {X} {TQ Y} (idH S)
    (record { map = constₛ q ; map-random = λ {β} _ → QBS.const-random (TQ Y) q }))

  infixl 7 _⊗ᵖ_
  _⊗ᵖ_ : ∀ {X Y : QBS S} → Pre X → Pre Y → Pre (_×Q_ S X Y)
  p ⊗ᵖ q = joinPre (mapPre (σq q) p)

  E-at-⊗ : ∀ {X Y : QBS S} (p : Pre X) (q : Pre Y) (f : STest X) (g : STest Y) →
    E-at (p ⊗ᵖ q) (f ⊗T g) ≃ E-at p f *S E-at q g
  E-at-⊗ {X} {Y} p q f g = ≃-trans (E-at-join (mapPre (σq q) p) F) (≃-trans (E-at-map (σq q) p (expT F))
    (≃-trans (E-at-cong p (precompT (σq q) (expT F)) (scaleT c f) pw) (≃-trans (E-at-scale p c f) (*S-comm c (E-at p f)))))
    where
    F = f ⊗T g
    c = E-at q g
    pw : ∀ x → valT (precompT (σq q) (expT F)) x ≃ valT (scaleT c f) x
    pw x = ≃-trans (E-at-expT (σPre (x , q)) F) (≃-trans (E-at-σ x q f g) (≃-trans (*S-comm (valT f x) c) ≃-refl))
