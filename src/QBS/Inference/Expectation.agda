{-# OPTIONS --safe --without-K #-}

-- Calculating with the expectation `E-at` of a bounded signed statistic (`Inference/ExpectationResp`):
--
--   * the algebra of signed tests: sum `_+T_`, negation `-T_`, scaling by a signed constant `scaleT c`, constants
--     `constT c`, and precomposition `precompT f` with a morphism, all built from the corresponding operations on the
--     `Hom X CutQ` parts (`addH`, `mulH`, `constH`);
--   * `E-at-η`: against the unit `ηPre x` the expectation is the value `valT g x` of the test at `x`;
--   * `E-at-map`: `E-at (mapPre f p) g ≃ E-at p (precompT f g)`;
--   * linearity: `E-at p (g +T h) ≃ E-at p g +S E-at p h`, `E-at p (-T g) ≃ -S E-at p g`,
--     `E-at p (scaleT c g) ≃ c *S E-at p g`, and `E-at p (constT c) ≃ c`;
--   * the tower law `E-at-join : E-at (joinPre P) g ≃ E-at P (expT g)`, where `expT g : STest (TQ X)` is `q ↦ E-at q g`
--     (`E-at-expT`).  Its parts are `q ↦ 2ᴺ · ∫ q (2⁻ᴺ f)` (`expH`), measurable in `q` by `∫ᶠ`, and the rescaling of
--     `Inference/ExpectationResp` (`∫-scale`) reduces everything to `∫-join`.
--
-- For the algebraic laws the pulled-back signed function (`pullback`, `Continuous/SignedTests`) is equal *pointwise and
-- definitionally* to the corresponding operation of `Analysis/SignedIntegral` (`+SF`, `-SF_`, `scaleSF`, `constSF`) applied
-- to the pull-backs of the arguments, so `E-cong` plus the linearity of `E` there is all that is needed; no integral
-- argument is repeated.
module QBS.Inference.Expectation where

open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Nat.Properties using (m≤m+n; m≤n+m)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)
import QBS.Inference.ExpectationResp as ER

module Expectation (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-irrel; J-fun; J-scale)
  open Integration A using (probClass)
  open OmegaSemiring A renaming (Carrier to ∣A∣) using (_≈_; _≤_; _*_; _+_; 0#; refl; +-mono; *-mono; ≤-trans; ≤-reflexive;
    +-cong; *-cong; sym; trans; *-identityʳ)
  open Meas (lemOf lem₁) using (Meas-⊕; Meas-⊗; Meas-const)
  open LevelSets (lemOf lem₁) using (LS)
  open Bounded A using (Sg; nat; nat-+; _≃_; mk≃; ≃-trans; _+S_; _*S_; -S_; finite; _−_[_,_])
  open Sg
  open SignedIntegral (lemOf lem₁) using (SF; E; E-cong; E-+; E-neg; E-scale; E-const; constSF; _+SF_; -SF_; scaleSF)
  open SignedTests (lemOf lem₁) using (CutQ; STest; pullback)
  open Continuous A (lemOf lem₁) probClass using (Pre; mapPre; ηPre; TQ; ∫; ∫ᶠ; joinPre; ∫-join)
  open Pre
  open QBS using (∣_∣)
  open ER.ExpectationResp lem₁ using (E-at; scaleHom; ∫-scale; hp-recover)
  open Arch (lowerRealsArch (lemOf lem₁)) using () renaming (half to halfA; half+half to hh)
  open BoundedCancel A halfA hh using (nat-mono)

  ----------------------------------------------------------------------------
  -- operations on the parts `Hom X CutQ`

  constH : ∀ {X : QBS S} → ∣A∣ → Hom S X CutQ
  constH c = record { map = constₛ c ; map-random = λ _ → Meas-const c }

  addH : ∀ {X : QBS S} → Hom S X CutQ → Hom S X CutQ → Hom S X CutQ
  addH f g = record
    { map = record
        { to = λ x → (Hom.map f ⟨$⟩ x) + (Hom.map g ⟨$⟩ x)
        ; cong = λ e → +-cong (Func.cong (Hom.map f) e) (Func.cong (Hom.map g) e) }
    ; map-random = λ {β} r → Meas-⊕ {λ s → Hom.map f ⟨$⟩ (β ⟨$⟩ s)} {λ s → Hom.map g ⟨$⟩ (β ⟨$⟩ s)}
        (Hom.map-random f r) (Hom.map-random g r)
    }

  mulH : ∀ {X : QBS S} → ∣A∣ → Hom S X CutQ → Hom S X CutQ
  mulH c f = record
    { map = record
        { to = λ x → c * (Hom.map f ⟨$⟩ x)
        ; cong = λ e → *-cong refl (Func.cong (Hom.map f) e) }
    ; map-random = λ {β} r → Meas-⊗ {λ _ → c} {λ s → Hom.map f ⟨$⟩ (β ⟨$⟩ s)} (Meas-const c) (Hom.map-random f r)
    }

  ----------------------------------------------------------------------------
  -- the algebra of signed tests

  -- the value of a signed test at a point
  valT : ∀ {X : QBS S} → STest X → ∣ X ∣ → Sg
  valT g x = (Hom.map (STest.pos g) ⟨$⟩ x) − (Hom.map (STest.neg g) ⟨$⟩ x)
    [ (STest.bound g , STest.pos-bdd g x) , (STest.bound g , STest.neg-bdd g x) ]

  infixl 6 _+T_
  _+T_ : ∀ {X : QBS S} → STest X → STest X → STest X
  g +T h = record
    { pos = addH (STest.pos g) (STest.pos h)
    ; neg = addH (STest.neg g) (STest.neg h)
    ; bound = STest.bound g ℕ.+ STest.bound h
    ; pos-bdd = λ x → ≤-trans (+-mono (STest.pos-bdd g x) (STest.pos-bdd h x)) nb
    ; neg-bdd = λ x → ≤-trans (+-mono (STest.neg-bdd g x) (STest.neg-bdd h x)) nb
    }
    where nb = ≤-reflexive (sym (nat-+ (STest.bound g) (STest.bound h)))

  -T_ : ∀ {X : QBS S} → STest X → STest X
  -T g = record { pos = STest.neg g ; neg = STest.pos g ; bound = STest.bound g
                ; pos-bdd = STest.neg-bdd g ; neg-bdd = STest.pos-bdd g }

  constT : ∀ {X : QBS S} → Sg → STest X
  constT c = record
    { pos = constH (pos c) ; neg = constH (neg c) ; bound = a ℕ.+ b
    ; pos-bdd = λ _ → ≤-trans (proj₂ (pos-fin c)) (nat-mono (m≤m+n a b))
    ; neg-bdd = λ _ → ≤-trans (proj₂ (neg-fin c)) (nat-mono (m≤n+m b a)) }
    where
    a = proj₁ (pos-fin c)
    b = proj₁ (neg-fin c)

  -- scaling by a signed constant: (c⁺ − c⁻)(g⁺ − g⁻)
  scaleT : ∀ {X : QBS S} → Sg → STest X → STest X
  scaleT c g = record
    { pos = addH (mulH (pos c) (STest.pos g)) (mulH (neg c) (STest.neg g))
    ; neg = addH (mulH (pos c) (STest.neg g)) (mulH (neg c) (STest.pos g))
    ; bound = a ℕ.* N ℕ.+ b ℕ.* N
    ; pos-bdd = λ x → proj₂ (SubSemiring.Is-+ finite (SubSemiring.Is-* finite (pos-fin c) (N , STest.pos-bdd g x))
                                                   (SubSemiring.Is-* finite (neg-fin c) (N , STest.neg-bdd g x)))
    ; neg-bdd = λ x → proj₂ (SubSemiring.Is-+ finite (SubSemiring.Is-* finite (pos-fin c) (N , STest.neg-bdd g x))
                                                   (SubSemiring.Is-* finite (neg-fin c) (N , STest.pos-bdd g x)))
    }
    where
    N = STest.bound g
    a = proj₁ (pos-fin c)
    b = proj₁ (neg-fin c)

  -- precomposition with a morphism
  precompT : ∀ {X Y : QBS S} → Hom S Y X → STest X → STest Y
  precompT f g = record
    { pos = _∘H_ S (STest.pos g) f ; neg = _∘H_ S (STest.neg g) f ; bound = STest.bound g
    ; pos-bdd = λ y → STest.pos-bdd g (Hom.map f ⟨$⟩ y) ; neg-bdd = λ y → STest.neg-bdd g (Hom.map f ⟨$⟩ y) }

  ----------------------------------------------------------------------------
  -- calculating

  -- the pulled-back signed function
  pl : ∀ {X : QBS S} (p : Pre X) → STest X → SF (m p)
  pl p g = proj₁ (pullback g (α-random p) (m p) (ok p))

  E-at-+ : ∀ {X : QBS S} (p : Pre X) (g h : STest X) → E-at p (g +T h) ≃ E-at p g +S E-at p h
  E-at-+ p g h = ≃-trans (E-cong {f = pl p (g +T h)} {g = pl p g +SF pl p h} (λ x → refl)) (E-+ (pl p g) (pl p h))

  E-at-neg : ∀ {X : QBS S} (p : Pre X) (g : STest X) → E-at p (-T g) ≃ -S (E-at p g)
  E-at-neg p g = ≃-trans (E-cong {f = pl p (-T g)} {g = -SF pl p g} (λ x → refl)) (E-neg (pl p g))

  E-at-scale : ∀ {X : QBS S} (p : Pre X) (c : Sg) (g : STest X) → E-at p (scaleT c g) ≃ c *S E-at p g
  E-at-scale p c g = ≃-trans (E-cong {f = pl p (scaleT c g)} {g = scaleSF c (pl p g)} (λ x → refl)) (E-scale c (pl p g))

  E-at-const : ∀ {X : QBS S} (p : Pre X) (c : Sg) → E-at p (constT c) ≃ c
  E-at-const p c = ≃-trans (E-cong {f = pl p (constT c)} {g = constSF (ok p) c} (λ x → refl)) (E-const (ok p) c)

  E-at-map : ∀ {X Y : QBS S} (f : Hom S Y X) (p : Pre Y) (g : STest X) → E-at (mapPre f p) g ≃ E-at p (precompT f g)
  E-at-map f p g = E-cong {f = pl (mapPre f p) g} {g = pl p (precompT f g)} (λ x → refl)

  E-at-η : ∀ {X : QBS S} (x : ∣ X ∣) (g : STest X) → E-at (ηPre {X} x) g ≃ valT g x
  E-at-η {X} x g = ≃-trans (E-cong {f = pl (ηPre x) g} {g = constSF o (valT g x)} (λ _ → refl)) (E-const o (valT g x))
    where o = ok (ηPre {X} x)

  ----------------------------------------------------------------------------
  -- the tower law

  -- the part f (bounded by N) as a function of the measure: q ↦ 2ᴺ · ∫ q (2⁻ᴺ f), which is ∫ f dq (`∫-scale`); the
  -- integral of a [0,1]-valued test is measurable in the measure by `∫ᶠ`
  expH : ∀ {X : QBS S} (f : Hom S X CutQ) (N : ℕ) (b : ∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) → Hom S (TQ X) CutQ
  expH {X} f N b = record
    { map = record
        { to = λ q → nat (2 ℕ.^ N) * ∫ q hs
        ; cong = λ e → *-cong refl (e hs) }
    ; map-random = λ {β} w → Meas-⊗ {λ _ → nat (2 ℕ.^ N)} {λ s → proj₁ (Hom.map (∫ᶠ hs) ⟨$⟩ (β ⟨$⟩ s))}
        (Meas-const (nat (2 ℕ.^ N))) (LS (Hom.map-random (∫ᶠ hs) {β} w))
    }
    where hs = scaleHom f N b

  -- the integral of f against q is the value of `expH f` at q
  J-exp : ∀ {X : QBS S} (q : Pre X) (f : Hom S X CutQ) (N : ℕ) (b : ∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) →
    J (m q) (λ r → Hom.map f ⟨$⟩ (α q ⟨$⟩ r)) (Hom.map-random f (α-random q)) ≈ nat (2 ℕ.^ N) * ∫ q (scaleHom f N b)
  J-exp q f N b = sym (trans (*-cong refl (∫-scale q f N b)) (hp-recover N _))

  -- its integral against a measure P of measures is the integral of f against the join
  tower-part : ∀ {X : QBS S} (P : Pre (TQ X)) (f : Hom S X CutQ) (N : ℕ) (b : ∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) →
    J (m (joinPre P)) (λ r → Hom.map f ⟨$⟩ (α (joinPre P) ⟨$⟩ r)) (Hom.map-random f (α-random (joinPre P))) ≈
      J (m P) (λ r → Hom.map (expH f N b) ⟨$⟩ (α P ⟨$⟩ r)) (Hom.map-random (expH f N b) {α P} (α-random P))
  tower-part {X} P f N b = trans (J-exp (joinPre P) f N b)
    (trans (*-cong refl (∫-join P hs))
      (trans (*-cong refl (sym (J-fun (m P) F)))
        (trans (sym (J-scale (m P) (nat (2 ℕ.^ N)) {_} (LS F))) (J-irrel (m P) _ _))))
    where
    hs = scaleHom f N b
    F = Hom.map-random (∫ᶠ hs) {α P} (α-random P)

  -- `q ↦ E-at q g` as a signed test on measures
  expT : ∀ {X : QBS S} → STest X → STest (TQ X)
  expT {X} g = record
    { pos = expH (STest.pos g) N (STest.pos-bdd g) ; neg = expH (STest.neg g) N (STest.neg-bdd g) ; bound = 2 ℕ.^ N
    ; pos-bdd = λ q → ≤-trans (*-mono (nat (2 ℕ.^ N)) (proj₂ (Hom.map (∫ᶠ (scaleHom (STest.pos g) N (STest.pos-bdd g))) ⟨$⟩ q)))
        (≤-reflexive (*-identityʳ (nat (2 ℕ.^ N))))
    ; neg-bdd = λ q → ≤-trans (*-mono (nat (2 ℕ.^ N)) (proj₂ (Hom.map (∫ᶠ (scaleHom (STest.neg g) N (STest.neg-bdd g))) ⟨$⟩ q)))
        (≤-reflexive (*-identityʳ (nat (2 ℕ.^ N)))) }
    where N = STest.bound g

  -- the tower law
  E-at-join : ∀ {X : QBS S} (P : Pre (TQ X)) (g : STest X) → E-at (joinPre P) g ≃ E-at P (expT g)
  E-at-join P g = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong (+-cong (tower-part P (STest.pos g) N (STest.pos-bdd g)) (sym (tower-part P (STest.neg g) N (STest.neg-bdd g)))) refl)
    where N = STest.bound g

  -- `expT g` computes the expectation under each measure
  E-at-expT : ∀ {X : QBS S} (q : Pre X) (g : STest X) → valT (expT g) q ≃ E-at q g
  E-at-expT q g = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong (+-cong (sym (J-exp q (STest.pos g) N (STest.pos-bdd g))) (J-exp q (STest.neg g) N (STest.neg-bdd g))) refl)
    where N = STest.bound g
