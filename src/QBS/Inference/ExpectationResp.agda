{-# OPTIONS --safe --without-K #-}

-- `E-at` respects the equality of measures of the monad (`Continuous/Monad`): if `p ≈ᵖ q` (all integrals of [0,1]-valued
-- tests agree) then the expectation of a bounded signed statistic is the same under `p` and `q`.
--
-- The proof rescales instead of truncating.  If both parts of the statistic are bounded by `N ≤ 2ᵏ`, then `hp k · part`
-- is a [0,1]-valued test (`hp k = 2⁻ᵏ`, `Analysis/Archimedean`), so `p ≈ᵖ q` applies to it directly, and `J-scale`
-- (`Analysis/Lebesgue`) and cancellation of `hp k` (`hp k · 2ᵏ = 1`) recover the integrals of the parts.  No monotone
-- convergence is needed.
module QBS.Inference.ExpectationResp where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Nat.Properties using (n≤1+n) renaming (≤-trans to ≤ₙ-trans)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_,_; proj₁)
open import Function.Bundles using (Func; _⟨$⟩_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.MeasFun using (module MeasFun)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Continuous.Sample using (S; module UnitInterval)
open import QBS.Continuous.Monad
open import QBS.Continuous.SignedTests using (module SignedTests)

module ExpectationResp (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A; J; J-irrel; J-fun; J-scale)
  open Integration A using (I; probClass)
  open OmegaSemiring A renaming (setoid to Aˢ) using (_≈_; _≤_; _*_; _+_; 0#; 1#; refl; sym; trans; *-cong; +-cong;
    *-assoc; *-comm; *-identityˡ; +-identityʳ; 0-least; *-mono; distribˡ; distribʳ; ≤-trans; ≤-reflexive)
  open Meas (lemOf lem₁) using (Meas-⊗; Meas-const)
  open MeasFun (lemOf lem₁) using (Meas→Fun)
  open LevelSets (lemOf lem₁) using (LS)
  open Bounded A using (Sg; nat; nat-+; _≃_; mk≃)
  open SignedIntegral (lemOf lem₁) using (E)
  open SignedTests (lemOf lem₁) using (CutQ; STest; pullback)
  open UnitInterval A using (AQ)
  open Continuous A (lemOf lem₁) probClass using (Pre; _≈ᵖ_; ∫)
  open Pre

  -- the expectation of a bounded signed statistic under a measure of the monad
  E-at : ∀ {X} → Pre X → STest X → Sg
  E-at p g = E (proj₁ (pullback g (α-random p) (m p) (ok p)))
  open Arch (lowerRealsArch (lemOf lem₁)) using (hp; hp-zero; hp-double) renaming (half to halfA; half+half to hh)
  open BoundedCancel A halfA hh using (2^-suc; suc≤2^; nat-mono)

  ----------------------------------------------------------------------------
  -- arithmetic: rescaling by 2⁻ᵏ

  -- 2⁻ᵏ · 2ᵏ = 1
  hp-pow2 : ∀ k → hp k * nat (2 ℕ.^ k) ≈ 1#
  hp-pow2 ℕ.zero = trans (*-cong hp-zero (+-identityʳ 1#)) (*-identityˡ 1#)
  hp-pow2 (suc k) = begin
    hp (suc k) * nat (2 ℕ.^ suc k)        ≈⟨ *-cong refl (≡.subst (λ n → nat (2 ℕ.^ suc k) ≈ nat n) (2^-suc k) refl) ⟩
    hp (suc k) * nat (t ℕ.+ t)            ≈⟨ *-cong refl (nat-+ t t) ⟩
    hp (suc k) * (nat t + nat t)          ≈⟨ distribˡ (hp (suc k)) (nat t) (nat t) ⟩
    hp (suc k) * nat t + hp (suc k) * nat t ≈⟨ sym (distribʳ (nat t) (hp (suc k)) (hp (suc k))) ⟩
    (hp (suc k) + hp (suc k)) * nat t     ≈⟨ *-cong (hp-double k) refl ⟩
    hp k * nat t                          ≈⟨ hp-pow2 k ⟩
    1# ∎
    where
    t = 2 ℕ.^ k
    open SetoidReasoning Aˢ

  -- 2ᵏ · (2⁻ᵏ · a) = a
  hp-recover : ∀ k a → nat (2 ℕ.^ k) * (hp k * a) ≈ a
  hp-recover k a = begin
    nat (2 ℕ.^ k) * (hp k * a) ≈⟨ sym (*-assoc (nat (2 ℕ.^ k)) (hp k) a) ⟩
    (nat (2 ℕ.^ k) * hp k) * a ≈⟨ *-cong (*-comm (nat (2 ℕ.^ k)) (hp k)) refl ⟩
    (hp k * nat (2 ℕ.^ k)) * a ≈⟨ *-cong (hp-pow2 k) refl ⟩
    1# * a                    ≈⟨ *-identityˡ a ⟩
    a ∎
    where open SetoidReasoning Aˢ

  -- cancellation of 2⁻ᵏ
  hp-cancel : ∀ k {a b} → hp k * a ≈ hp k * b → a ≈ b
  hp-cancel k {a} {b} e = trans (sym (hp-recover k a)) (trans (*-cong refl e) (hp-recover k b))

  -- a part bounded by N is below 2ᵏ for k = N, so its rescaling is below 1
  hp-bound : ∀ N {a} → a ≤ nat N → hp N * a ≤ 1#
  hp-bound N {a} h = ≤-trans (*-mono (hp N) (≤-trans h (nat-mono (≤ₙ-trans (n≤1+n N) (suc≤2^ N)))))
    (≤-reflexive (hp-pow2 N))

  ----------------------------------------------------------------------------
  -- the rescaled test

  -- the part f of a statistic, bounded by N, rescaled to a [0,1]-valued test
  scaleHom : ∀ {X : QBS S} (f : Hom S X CutQ) (N : ℕ) → (∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) → Hom S X AQ
  scaleHom {X} f N b = record
    { map = record
        { to = λ x → hp N * (Hom.map f ⟨$⟩ x) , hp-bound N (b x)
        ; cong = λ e → *-cong refl (Func.cong (Hom.map f) e) }
    ; map-random = λ {β} rβ → Meas→Fun {λ r → hp N * (Hom.map f ⟨$⟩ (β ⟨$⟩ r))} (λ r → hp-bound N (b (β ⟨$⟩ r)))
        (Meas-⊗ {λ _ → hp N} {λ r → Hom.map f ⟨$⟩ (β ⟨$⟩ r)} (Meas-const (hp N)) (Hom.map-random f rβ))
    }

  -- its integral is the rescaled integral of f
  ∫-scale : ∀ {X : QBS S} (p : Pre X) (f : Hom S X CutQ) (N : ℕ) (b : ∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) →
    ∫ p (scaleHom f N b) ≈
      hp N * J (m p) (λ r → Hom.map f ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random f (α-random p))
  ∫-scale {X} p f N b = trans (sym (J-fun (m p) {h} F)) (trans (J-irrel (m p) (LS F) hm) (J-scale (m p) (hp N) {φ} mφ))
    where
    φ = λ r → Hom.map f ⟨$⟩ (α p ⟨$⟩ r)
    h = λ r → hp N * φ r
    mφ = Hom.map-random f (α-random p)
    hm = Meas-⊗ {λ _ → hp N} {φ} (Meas-const (hp N)) mφ
    F = Hom.map-random (scaleHom f N b) (α-random p)

  -- equal measures give equal integrals of a bounded part
  J-resp : ∀ {X : QBS S} {p q : Pre X} → p ≈ᵖ q → (f : Hom S X CutQ) (N : ℕ) →
    (b : ∀ x → (Hom.map f ⟨$⟩ x) ≤ nat N) →
    J (m p) (λ r → Hom.map f ⟨$⟩ (α p ⟨$⟩ r)) (Hom.map-random f (α-random p)) ≈
      J (m q) (λ r → Hom.map f ⟨$⟩ (α q ⟨$⟩ r)) (Hom.map-random f (α-random q))
  J-resp {X} {p} {q} e f N b =
    hp-cancel N (trans (sym (∫-scale p f N b)) (trans (e (scaleHom f N b)) (∫-scale q f N b)))

  ----------------------------------------------------------------------------
  -- the expectation

  E-resp : ∀ {X : QBS S} {p q : Pre X} → p ≈ᵖ q → (g : STest X) → E-at p g ≃ E-at q g
  E-resp {X} {p} {q} e g = mk≃ 0# (0 , 0-least) (+-cong (+-cong jpos (sym jneg)) refl)
    where
    jpos = J-resp {p = p} {q = q} e (STest.pos g) (STest.bound g) (STest.pos-bdd g)
    jneg = J-resp {p = p} {q = q} e (STest.neg g) (STest.bound g) (STest.neg-bdd g)
