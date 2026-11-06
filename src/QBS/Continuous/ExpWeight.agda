{-# OPTIONS --safe --without-K #-}

-- Exponential weights of signed values and signed tests (plan 07, item 58; enabler for `Continuous/ExpFamily`).
--   * `expW s = expC s⁺ ⊗ negExp s⁻` in `Cut` (the weight space `WQ`), with `expW-+` and `expW-0`;
--   * `expWT f : Hom S X WQ` for a signed test `f : SgT X`;
--   * `expW-cong` (under `≃`) and `expWT-cong` (under `≐`);
--   * `expW-pos` and `expW-bnd` for bounded `s`;
--   * `log-expW : logS (expW s) ≃ s`, from the log equation `log-expW-eq`.
-- Route: multiplicativity from `ExpLower.Add.exp-add` and `HalfLineNegExp.negExp-add`; congruence by
-- multiplying by `expC (neg s) · expC (neg t) · expC k` and cancelling via `negExp-expC-nat` (`ExpWeightAlg`);
-- log inversion from `LogNeg.UD` and the injectivity `LogNeg.exp-inj`, with `ExpWeightAlg.ud-step`.
module QBS.Continuous.ExpWeight where

open import Algebra.Bundles using (CommutativeSemiring)
open import Algebra.Properties.CommutativeSemigroup using (interchange)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised.Base using (_<_) renaming (_*_ to _*ℚ_; _+_ to _+ℚ_)
open import Function.Bundles using (Func)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.RationalLemmas using (1ℚᵘ; 0<1; 0<½; ½; <-trans; *-pos; inv; *-mono-<-pos; ≃-<ʳ; lt-add)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (Cut; _⊑_; oneC; ⊑-trans; ⊕-inl)
open _⊑_ using (ap)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.ExpLower using (expC; expC-zero; expC-cong; expC-bound; pow3; 0<pow3; 1+≤expC; P-id; pos-inv;
  module Add)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SignedTest using (module SignedTest)
open import QBS.Continuous.SignedLog using (module SignedLog)
open import QBS.Continuous.LogNeg using (½<1; module LogNeg)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.MonusAlg using (module MonusAlg)
open import QBS.Continuous.ExpWeightAlg using (module ExpWeightAlg)

module ExpWeight (lem₁ : LEM₁) where
  private
    lem = lemOf lem₁
    A = Lebesgue.A lem
  open OmegaSemiring A using (_≈_; _*_; _+_; _≤_; 1#; 0#; refl; sym; trans; *-cong; *-identityˡ; +-cong; *-comm;
                              commutativeSemiring; ≤-trans; ≤-reflexive; *-commutativeSemigroup; +-identityʳ)
  open Bounded A using (Sg; _≃_; _+S_; 0S; Bnd; finite; mk≃)
  open SubSemiring finite using (Is-0)
  open Sg
  open NegExp lem using (negExp; negExp-zero; negExp-anti; Meas-negExp; Meas-expC; negExp-expC-nat; negExp≤1)
  open Meas lem using (Meas-⊗)
  open Weights lem using (WQ)
  open SignedTest lem₁ using (SgT; at⁺; at⁻; FinT; _≐_; posT; negT)
  open SignedLog lem₁ using (PosQ; BndQ-mul; PosQ-mul; logS; logP; logN)
  open Exp A using (natE)
  open HalfLineNegExp lem₁ using (negExp-add)
  open LebesgueDyadicAlg lem using (natE≈nat)
  open MonusAlg lem₁ using (rat-bnd)
  open LogNeg lem using (UD; exp-inj)
  open import Relation.Binary.Reasoning.Setoid (OmegaSemiring.setoid A)
  open Hom

  expW : Sg → Cut
  expW s = expC lem (pos s) * negExp (neg s)

  expC-add : ∀ x y → expC lem (x + y) ≈ expC lem x * expC lem y
  expC-add x y = AddE.exp-add
    where module AddE = Add lem x y

  expW-0 : expW 0S ≈ 1#
  expW-0 = trans (*-cong (expC-zero lem) negExp-zero) (*-identityˡ 1#)

  expW-prod-alg : ∀ a b c d → (a * b) * (c * d) ≈ (a * c) * (b * d)
  expW-prod-alg = interchange *-commutativeSemigroup

  expW-+ : ∀ s t → expW (s +S t) ≈ expW s * expW t
  expW-+ s t = trans (*-cong (expC-add (pos s) (pos t)) (negExp-add hn hm hk))
    (expW-prod-alg (expC lem (pos s)) (expC lem (pos t)) (negExp (neg s)) (negExp (neg t)))
    where
      N = proj₁ (neg-fin s)
      M = proj₁ (neg-fin t)
      K = proj₁ (neg-fin (s +S t))
      hn = ≤-trans (proj₂ (neg-fin s)) (≤-reflexive (sym (natE≈nat N)))
      hm = ≤-trans (proj₂ (neg-fin t)) (≤-reflexive (sym (natE≈nat M)))
      hk = ≤-trans (proj₂ (neg-fin (s +S t))) (≤-reflexive (sym (natE≈nat K)))

  private
    module CS = CommutativeSemiring commutativeSemiring
    module EWAlg = ExpWeightAlg CS.*-commutativeMonoid
  open EWAlg using (cancel-mul; cancel-3; rearrange-step; rearrange-step′; ud-step)

  bnd-natE : ∀ {a} → Bnd a → Σ ℕ (λ n → a ≤ natE n)
  bnd-natE (n , h) = n , ≤-trans h (≤-reflexive (sym (natE≈nat n)))

  neg-exp-inv : ∀ {a} → Bnd a → negExp a * expC lem a ≈ 1#
  neg-exp-inv {a} ba = negExp-expC-nat a (proj₁ (bnd-natE ba)) (proj₂ (bnd-natE ba))

  exp-inv : ∀ {a} → Bnd a → expC lem a * negExp a ≈ 1#
  exp-inv {a} ba = trans (*-comm (expC lem a) (negExp a)) (neg-exp-inv ba)

  expW-C-step : ∀ s t k →
    expW s * ((expC lem (neg s) * expC lem (neg t)) * expC lem k) ≈
    expC lem (pos s + neg t + k)
  expW-C-step s t k = begin
    expW s * ((expC lem (neg s) * expC lem (neg t)) * expC lem k)
      ≈⟨ rearrange-step (expC lem (pos s)) (negExp (neg s)) (expC lem (neg s)) (expC lem (neg t)) (expC lem k)
           (neg-exp-inv (neg-fin s)) ⟩
    (expC lem (pos s) * expC lem (neg t)) * expC lem k  ≈⟨ *-cong (sym (expC-add (pos s) (neg t))) refl ⟩
    expC lem (pos s + neg t) * expC lem k              ≈⟨ sym (expC-add (pos s + neg t) k) ⟩
    expC lem (pos s + neg t + k)                       ∎

  expW-C-step′ : ∀ s t k →
    expW t * ((expC lem (neg s) * expC lem (neg t)) * expC lem k) ≈
    expC lem (pos t + neg s + k)
  expW-C-step′ s t k = begin
    expW t * ((expC lem (neg s) * expC lem (neg t)) * expC lem k)
      ≈⟨ rearrange-step′ (expC lem (pos t)) (negExp (neg t)) (expC lem (neg s)) (expC lem (neg t)) (expC lem k)
           (neg-exp-inv (neg-fin t)) ⟩
    (expC lem (pos t) * expC lem (neg s)) * expC lem k  ≈⟨ *-cong (sym (expC-add (pos t) (neg s))) refl ⟩
    expC lem (pos t + neg s) * expC lem k              ≈⟨ sym (expC-add (pos t + neg s) k) ⟩
    expC lem (pos t + neg s + k)                       ∎

  expW-C-eq : ∀ s t (st : s ≃ t) →
    expW s * ((expC lem (neg s) * expC lem (neg t)) * expC lem (Bounded._≃_.k st)) ≈
    expW t * ((expC lem (neg s) * expC lem (neg t)) * expC lem (Bounded._≃_.k st))
  expW-C-eq s t (mk≃ k fk eq) =
    begin
      expW s * ((expC lem (neg s) * expC lem (neg t)) * expC lem k)  ≈⟨ expW-C-step s t k ⟩
      expC lem (pos s + neg t + k)                                   ≈⟨ expC-cong lem eq ⟩
      expC lem (pos t + neg s + k)                                   ≈⟨ sym (expW-C-step′ s t k) ⟩
      expW t * ((expC lem (neg s) * expC lem (neg t)) * expC lem k)  ∎

  expW-cong : ∀ {s t} → s ≃ t → expW s ≈ expW t
  expW-cong {s} {t} (mk≃ k fk eq) = cancel-mul (expW s) (expW t) C D
    (cancel-3 (exp-inv (neg-fin s)) (exp-inv (neg-fin t)) (exp-inv fk))
    (expW-C-eq s t (mk≃ k fk eq))
    where
      C = (expC lem (neg s) * expC lem (neg t)) * expC lem k
      D = (negExp (neg s) * negExp (neg t)) * negExp k

  expWT : ∀ {X : QBS S} → SgT X → Hom S X WQ
  expWT {X} f = record
    { map = record
        { to = λ x → expC lem (at⁺ f x) * negExp (at⁻ f x)
        ; cong = λ xy → *-cong (expC-cong lem (Func.cong (map (posT f)) xy))
                                (negExp-anti (proj₂ (Func.cong (map (negT f)) xy)) ,
                                 negExp-anti (proj₁ (Func.cong (map (negT f)) xy)))
        }
    ; map-random = λ mα → Meas-⊗ (Meas-expC (map-random (posT f) mα)) (Meas-negExp (map-random (negT f) mα))
    }

  atSg : ∀ {X : QBS S} (f : SgT X) → FinT f → ∀ x → Sg
  atSg f fin x = record
    { pos = at⁺ f x
    ; neg = at⁻ f x
    ; pos-fin = proj₁ (fin x)
    ; neg-fin = proj₂ (fin x)
    }

  expWT-cong : ∀ {X : QBS S} {f g : SgT X} → FinT f → FinT g → f ≐ g → _≈H_ S (expWT f) (expWT g)
  expWT-cong finf fing e {x} =
    expW-cong {s = atSg _ finf x} {t = atSg _ fing x} (mk≃ 0# Is-0 (+-cong (e x) refl))

  expC-pos : ∀ x → PosQ (expC lem x)
  expC-pos x = ½ , 0<½ , ap (⊑-trans (⊕-inl oneC x) (1+≤expC lem x)) ½ ½<1

  negExp-pos : ∀ {x} → Bnd x → PosQ (negExp x)
  negExp-pos {x} bx = q , 0<q , t , q<t , f
    where
      n = proj₁ (bnd-natE bx)
      h = proj₂ (bnd-natE bx)
      B = pow3 lem n
      0<B = 0<pow3 lem n
      t = proj₁ (inv 0<B)
      ht = proj₂ (inv 0<B)
      0<t = pos-inv 0<B ht
      q = t *ℚ ½
      0<q = *-pos 0<t 0<½
      q<t = ≃-<ʳ (P-id t) (*-mono-<-pos 0<t ½<1)
      f : ∀ s → Cut.mem (expC lem x) s → t *ℚ s < 1ℚᵘ
      f s ms = ≃-<ʳ ht (*-mono-<-pos 0<t (expC-bound lem x n h s ms))

  expW-pos : ∀ s → PosQ (expW s)
  expW-pos s = PosQ-mul {expC lem (pos s)} {negExp (neg s)} (expC-pos (pos s)) (negExp-pos (neg-fin s))

  expC-bnd : ∀ {x} → Bnd x → BndQ (expC lem x)
  expC-bnd {x} bx = pow3 lem n , expC-bound lem x n h
    where
      n = proj₁ (bnd-natE bx)
      h = proj₂ (bnd-natE bx)

  negExp-bnd : ∀ {x} → BndQ (negExp x)
  negExp-bnd {x} = 1ℚᵘ +ℚ 1ℚᵘ , λ r mr → <-trans (ap (negExp≤1 x) r mr) (lt-add 0<1)

  expW-bnd : ∀ s → BndQ (expW s)
  expW-bnd s = BndQ-mul {expC lem (pos s)} {negExp (neg s)} (expC-bnd (pos-fin s)) (negExp-bnd {neg s})

  expW-fin : ∀ s → Bnd (expW s)
  expW-fin s = rat-bnd (expW s) (expW-bnd s)

  -- the log equation behind `log-expW`
  log-expW-eq : ∀ s → logP (expW s) + neg s ≈ pos s + logN (expW s)
  log-expW-eq s = exp-inj (begin
    expC lem (logP x + neg s)  ≈⟨ expC-add (logP x) (neg s) ⟩
    ep * e
      ≈⟨ ud-step ep en p e (negExp (neg s)) (neg-exp-inv (neg-fin s)) (UD (expW-pos s) (expW-bnd s)) ⟩
    p * en                     ≈⟨ sym (expC-add (pos s) (logN x)) ⟩
    expC lem (pos s + logN x)  ∎)
    where
      x = expW s
      ep = expC lem (logP x)
      en = expC lem (logN x)
      p = expC lem (pos s)
      e = expC lem (neg s)

  log-expW : ∀ s → logS (expW s) (expW-pos s) (expW-bnd s) ≃ s
  log-expW s = mk≃ 0# Is-0 (begin
    logP (expW s) + neg s + 0#  ≈⟨ +-identityʳ _ ⟩
    logP (expW s) + neg s       ≈⟨ log-expW-eq s ⟩
    pos s + logN (expW s)       ≈⟨ sym (+-identityʳ _) ⟩
    pos s + logN (expW s) + 0#  ∎)


