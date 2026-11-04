{-# OPTIONS --safe --without-K #-}

-- The negative part of the logarithm, `logN x = log (1 / (x ⊓ 1))` (plan 03, "Signed layer", helper for `SignedLog`):
-- logN x = logP (recC (x ⊓ 1)), the positive logarithm of the reciprocal of the part of x below 1.
--   * `logN-anti`, `logN-cong`, `logN-bndQ` (positive x gives a bounded logN x), `Meas-logN`;
--   * `logN-ge` : logN x ≈ 0 for 1 ≤ x;
--   * `logN-le` : e^{−logN x} ≈ x for x ≤ 1 positive, from `negExp-expC` for e^{N} ≈ recC (x ⊓ 1) (`logP-ge`),
--     `recC-mul`, and commutativity;
--   * `UD` : x · e^{logN x} ≈ e^{logP x} for x positive and bounded (the two cases x ≤ 1 and 1 ≤ x, `tot1`).
module QBS.Continuous.LogNeg where

open import Level using (lift)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LowerRealsNear using (BndQ)
open import QBS.Analysis.ExpLower using (expC; expC-zero; expC-cong; P-id; module Add)
open import QBS.Analysis.NegExp using (module NegExp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.LogCore using (module LogCore)
open import QBS.Continuous.LogRecip using (recC; recC-anti; recC-cong; module LogRecip)
open import QBS.Classical using (LEM₀)

PosQ′ : Cut → Set
PosQ′ x = Σ ℚᵘ (λ q → 0ℚᵘ < q × mem x q)

½<1 : ½ < 1ℚᵘ
½<1 = ≃-<ʳ ½+½ (lt-add {½} 0<½)

-- a point of x ⊓ 1 above 0
posw : ∀ {x} → PosQ′ x → Σ ℚᵘ (λ a → 0ℚᵘ < a × mem (x ⊓ oneC) a)
posw {x} (q , 0<q , mq) with ≤-or-> 1ℚᵘ q
... | inj₂ q<1 = q , 0<q , mq , q<1
... | inj₁ 1≤q = ½ , 0<½ , down x (<-≤ (<-≤-trans ½<1 1≤q)) mq , ½<1

rec-step : ∀ {q′ s} → 0ℚᵘ < q′ → q′ < 1ℚᵘ → s < 1ℚᵘ → q′ * s < 1ℚᵘ
rec-step {q′} {s} 0<q′ q′<1 s<1 with pos-or-nonpos s
... | inj₁ 0<s = <-trans (≃-<ʳ (P-id q′) (*-mono-<-pos 0<q′ s<1)) q′<1
... | inj₂ s≤0 = ≤-<-trans (≤-trans (*-mono-≤-nn (<-≤ 0<q′) s≤0) (≤-≃ (≃-trans (*-comm q′ 0ℚᵘ) (*-zeroˡ q′)))) 0<1

-- the reciprocal of a part below 1 is at least 1
one⊑recC : ∀ {w} → w ⊑ oneC → oneC ⊑ recC w
one⊑recC {w} wo = mk⊑ go
  where
    go : ∀ q → q < 1ℚᵘ → mem (recC w) q
    go q lt with neg-or-nonneg q
    ... | inj₁ q<0 = neg (recC w) q<0
    ... | inj₂ 0≤q = let q′ , q<q′ , q′<1 = dense lt
      in q′ , q<q′ , λ s ms → rec-step (≤-<-trans 0≤q q<q′) q′<1 (ap wo s ms)

-- the reciprocal of a cut with a positive point is bounded
bnd-rec : ∀ {w a} → 0ℚᵘ < a → mem w a → BndQ (recC w)
bnd-rec {w} {a} 0<a ma = t , λ q (p , lt , f) → <-trans lt
  (*-cancel-<ʳ 0<a (≃-<ʳ (≃-sym ht) (f a ma)))
  where
    t = proj₁ (inv 0<a)
    ht = proj₂ (inv 0<a)

-- a cut is below 1 or above 1
tot1 : LEM₀ → ∀ x → x ⊑ oneC ⊎ oneC ⊑ x
tot1 lem x with lem (Σ ℚᵘ (λ q → mem x q × 1ℚᵘ ≤ q))
... | inj₁ (q , mq , 1≤q) = inj₂ (mk⊑ (λ r lt → down x (<-≤ (<-≤-trans lt 1≤q)) mq))
... | inj₂ none = inj₁ (mk⊑ (λ q mq → go q mq (≤-or-> 1ℚᵘ q)))
  where
    go : ∀ q → mem x q → 1ℚᵘ ≤ q ⊎ q < 1ℚᵘ → q < 1ℚᵘ
    go q mq (inj₁ le) = ⊥-elim (none (q , mq , le))
    go q mq (inj₂ lt) = lt

module LogNeg (lem : LEM₀) where
  open LogCore lem using (logP; logP-mono; logP-cong; logP-le; logP-ge; logP-bndQ; Meas-logP; log-exp-P)
  open LogRecip lem using (recC-mul; recC-lt1; Meas-recC)
  open NegExp lem using (negExp; negExp-expC)
  open Meas lem using (Meas; Meas-⊓; Meas-const)
  A = LowerRealsOmega lem
  open OmegaSemiring A using (commutativeSemiring; refl)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  logN : Cut → Cut
  logN x = logP (recC (x ⊓ oneC))

  ⊓1-mono : ∀ {x y} → x ⊑ y → x ⊓ oneC ⊑ y ⊓ oneC
  ⊓1-mono xy = mk⊑ (λ q (a , b) → ap xy q a , b)

  logN-anti : ∀ {x y} → x ⊑ y → logN y ⊑ logN x
  logN-anti xy = logP-mono (recC-anti (⊓1-mono xy))

  logN-cong : ∀ {x y} → x ≋ y → logN x ≋ logN y
  logN-cong (a , b) = logN-anti b , logN-anti a

  logN-bndQ : ∀ {x} → PosQ′ x → BndQ (logN x)
  logN-bndQ {x} px = let a , 0<a , ma = posw {x} px in logP-bndQ {recC (x ⊓ oneC)} (bnd-rec {x ⊓ oneC} 0<a ma)

  logN-ge : ∀ {x} → oneC ⊑ x → logN x ≋ zeroC
  logN-ge ox = logP-le (recC-lt1 (mk⊑ (λ q lt → ap ox q lt , lt)))

  w≋ : ∀ {x} → x ⊑ oneC → x ⊓ oneC ≋ x
  w≋ {x} xo = mk⊑ (λ q (a , _) → a) , mk⊑ (λ q m → m , ap xo q m)

  rec-exp : ∀ {x} → PosQ′ x → x ⊑ oneC → expC lem (logN x) ≋ recC (x ⊓ oneC)
  rec-exp {x} px xo = logP-ge (recC (x ⊓ oneC)) (one⊑recC (mk⊑ (λ q (_ , lt) → lt)))
    (bnd-rec {x ⊓ oneC} (proj₁ (proj₂ (posw {x} px))) (proj₂ (proj₂ (posw {x} px))))

  NE : ∀ {x} → PosQ′ x → x ⊑ oneC → negExp (logN x) ⊗ expC lem (logN x) ≋ oneC
  NE {x} px xo = negExp-expC (logN x) (proj₁ bz) (λ s ms → proj₂ bz s (ap (proj₁ (rec-exp px xo)) s ms))
    where bz = bnd-rec {x ⊓ oneC} (proj₁ (proj₂ (posw {x} px))) (proj₂ (proj₂ (posw {x} px)))

  logN-le : ∀ {x} → PosQ′ x → x ⊑ oneC → negExp (logN x) ≋ x
  logN-le {x} px xo = ≋-trans (≋-sym (⊗-identityˡ n)) (≋-trans (⊗-cong (≋-sym rm) (≋-refl {n}))
    (≋-trans eq (≋-trans (⊗-cong (≋-refl {w}) (⊗-cong (≋-refl {n}) (≋-sym (rec-exp px xo))))
      (≋-trans (⊗-cong (≋-refl {w}) (NE px xo)) (≋-trans (⊗-comm w oneC) (≋-trans (⊗-identityˡ w) (w≋ xo)))))))
    where
      w = x ⊓ oneC
      z = recC w
      n = negExp (logN x)
      a = posw {x} px
      rm : z ⊗ w ≋ oneC
      rm = recC-mul w 1ℚᵘ (λ s (_ , lt) → lt) (proj₁ (proj₂ a)) (proj₂ (proj₂ a))
      eq : (z ⊗ w) ⊗ n ≋ w ⊗ (n ⊗ z)
      eq = solve 3 (λ z w n → (z :* w) :* n := w :* (n :* z)) refl z w n

  -- x · e^{logN x} = e^{logP x}
  UD : ∀ {x} → PosQ′ x → BndQ x → x ⊗ expC lem (logN x) ≋ expC lem (logP x)
  UD {x} px bx with tot1 lem x
  ... | inj₁ xo = ≋-trans (⊗-cong (≋-sym (logN-le px xo)) (≋-refl {expC lem (logN x)}))
    (≋-trans (NE px xo) (≋-sym (≋-trans (expC-cong lem (logP-le xo)) (expC-zero lem))))
  ... | inj₂ ox = ≋-trans (⊗-cong (≋-refl {x}) (≋-trans (expC-cong lem (logN-ge ox)) (expC-zero lem)))
    (≋-trans (⊗-comm x oneC) (≋-trans (⊗-identityˡ x) (≋-sym (logP-ge x ox bx))))

  Meas-logN : ∀ {h} → Meas h → Meas (λ r → logN (h r))
  Meas-logN {h} mh = Meas-logP (Meas-recC (Meas-⊓ {h} {λ _ → oneC} mh (Meas-const oneC)))

  -- e^a = e^b gives a = b
  exp-inj : ∀ {a b} → expC lem a ≋ expC lem b → a ≋ b
  exp-inj {a} {b} h = ≋-trans (≋-sym (log-exp-P a)) (≋-trans (logP-cong h) (log-exp-P b))

  logmul-eq : ∀ x y d dx dy → ((x ⊗ y) ⊗ d) ⊗ (dx ⊗ dy) ≋ ((x ⊗ dx) ⊗ (y ⊗ dy)) ⊗ d
  logmul-eq = solve 5 (λ x y d dx dy → ((x :* y) :* d) :* (dx :* dy) := ((x :* dx) :* (y :* dy)) :* d) refl

  -- the exponentials of both sides of log (x y) + log x⁻ + log y⁻ = log x⁺ + log y⁺ + log (x y)⁻ agree
  logmul-exp : ∀ {x y} → PosQ′ x → PosQ′ y → PosQ′ (x ⊗ y) → BndQ x → BndQ y → BndQ (x ⊗ y) →
    expC lem (logP (x ⊗ y) ⊕ (logN x ⊕ logN y)) ≋ expC lem ((logP x ⊕ logP y) ⊕ logN (x ⊗ y))
  logmul-exp {x} {y} px py pxy bx by bxy = ≋-trans (Add.exp-add lem (logP (x ⊗ y)) (logN x ⊕ logN y))
    (≋-trans (⊗-cong (≋-sym (UD pxy bxy)) (Add.exp-add lem (logN x) (logN y)))
      (≋-trans (logmul-eq x y (expC lem (logN (x ⊗ y))) (expC lem (logN x)) (expC lem (logN y)))
        (≋-trans (⊗-cong (⊗-cong (UD px bx) (UD py by)) (≋-refl {expC lem (logN (x ⊗ y))}))
          (≋-sym (≋-trans (Add.exp-add lem (logP x ⊕ logP y) (logN (x ⊗ y)))
            (⊗-cong (Add.exp-add lem (logP x) (logP y)) (≋-refl {expC lem (logN (x ⊗ y))})))))))
