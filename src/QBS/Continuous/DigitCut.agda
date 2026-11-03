{-# OPTIONS --safe --without-K #-}

-- Two facts about cuts that the digit code of `[0,∞]` needs (`Continuous/DigitCode`), both from `Analysis/ExpLower`:
-- `natE (n+1)` and `m / 2ⁿ` are rational cuts, so a point is either above a dyadic threshold or below it.
--   * `below-dec`: if x is not ≥ the dyadic point `(M+1)/2ⁿ`, then x ≤ `(M+1)/2ⁿ`;
--   * `nat-big`: every rational lies in some `natE k` (the natural numbers are cofinal).
module QBS.Continuous.DigitCut where

open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Sum.Base as Sum
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; _<_; _≤_)

open import QBS.Classical using (LEM₀)
open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut using (mem; down)
open _⊑_ using (ap)
open import QBS.Analysis.LowerRealsArch using (qC; hpC; hpC≈; tp; tp-pos)
open import QBS.Analysis.ExpLower using (natE≋; qC-mul; 0<nat)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Continuous.Intervals using (module Intervals)

module DigitCut (lem : LEM₀) where
  open Lebesgue lem using (A)
  open Exp A using (natE)
  open Intervals lem using (Ge; dy)

  -- the dyadic point `(M+1)/2ⁿ` is the rational cut `(M+1) · 2⁻ⁿ`
  dy-q : ∀ M n → dy n (suc M) ≋ qC (nat (suc M) * tp n) (*-pos (0<nat M) (tp-pos n))
  dy-q M n = ≋-trans (⊗-cong (natE≋ lem M) (≋-sym (hpC≈ lem n))) (qC-mul (0<nat M) (tp-pos n))

  below-dec : ∀ M n x → (Ge (dy n (suc M)) x → ⊥) → x ⊑ dy n (suc M)
  below-dec M n x ng = mk⊑ (λ q mq → ap (proj₂ (dy-q M n)) q (lt q mq))
    where
      r : ℚᵘ
      r = nat (suc M) * tp n
      lt : ∀ q → mem x q → q < r
      lt q mq = Sum.[ (λ r≤q → ⊥-elim (ng (λ s ms → down x (<-≤ (<-≤-trans (ap (proj₁ (dy-q M n)) s ms) r≤q)) mq)))
                    , (λ q<r → q<r) ]′ (≤-or-> r q)

  nat-big : ∀ q → Σ ℕ (λ k → mem (natE k) q)
  nat-big q with nat-bound (q + 1ℚᵘ)
  ... | k , le = suc k , ap (proj₂ (natE≋ lem k)) q (<-≤-trans (lt-add 0<1) (≤-trans le (nat-mono (ℕ.n≤1+n k))))
