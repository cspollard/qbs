{-# OPTIONS --safe --without-K #-}

-- The additive extended non-negative reals ([0,∞], +, ×) as lower cuts of the rationals, as a
-- normalisable complete semiring: sums over arbitrary index sets are genuine sums (finite
-- sub-sums of distinct indices, see `Analysis/CutSum.agda`), so measures over it are ordinary
-- (countably additive) probability weights.  Classical: excluded middle for `Set₁`, which also
-- gives decidable equality and hence proof-irrelevant identity on index types.
module QBS.Model.AdditiveSemiring where

import Level as L
open import Function.Bundles using (Inverse; _↔_)
open import Function.Base using (case_of_)
open import Data.Empty.Polymorphic using (⊥)
import Data.Empty as E
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Data.Rational.Unnormalised.Base using (_≃_; _<_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.CutSum
open Basic
open import QBS.Model.Semiring
open import QBS.Classical using (LEM)

private
  ℓ₁ = L.suc L.zero

module _ (lem₁ : LEM ℓ₁) where
  private
    lem′ : ∀ (P : Set₁) → P ⊎ (P → E.⊥)
    lem′ P with lem₁ P
    ... | inj₁ p = inj₁ p
    ... | inj₂ n = inj₂ (λ p → case n p of λ ())

    lift⊥ : E.⊥ → ⊥ {ℓ₁}
    lift⊥ ()

  open CSum lem′

  additiveComplete : CompleteSemiring ℓ₁
  additiveComplete = record
    { commutativeSemiring = cutSemiring
    ; ∑ = sumC
    ; ∑-cong = λ {I} {f} {g} e →
        mk⊑ (λ q d → Mem⇒sum (Mem-mono (λ i → proj₁ (e i)) (sum⇒Mem d)))
        , mk⊑ (λ q d → Mem⇒sum (Mem-mono (λ i → proj₂ (e i)) (sum⇒Mem d)))
    ; ∑-empty = λ f →
        mk⊑ (λ q d → Mem-empty (sum⇒Mem d)) , mk⊑ (λ q lt → Mem⇒sum (m-neg lt))
    ; ∑-unit = λ f →
        mk⊑ (λ q d → Mem-unit (sum⇒Mem d)) , mk⊑ (λ q m → Mem⇒sum (Mem-unit⁻ m))
    ; ∑-⊎ = λ {I} {J} f →
        mk⊑ (λ q d → let a , b , ma , mb , le = Sum.split (sum⇒Mem d)
                     in a , b , Mem⇒sum ma , Mem⇒sum mb , le)
        , mk⊑ (λ q (a , b , ma , mb , le) → Mem⇒sum (Sum.join (sum⇒Mem ma) (sum⇒Mem mb) le))
    ; ∑-Σ = λ {I} {J} f → sum-Σ f
    ; ∑-reindex = λ {I} {J} e f →
        mk⊑ (λ q d → Mem⇒sum (Mem-mono (λ j → subst-⊑ f (Inverse.inverseˡ e refl))
               (Reindex.reidx (Inverse.to e) (Inverse.from e) (λ i → Inverse.inverseʳ e refl)
                   (λ j → Inverse.inverseˡ e refl) (sum⇒Mem d))))
        , mk⊑ (λ q d → Mem⇒sum
            (Reindex.reidx (Inverse.from e) (Inverse.to e) (λ j → Inverse.inverseˡ e refl)
            (λ i → Inverse.inverseʳ e refl) (sum⇒Mem d)))
    ; ∑-distribˡ = λ {I} x f → sum-distribˡ x f
    }
    where
      subst-⊑ : ∀ {J : Set₁} (f : J → Cut) {a b : J} → a ≡ b → f a ⊑ f b
      subst-⊑ f refl = ⊑-refl

  -- weights invertible iff neither 0 nor ∞, decided classically
  additiveNormalizable : NormalizableSemiring ℓ₁
  additiveNormalizable = record
    { complete = additiveComplete
    ; invertible? = λ m → case lem₁ (Σ Cut (λ n → m ⊗ n ≋ oneC)) of λ
        { (inj₁ p) → inj₁ p ; (inj₂ no) → inj₂ (λ n e → no (n , e)) }
    ; nontrivial = λ e → lift⊥ (<-irrefl ≃-refl (ap (proj₂ e) 0ℚᵘ 0<1))
    }
