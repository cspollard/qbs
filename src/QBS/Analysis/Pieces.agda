{-# OPTIONS --safe --without-K #-}

-- Splitting `[0,∞]` into countably many pieces on which a weight is bounded: the piece 0 is
-- `{w = ∞}` and the piece `k+1` is `{k < w ≤ k+1}`.  Every weight lies in at most one piece
-- (in none exactly when it is 0), which gives the pointwise decomposition of an integrand
-- `w · g` as a countable sum over the pieces (with `∞ · g` on the piece 0).
module QBS.Analysis.Pieces where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (tt)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Data.Rational.Unnormalised.Base using (_≤_; _<_; _+_; _≃_)
import Relation.Binary.Definitions

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Series using (module Series)
open import QBS.Classical using (LEM₀)

open Cut
open _⊑_

module Pieces (lem : LEM₀) where
  A = LowerRealsOmega lem
  open OmegaSemiring A using (_≈_; _*_; 0#; 1#; trans; sym; refl; zeroˡ) renaming
      (*-cong to *ᴬ-cong; *-identityˡ to *ᴬ-identityˡ; *-assoc to *ᴬ-assoc)
  open Series A

  -- the piece predicates on a weight
  InPiece : ℕ → Cut → Set
  InPiece ℕ.zero w = ∀ k → mem w (nat k)
  InPiece (ℕ.suc k) w = mem w (nat k) × (mem w (nat (ℕ.suc k)) → ⊥)

  -- the weight factor of the piece (the piece 0 carries the constant ∞)
  κ : ℕ → Cut
  κ ℕ.zero = infC
  κ (ℕ.suc _) = 1#

  fac : ℕ → Cut → Cut
  fac ℕ.zero w = 1#
  fac (ℕ.suc _) w = w

  ----------------------------------------------------------------------------
  -- facts about the naturals as rationals and cuts

  nat-mono-suc : ∀ k → nat k ≤ nat (ℕ.suc k)
  nat-mono-suc k = ≤-trans (≤-≃ (≃-sym (+-identityʳ (nat k))))
    (≤-trans (+-mono-≤ (≤-refl {nat k}) (<-≤ 0<1)) (≤-≃ (≃-sym (nat-suc k))))

  nat-0≤ : ∀ j → 0ℚᵘ ≤ nat j
  nat-0≤ ℕ.zero = ≤-refl
  nat-0≤ (ℕ.suc j) = ≤-trans (nat-0≤ j) (nat-mono-suc j)

  nat-mono : ∀ {k j} → k ℕ.≤ j → nat k ≤ nat j
  nat-mono {ℕ.zero} {j} ℕ.z≤n = nat-0≤ j
  nat-mono {ℕ.suc k} {ℕ.suc j} (ℕ.s≤s h) =
    ≤-trans (≤-≃ (nat-suc k)) (≤-trans (+-mono-≤ (nat-mono h) (≤-refl {1ℚᵘ})) (≤-≃ (≃-sym (nat-suc j))))

  -- every weight with all `nat k` below it is ∞
  all⇒inf : ∀ w → (∀ k → mem w (nat k)) → w ≋ infC
  all⇒inf w h = mk⊑ (λ _ _ → tt) , mk⊑ (λ q _ →
    let k , qk = nat-bound q in down w qk (h k))

  -- a weight not above 0 is 0
  nonpos⇒zero : ∀ w → (mem w 0ℚᵘ → ⊥) → w ≋ zeroC
  nonpos⇒zero w h = mk⊑ (λ q mq → case-lt q mq) , mk⊑ (λ q q<0 → neg w q<0)
    where
      case-lt : ∀ q → mem w q → q < 0ℚᵘ
      case-lt q mq with neg-or-nonneg q
      ... | inj₁ q<0 = q<0
      ... | inj₂ 0≤q = ⊥-elim (h (down w 0≤q mq))

  ----------------------------------------------------------------------------
  -- every weight is in a unique piece, or is 0

  not-all⇒ex : ∀ w → ((∀ k → mem w (nat k)) → ⊥) → Σ ℕ (λ k → mem w (nat k) → ⊥)
  not-all⇒ex w notAll with lem (Σ ℕ (λ k → mem w (nat k) → ⊥))
  ... | inj₁ s = s
  ... | inj₂ no = ⊥-elim (notAll (λ k → dec k))
    where
      dec : ∀ k → mem w (nat k)
      dec k with lem (mem w (nat k))
      ... | inj₁ yes = yes
      ... | inj₂ n = ⊥-elim (no (k , n))

  -- the first failure
  find : ∀ w → mem w 0ℚᵘ → ∀ k → (mem w (nat k) → ⊥) → Σ ℕ (λ j → mem w (nat j) × (mem w (nat (ℕ.suc j)) → ⊥))
  find w m0 ℕ.zero nk = ⊥-elim (nk m0)
  find w m0 (ℕ.suc k) nk with lem (mem w (nat k))
  ... | inj₁ yes = k , yes , nk
  ... | inj₂ no = find w m0 k no

  piece-of : ∀ w → Σ ℕ (λ n → InPiece n w) ⊎ (w ≋ zeroC)
  piece-of w with lem (∀ k → mem w (nat k))
  ... | inj₁ all = inj₁ (ℕ.zero , all)
  ... | inj₂ notAll with lem (mem w 0ℚᵘ)
  ...   | inj₂ n0 = inj₂ (nonpos⇒zero w n0)
  ...   | inj₁ m0 with not-all⇒ex w notAll
  ...     | k₁ , nk₁ with find w m0 k₁ nk₁
  ...       | j , mj , nj = inj₁ (ℕ.suc j , mj , nj)

  piece-unique : ∀ w {n n′} → InPiece n w → InPiece n′ w → n ≡.≡ n′
  piece-unique w {ℕ.zero} {ℕ.zero} _ _ = ≡.refl
  piece-unique w {ℕ.zero} {ℕ.suc k} a (_ , nk) = ⊥-elim (nk (a (ℕ.suc k)))
  piece-unique w {ℕ.suc k} {ℕ.zero} (_ , nk) a = ⊥-elim (nk (a (ℕ.suc k)))
  piece-unique w {ℕ.suc k} {ℕ.suc k′} (mk , nk) (mk′ , nk′) with ℕ.<-cmp k k′
  ... | Relation.Binary.Definitions.tri< lt _ _ = ⊥-elim (nk (down w (nat-mono lt) mk′))
  ... | Relation.Binary.Definitions.tri≈ _ eq _ = ≡.cong ℕ.suc eq
  ... | Relation.Binary.Definitions.tri> _ _ gt = ⊥-elim (nk′ (down w (nat-mono gt) mk))

  ----------------------------------------------------------------------------
  -- the pointwise decomposition

  -- on its own piece the integrand is `w · g`
  onPiece : ∀ n w g χ → InPiece n w → χ ≈ 1# → κ n * ((χ * fac n w) * g) ≈ w * g
  onPiece ℕ.zero w g χ all χ1 = trans
      (*ᴬ-cong (refl {infC}) (trans (*ᴬ-cong (trans (*ᴬ-cong χ1 (refl {1#})) (*ᴬ-identityˡ 1#)) (refl {g})) (*ᴬ-identityˡ g)))
                                       (*ᴬ-cong (sym (all⇒inf w all)) (refl {g}))
  onPiece (ℕ.suc _) w g χ _ χ1 = trans (*ᴬ-identityˡ _) (*ᴬ-cong (trans (*ᴬ-cong χ1 (refl {w})) (*ᴬ-identityˡ w)) (refl {g}))

  decomp : ∀ w g (χs : ℕ → Cut) →
    (∀ n → (InPiece n w × χs n ≈ 1#) ⊎ ((InPiece n w → ⊥) × χs n ≈ 0#)) →
    ∑ᶠ (λ n → κ n * ((χs n * fac n w) * g)) ≈ w * g
  decomp w g χs hχ with piece-of w
  ... | inj₁ (n₀ , in₀) = trans (∑ᶠ-single {λ n → κ n * ((χs n * fac n w) * g)} n₀ off) on
    where
      off : ∀ n → (n ≡.≡ n₀ → ⊥) → κ n * ((χs n * fac n w) * g) ≈ 0#
      off n n≢ with hχ n
      ... | inj₁ (inn , _) = ⊥-elim (n≢ (piece-unique w inn in₀))
      ... | inj₂ (_ , z) = trans
          (*ᴬ-cong (refl {κ n}) (trans (*ᴬ-cong (trans (*ᴬ-cong z (refl {fac n w})) (zeroˡ _)) (refl {g})) (zeroˡ g)))
          (OmegaSemiring.zeroʳ A (κ n))
      χ₀ : χs n₀ ≈ 1#
      χ₀ with hχ n₀
      ... | inj₁ (_ , o) = o
      ... | inj₂ (ni , _) = ⊥-elim (ni in₀)
      on : κ n₀ * ((χs n₀ * fac n₀ w) * g) ≈ w * g
      on = onPiece n₀ w g (χs n₀) in₀ χ₀
  ... | inj₂ w0 = trans (∑ᶠ-zero {λ n → κ n * ((χs n * fac n w) * g)} zeros)
                     (sym (trans (*ᴬ-cong w0 (refl {g})) (zeroˡ g)))
    where
      noPiece : ∀ n → InPiece n w → ⊥
      noPiece ℕ.zero all = <-irrefl ≃-refl (ap (proj₁ w0) 0ℚᵘ (all ℕ.zero))
      noPiece (ℕ.suc k) (mk , _) = <-irrefl ≃-refl (ap (proj₁ w0) 0ℚᵘ (down w (nat-0≤ k) mk))
      zeros : ∀ n → κ n * ((χs n * fac n w) * g) ≈ 0#
      zeros n with hχ n
      ... | inj₁ (inn , _) = ⊥-elim (noPiece n inn)
      ... | inj₂ (_ , z) = trans
          (*ᴬ-cong (refl {κ n}) (trans (*ᴬ-cong (trans (*ᴬ-cong z (refl {fac n w})) (zeroˡ _)) (refl {g})) (zeroˡ g)))
          (OmegaSemiring.zeroʳ A (κ n))
