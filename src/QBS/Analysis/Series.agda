{-# OPTIONS --safe --without-K #-}

-- Countable sums in an `OmegaSemiring`: ∑ᶠ a = ⨆ of the partial sums.  Additivity, scaling,
-- shifting, and Tonelli (swapping iterated sums; summing along the Cantor enumeration of ℕ × ℕ).
module QBS.Analysis.Series where

open import Level using (Level)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Model.Pairing

module Series {ℓ} (A : OmegaSemiring ℓ) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open SetoidReasoning setoid

  ----------------------------------------------------------------------------
  -- finite partial sums

  psum : (ℕ → ∣A∣) → ℕ → ∣A∣
  psum a ℕ.zero = 0#
  psum a (ℕ.suc N) = psum a N + a N

  psum-inc : ∀ a → Increasing (psum a)
  psum-inc a N = ≤-+ʳ

  ∑ᶠ : (ℕ → ∣A∣) → ∣A∣
  ∑ᶠ a = ⨆ (psum a) (psum-inc a)

  open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup using () renaming (interchange to +-interchange)

  ≤-+ˡ : ∀ {a b} → b ≤ a + b
  ≤-+ˡ {a} {b} = ≤-resp refl (+-comm b a) ≤-+ʳ

  psum-cong : ∀ {a b} → (∀ n → a n ≈ b n) → ∀ N → psum a N ≈ psum b N
  psum-cong e ℕ.zero = refl
  psum-cong e (ℕ.suc N) = +-cong (psum-cong e N) (e N)

  -- agreement below N suffices
  psum-cong-lt : ∀ {a b} N → (∀ n → n ℕ.< N → a n ≈ b n) → psum a N ≈ psum b N
  psum-cong-lt ℕ.zero e = refl
  psum-cong-lt (ℕ.suc N) e =
    +-cong (psum-cong-lt N (λ n n<N → e n (ℕ.m<n⇒m<1+n n<N))) (e N (ℕ.n<1+n N))

  psum-mono : ∀ {a b} → (∀ n → a n ≤ b n) → ∀ N → psum a N ≤ psum b N
  psum-mono le ℕ.zero = ≤-refl
  psum-mono le (ℕ.suc N) = +-mono (psum-mono le N) (le N)

  psum-index-mono : ∀ a {N N′} → N ℕ.≤ N′ → psum a N ≤ psum a N′
  psum-index-mono a h = inc-mono (psum a) (psum-inc a) (ℕ.≤⇒≤′ h)

  psum-+ : ∀ a b N → psum (λ n → a n + b n) N ≈ psum a N + psum b N
  psum-+ a b ℕ.zero = sym (+-identityˡ 0#)
  psum-+ a b (ℕ.suc N) = begin
    psum (λ n → a n + b n) N + (a N + b N)   ≈⟨ +-cong (psum-+ a b N) refl ⟩
    (psum a N + psum b N) + (a N + b N)      ≈⟨ +-interchange _ _ _ _ ⟩
    (psum a N + a N) + (psum b N + b N)      ∎

  psum-scale : ∀ c a N → psum (λ n → c * a n) N ≈ c * psum a N
  psum-scale c a ℕ.zero = sym (zeroʳ c)
  psum-scale c a (ℕ.suc N) = trans (+-cong (psum-scale c a N) refl) (sym (distribˡ c (psum a N) (a N)))

  term-≤-psum : ∀ a {n N} → n ℕ.< N → a n ≤ psum a N
  term-≤-psum a {n} {ℕ.suc N} (ℕ.s≤s n≤N) with n ℕ.≟ N
  ... | yes ≡.refl = ≤-+ˡ
  ... | no n≢N = ≤-trans (term-≤-psum a (ℕ.≤∧≢⇒< n≤N n≢N)) (psum-inc a N)

  psum≤∑ᶠ : ∀ a N → psum a N ≤ ∑ᶠ a
  psum≤∑ᶠ a N = ⨆-ub (psum a) (psum-inc a) N

  ≤-∑ᶠ : ∀ a n → a n ≤ ∑ᶠ a
  ≤-∑ᶠ a n = ≤-trans (term-≤-psum a (ℕ.n<1+n n)) (psum≤∑ᶠ a (ℕ.suc n))

  ∑ᶠ-lub : ∀ {a b} → (∀ N → psum a N ≤ b) → ∑ᶠ a ≤ b
  ∑ᶠ-lub {a} le = ⨆-lub (psum a) (psum-inc a) le

  ∑ᶠ-mono : ∀ {a b} → (∀ n → a n ≤ b n) → ∑ᶠ a ≤ ∑ᶠ b
  ∑ᶠ-mono {a} {b} le = ∑ᶠ-lub (λ N → ≤-trans (psum-mono le N) (psum≤∑ᶠ b N))

  ∑ᶠ-cong : ∀ {a b} → (∀ n → a n ≈ b n) → ∑ᶠ a ≈ ∑ᶠ b
  ∑ᶠ-cong e = ≤-antisym (∑ᶠ-mono (λ n → ≤-reflexive (e n))) (∑ᶠ-mono (λ n → ≤-reflexive (sym (e n))))

  ----------------------------------------------------------------------------
  -- elementary sums

  psum-zero : ∀ {a} → (∀ n → a n ≈ 0#) → ∀ N → psum a N ≈ 0#
  psum-zero e ℕ.zero = refl
  psum-zero e (ℕ.suc N) = trans (+-cong (psum-zero e N) (e N)) (+-identityˡ 0#)

  ∑ᶠ-zero : ∀ {a} → (∀ n → a n ≈ 0#) → ∑ᶠ a ≈ 0#
  ∑ᶠ-zero e = ≤-antisym (∑ᶠ-lub (λ N → ≤-reflexive (psum-zero e N))) 0-least

  ∑ᶠ-single : ∀ {a} k → (∀ n → (n ≡.≡ k → ⊥) → a n ≈ 0#) → ∑ᶠ a ≈ a k
  ∑ᶠ-single {a} k e = ≤-antisym (∑ᶠ-lub bound) (≤-∑ᶠ a k)
    where
      bound : ∀ N → psum a N ≤ a k
      bound ℕ.zero = 0-least
      bound (ℕ.suc N) with N ℕ.≟ k
      ... | yes ≡.refl = ≤-reflexive (trans (+-cong
              (trans (psum-cong-lt N (λ n n<N → e n (λ n≡N → ℕ.<-irrefl n≡N n<N)))
                     (psum-zero {λ _ → 0#} (λ _ → refl) N))
              refl) (+-identityˡ _))
      ... | no N≢k = ≤-trans (≤-reflexive (trans (+-cong refl (e N N≢k)) (+-identityʳ _))) (bound N)

  ----------------------------------------------------------------------------
  -- suprema of sums

  ⨆-mono : ∀ {c d} (ic : Increasing c) (id : Increasing d) → (∀ n → c n ≤ d n) → ⨆ c ic ≤ ⨆ d id
  ⨆-mono {c} {d} ic id le = ⨆-lub c ic (λ n → ≤-trans (le n) (⨆-ub d id n))

  ⨆-+-lub : ∀ {c d} (ic : Increasing c) (id : Increasing d) {b} →
    (∀ m n → c m + d n ≤ b) → ⨆ c ic + ⨆ d id ≤ b
  ⨆-+-lub {c} {d} ic id {b} h =
    ≤-trans (≤-reflexive (+-⨆ (⨆ c ic) d id incL)) (⨆-lub _ incL step)
    where
      incL : Increasing (λ n → ⨆ c ic + d n)
      incL n = +-mono ≤-refl (id n)
      step : ∀ n → ⨆ c ic + d n ≤ b
      step n = ≤-trans (≤-reflexive (trans (+-comm _ _) (+-⨆ (d n) c ic incR)))
                 (⨆-lub _ incR (λ m → ≤-trans (≤-reflexive (+-comm (d n) (c m))) (h m n)))
        where
          incR : Increasing (λ m → d n + c m)
          incR m = +-mono ≤-refl (ic m)

  ⨆-+-diag : ∀ {c d} (ic : Increasing c) (id : Increasing d) (incS : Increasing (λ n → c n + d n)) →
    ⨆ c ic + ⨆ d id ≈ ⨆ (λ n → c n + d n) incS
  ⨆-+-diag {c} {d} ic id incS = ≤-antisym
    (⨆-+-lub ic id (λ m n → ≤-trans
      (+-mono (inc-mono c ic (ℕ.≤⇒≤′ (ℕ.m≤m⊔n m n))) (inc-mono d id (ℕ.≤⇒≤′ (ℕ.m≤n⊔m m n))))
      (⨆-ub _ incS (m ℕ.⊔ n))))
    (⨆-lub _ incS (λ n → +-mono (⨆-ub c ic n) (⨆-ub d id n)))

  ⨆-shift : ∀ c (ic : Increasing c) (ic′ : Increasing (λ n → c (ℕ.suc n))) →
    ⨆ c ic ≈ ⨆ (λ n → c (ℕ.suc n)) ic′
  ⨆-shift c ic ic′ = ≤-antisym
    (⨆-lub c ic (λ n → ≤-trans (ic n) (⨆-ub _ ic′ n)))
    (⨆-lub _ ic′ (λ n → ⨆-ub c ic (ℕ.suc n)))

  ∑ᶠ-+ : ∀ a b → ∑ᶠ (λ n → a n + b n) ≈ ∑ᶠ a + ∑ᶠ b
  ∑ᶠ-+ a b = trans (⨆-cong (psum-inc _) incS (psum-+ a b))
                   (sym (⨆-+-diag (psum-inc a) (psum-inc b) incS))
    where
      incS : Increasing (λ N → psum a N + psum b N)
      incS N = +-mono (psum-inc a N) (psum-inc b N)

  ∑ᶠ-scale : ∀ c a → c * ∑ᶠ a ≈ ∑ᶠ (λ n → c * a n)
  ∑ᶠ-scale c a = trans (*-⨆ c (psum a) (psum-inc a) incC)
                       (⨆-cong incC (psum-inc _) (λ N → sym (psum-scale c a N)))
    where
      incC : Increasing (λ N → c * psum a N)
      incC N = *-mono c (psum-inc a N)

  psum-shift : ∀ a N → psum a (ℕ.suc N) ≈ a ℕ.zero + psum (λ n → a (ℕ.suc n)) N
  psum-shift a ℕ.zero = trans (+-identityˡ _) (sym (+-identityʳ _))
  psum-shift a (ℕ.suc N) = begin
    psum a (ℕ.suc N) + a (ℕ.suc N)                                   ≈⟨ +-cong (psum-shift a N) refl ⟩
    (a ℕ.zero + psum (λ n → a (ℕ.suc n)) N) + a (ℕ.suc N)            ≈⟨ +-assoc _ _ _ ⟩
    a ℕ.zero + (psum (λ n → a (ℕ.suc n)) N + a (ℕ.suc N))            ∎

  ∑ᶠ-shift : ∀ a → ∑ᶠ a ≈ a ℕ.zero + ∑ᶠ (λ n → a (ℕ.suc n))
  ∑ᶠ-shift a = trans (⨆-shift (psum a) (psum-inc a) incS)
                 (trans (⨆-cong incS incA (psum-shift a))
                        (sym (+-⨆ (a ℕ.zero) (psum (λ n → a (ℕ.suc n))) (psum-inc _) incA)))
    where
      incS : Increasing (λ n → psum a (ℕ.suc n))
      incS n = psum-inc a (ℕ.suc n)
      incA : Increasing (λ N → a ℕ.zero + psum (λ n → a (ℕ.suc n)) N)
      incA N = +-mono ≤-refl (psum-inc _ N)

  ----------------------------------------------------------------------------
  -- iterated sums

  -- finite iterated sum over the rectangle [0,N) × [0,M)
  psum2 : (ℕ → ℕ → ∣A∣) → ℕ → ℕ → ∣A∣
  psum2 a N M = psum (λ n → psum (a n) M) N

  psum2-incM : ∀ a N → Increasing (psum2 a N)
  psum2-incM a N M = psum-mono (λ n → psum-inc (a n) M) N

  psum2-incN : ∀ a M → Increasing (λ N → psum2 a N M)
  psum2-incN a M N = ≤-+ʳ

  -- finite sums commute with suprema
  psum-⨆ : ∀ a N → psum (λ n → ∑ᶠ (a n)) N ≈ ⨆ (psum2 a N) (psum2-incM a N)
  psum-⨆ a ℕ.zero = sym (⨆-const 0# (psum2-incM a ℕ.zero))
  psum-⨆ a (ℕ.suc N) = begin
    psum (λ n → ∑ᶠ (a n)) N + ∑ᶠ (a N)
      ≈⟨ +-cong (psum-⨆ a N) refl ⟩
    ⨆ (psum2 a N) (psum2-incM a N) + ⨆ (psum (a N)) (psum-inc (a N))
      ≈⟨ ⨆-+-diag (psum2-incM a N) (psum-inc (a N)) incS ⟩
    ⨆ (λ M → psum2 a N M + psum (a N) M) incS
      ≈⟨ ⨆-cong incS (psum2-incM a (ℕ.suc N)) (λ M → refl) ⟩
    ⨆ (psum2 a (ℕ.suc N)) (psum2-incM a (ℕ.suc N))   ∎
    where
      incS : Increasing (λ M → psum2 a N M + psum (a N) M)
      incS M = +-mono (psum2-incM a N M) (psum-inc (a N) M)

  rowsup : (ℕ → ℕ → ∣A∣) → ℕ → ∣A∣
  rowsup a N = ⨆ (psum2 a N) (psum2-incM a N)

  rowsup-inc : ∀ a → Increasing (rowsup a)
  rowsup-inc a N = ⨆-mono (psum2-incM a N) (psum2-incM a (ℕ.suc N)) (λ M → psum2-incN a M N)

  colsup : (ℕ → ℕ → ∣A∣) → ℕ → ∣A∣
  colsup a M = ⨆ (λ N → psum2 a N M) (psum2-incN a M)

  colsup-inc : ∀ a → Increasing (colsup a)
  colsup-inc a M = ⨆-mono (psum2-incN a M) (psum2-incN a (ℕ.suc M)) (λ N → psum2-incM a N M)

  -- ∑ₙ ∑ₘ aₙₘ is the supremum of the rectangle sums
  ∑ᶠ-rows : ∀ a → ∑ᶠ (λ n → ∑ᶠ (a n)) ≈ ⨆ (rowsup a) (rowsup-inc a)
  ∑ᶠ-rows a = ⨆-cong (psum-inc _) (rowsup-inc a) (psum-⨆ a)

  -- the supremum of rectangle sums over both indices, in either order
  ⨆⨆-swap : ∀ a → ⨆ (rowsup a) (rowsup-inc a) ≈ ⨆ (colsup a) (colsup-inc a)
  ⨆⨆-swap a = ≤-antisym
    (⨆-lub _ (rowsup-inc a) (λ N → ⨆-lub _ (psum2-incM a N) (λ M →
       ≤-trans (⨆-ub _ (psum2-incN a M) N) (⨆-ub _ (colsup-inc a) M))))
    (⨆-lub _ (colsup-inc a) (λ M → ⨆-lub _ (psum2-incN a M) (λ N →
       ≤-trans (⨆-ub _ (psum2-incM a N) M) (⨆-ub _ (rowsup-inc a) N))))

  -- finite rectangle sums commute
  psum2-flip : ∀ a N M → psum2 (λ n m → a m n) N M ≈ psum2 a M N
  psum2-flip a ℕ.zero M = sym (psum-zero (λ n → refl) M)
  psum2-flip a (ℕ.suc N) M = begin
    psum2 (λ n m → a m n) N M + psum (λ m → a m N) M
      ≈⟨ +-cong (psum2-flip a N M) refl ⟩
    psum2 a M N + psum (λ m → a m N) M
      ≈⟨ sym (psum-+ (λ n → psum (a n) N) (λ n → a n N) M) ⟩
    psum2 a M (ℕ.suc N)   ∎

  ∑ᶠ-swap : ∀ a → ∑ᶠ (λ n → ∑ᶠ (a n)) ≈ ∑ᶠ (λ m → ∑ᶠ (λ n → a n m))
  ∑ᶠ-swap a = trans (∑ᶠ-rows a) (trans (⨆⨆-swap a) (sym (trans (∑ᶠ-rows (λ m n → a n m)) flipped)))
    where
      flipped : ⨆ (rowsup (λ m n → a n m)) (rowsup-inc _) ≈ ⨆ (colsup a) (colsup-inc a)
      flipped = ⨆-cong (rowsup-inc _) (colsup-inc a) (λ N →
        ⨆-cong (psum2-incM _ N) (psum2-incN a N) (λ M → psum2-flip a N M))

  ----------------------------------------------------------------------------
  -- summing along the Cantor enumeration of ℕ × ℕ

  private
    ifD : ∀ {P : Set} → Dec P → ∣A∣ → ∣A∣ → ∣A∣
    ifD (yes _) x y = x
    ifD (no _) x y = y

    -- masks on the index of a sequence
    ne eq : ℕ → (ℕ → ∣A∣) → ℕ → ∣A∣
    ne x₀ b x = ifD (x ℕ.≟ x₀) 0# (b x)
    eq x₀ b x = ifD (x ℕ.≟ x₀) (b x) 0#

    mask-split : ∀ x₀ b x → b x ≈ ne x₀ b x + eq x₀ b x
    mask-split x₀ b x with x ℕ.≟ x₀
    ... | yes _ = sym (+-identityˡ _)
    ... | no _ = sym (+-identityʳ _)

    ne-other : ∀ x₀ b x → (x ≡.≡ x₀ → ⊥) → ne x₀ b x ≈ b x
    ne-other x₀ b x h with x ℕ.≟ x₀
    ... | yes p = ⊥-elim (h p)
    ... | no _ = refl

    eq-self : ∀ x₀ b → b x₀ ≈ eq x₀ b x₀
    eq-self x₀ b with x₀ ℕ.≟ x₀
    ... | yes _ = refl
    ... | no h = ⊥-elim (h ≡.refl)

    -- a sum along an injective map is bounded by the sum over any prefix containing the image
    inj-subsum : ∀ J (f : ℕ → ℕ) K →
      (∀ i j → i ℕ.< J → j ℕ.< J → f i ≡.≡ f j → i ≡.≡ j) →
      (∀ j → j ℕ.< J → f j ℕ.< K) →
      ∀ b → psum (λ j → b (f j)) J ≤ psum b K
    inj-subsum ℕ.zero f K inj bd b = 0-least
    inj-subsum (ℕ.suc J) f K inj bd b = ≤-trans (+-mono part₁ part₂)
        (≤-reflexive (trans (sym (psum-+ _ _ K)) (psum-cong split K)))
      where
        b′ = ne (f J) b
        b″ = eq (f J) b
        split : ∀ x → b′ x + b″ x ≈ b x
        split x = sym (mask-split (f J) b x)
        distinct : ∀ j → j ℕ.< J → f j ≡.≡ f J → ⊥
        distinct j j<J e = ℕ.<-irrefl (inj j J (ℕ.m<n⇒m<1+n j<J) (ℕ.n<1+n J) e) j<J
        part₁ : psum (λ j → b (f j)) J ≤ psum b′ K
        part₁ = ≤-trans (≤-reflexive (psum-cong-lt J (λ j j<J → sym (ne-other (f J) b (f j) (distinct j j<J)))))
                  (inj-subsum J f K (λ i j i<J j<J → inj i j (ℕ.m<n⇒m<1+n i<J) (ℕ.m<n⇒m<1+n j<J))
                    (λ j j<J → bd j (ℕ.m<n⇒m<1+n j<J)) b′)
        part₂ : b (f J) ≤ psum b″ K
        part₂ = ≤-trans (≤-reflexive (eq-self (f J) b)) (term-≤-psum b″ (bd J (ℕ.n<1+n J)))

    -- masks on grid points
    rowzero rowonly : ℕ → (ℕ → ℕ → ∣A∣) → ℕ → ℕ → ∣A∣
    rowzero N c n m = ifD (n ℕ.≟ N) 0# (c n m)
    rowonly N c n m = ifD (n ℕ.≟ N) (c n m) 0#

    rowsplit : ∀ N c n m → c n m ≈ rowzero N c n m + rowonly N c n m
    rowsplit N c n m with n ℕ.≟ N
    ... | yes _ = sym (+-identityˡ _)
    ... | no _ = sym (+-identityʳ _)

    rowzero-other : ∀ N c n m → (n ≡.≡ N → ⊥) → rowzero N c n m ≈ c n m
    rowzero-other N c n m h with n ℕ.≟ N
    ... | yes p = ⊥-elim (h p)
    ... | no _ = refl

    rowonly-self : ∀ N c m → rowonly N c N m ≈ c N m
    rowonly-self N c m with N ℕ.≟ N
    ... | yes _ = refl
    ... | no h = ⊥-elim (h ≡.refl)

    ptzero ptonly : ℕ → ℕ → (ℕ → ℕ → ∣A∣) → ℕ → ℕ → ∣A∣
    ptzero n₀ m₀ c n m = ifD (n ℕ.≟ n₀) (ifD (m ℕ.≟ m₀) 0# (c n m)) (c n m)
    ptonly n₀ m₀ c n m = ifD (n ℕ.≟ n₀) (ifD (m ℕ.≟ m₀) (c n m) 0#) 0#

    ptsplit : ∀ n₀ m₀ c n m → c n m ≈ ptzero n₀ m₀ c n m + ptonly n₀ m₀ c n m
    ptsplit n₀ m₀ c n m with n ℕ.≟ n₀
    ... | no _ = sym (+-identityʳ _)
    ... | yes _ with m ℕ.≟ m₀
    ...   | yes _ = sym (+-identityˡ _)
    ...   | no _ = sym (+-identityʳ _)

    ptzero-other : ∀ n₀ m₀ c n m → (n ≡.≡ n₀ → m ≡.≡ m₀ → ⊥) → ptzero n₀ m₀ c n m ≈ c n m
    ptzero-other n₀ m₀ c n m h with n ℕ.≟ n₀
    ... | no _ = refl
    ... | yes p with m ℕ.≟ m₀
    ...   | yes q = ⊥-elim (h p q)
    ...   | no _ = refl

    ptonly-self : ∀ n₀ m₀ c → ptonly n₀ m₀ c n₀ m₀ ≈ c n₀ m₀
    ptonly-self n₀ m₀ c with n₀ ℕ.≟ n₀
    ... | no h = ⊥-elim (h ≡.refl)
    ... | yes _ with m₀ ℕ.≟ m₀
    ...   | yes _ = refl
    ...   | no h = ⊥-elim (h ≡.refl)

    psum2-cong : ∀ {a b} → (∀ n m → a n m ≈ b n m) → ∀ N M → psum2 a N M ≈ psum2 b N M
    psum2-cong e N M = psum-cong (λ n → psum-cong (e n) M) N

    psum2-cong-lt : ∀ {a b} N M → (∀ n m → n ℕ.< N → a n m ≈ b n m) → psum2 a N M ≈ psum2 b N M
    psum2-cong-lt N M e = psum-cong-lt N (λ n n<N → psum-cong (λ m → e n m n<N) M)

    psum2-+ : ∀ a b N M → psum2 (λ n m → a n m + b n m) N M ≈ psum2 a N M + psum2 b N M
    psum2-+ a b N M = trans (psum-cong (λ n → psum-+ (a n) (b n) M) N)
                            (psum-+ (λ n → psum (a n) M) (λ n → psum (b n) M) N)

    term2-≤ : ∀ a {n m N M} → n ℕ.< N → m ℕ.< M → a n m ≤ psum2 a N M
    term2-≤ a {n} {m} {N} {M} n<N m<M = ≤-trans (term-≤-psum (a n) m<M) (term-≤-psum (λ n′ → psum (a n′) M) n<N)

    unpair-inj : ∀ {i j} → unpair i ≡.≡ unpair j → i ≡.≡ j
    unpair-inj {i} {j} e = ≡.trans (≡.sym (pair-unpair i)) (≡.trans (≡.cong pair′ e) (pair-unpair j))

    enum : (ℕ → ℕ → ∣A∣) → ℕ → ∣A∣
    enum a k = a (proj₁ (unpair k)) (proj₂ (unpair k))

    bound-comp : ∀ K → Σ ℕ (λ B → ∀ k → k ℕ.< K → proj₁ (unpair k) ℕ.< B × proj₂ (unpair k) ℕ.< B)
    bound-comp ℕ.zero = ℕ.zero , (λ k ())
    bound-comp (ℕ.suc K) with bound-comp K
    ... | B , h = ℕ.suc ((B ℕ.⊔ proj₁ (unpair K)) ℕ.⊔ proj₂ (unpair K)) , step
      where
        up : ∀ x → x ℕ.≤ B → x ℕ.< ℕ.suc ((B ℕ.⊔ proj₁ (unpair K)) ℕ.⊔ proj₂ (unpair K))
        up x le = ℕ.s≤s (ℕ.≤-trans le (ℕ.≤-trans (ℕ.m≤m⊔n B _) (ℕ.m≤m⊔n _ _)))
        step : ∀ k → k ℕ.< ℕ.suc K → _
        step k k<sK with k ℕ.≟ K
        ... | no k≢K = let k<K = ℕ.≤∧≢⇒< (ℕ.s≤s⁻¹ k<sK) k≢K
                           (l , r) = h k k<K
                       in up _ (ℕ.<⇒≤ l) , up _ (ℕ.<⇒≤ r)
        ... | yes ≡.refl =
              ℕ.s≤s (ℕ.≤-trans (ℕ.m≤n⊔m B _) (ℕ.m≤m⊔n _ _)) , ℕ.s≤s (ℕ.m≤n⊔m _ _)

    row-bound : ∀ N M → Σ ℕ (λ K → ∀ m → m ℕ.< M → pair N m ℕ.< K)
    row-bound N ℕ.zero = ℕ.zero , (λ m ())
    row-bound N (ℕ.suc M) with row-bound N M
    ... | K , h = ℕ.suc (K ℕ.⊔ pair N M) , step
      where
        step : ∀ m → m ℕ.< ℕ.suc M → pair N m ℕ.< ℕ.suc (K ℕ.⊔ pair N M)
        step m m<sM with m ℕ.≟ M
        ... | yes ≡.refl = ℕ.s≤s (ℕ.m≤n⊔m K _)
        ... | no m≢M = ℕ.s≤s (ℕ.≤-trans (ℕ.<⇒≤ (h m (ℕ.≤∧≢⇒< (ℕ.s≤s⁻¹ m<sM) m≢M))) (ℕ.m≤m⊔n K _))

    -- a prefix of the enumeration is bounded by a big enough rectangle
    dirA : ∀ K B → (∀ k → k ℕ.< K → proj₁ (unpair k) ℕ.< B × proj₂ (unpair k) ℕ.< B) →
      ∀ c → psum (enum c) K ≤ psum2 c B B
    dirA ℕ.zero B bd c = 0-least
    dirA (ℕ.suc K) B bd c = ≤-trans (+-mono part₁ part₂) (≤-reflexive total)
      where
        n₀ = proj₁ (unpair K)
        m₀ = proj₂ (unpair K)
        c° = ptzero n₀ m₀ c
        cₚ = ptonly n₀ m₀ c
        bd₀ = bd K (ℕ.n<1+n K)
        distinct : ∀ k → k ℕ.< K → proj₁ (unpair k) ≡.≡ n₀ → proj₂ (unpair k) ≡.≡ m₀ → ⊥
        distinct k k<K p q = ℕ.<-irrefl (unpair-inj (≡.cong₂ _,_ p q)) k<K
        part₁ : psum (enum c) K ≤ psum2 c° B B
        part₁ = ≤-trans
          (≤-reflexive (psum-cong-lt K (λ k k<K → sym (ptzero-other n₀ m₀ c _ _ (distinct k k<K)))))
          (dirA K B (λ k k<K → bd k (ℕ.m<n⇒m<1+n k<K)) c°)
        part₂ : enum c K ≤ psum2 cₚ B B
        part₂ = ≤-trans (≤-reflexive (sym (ptonly-self n₀ m₀ c))) (term2-≤ cₚ (proj₁ bd₀) (proj₂ bd₀))
        total : psum2 c° B B + psum2 cₚ B B ≈ psum2 c B B
        total = trans (sym (psum2-+ c° cₚ B B)) (sym (psum2-cong (ptsplit n₀ m₀ c) B B))

    -- a rectangle is bounded by a big enough prefix of the enumeration
    dirB : ∀ M N → Σ ℕ (λ K → ∀ c → psum2 c N M ≤ psum (enum c) K)
    dirB M ℕ.zero = ℕ.zero , (λ c → ≤-refl)
    dirB M (ℕ.suc N) with dirB M N | row-bound N M
    ... | K₁ , h | K₂ , r = K₁ ℕ.⊔ K₂ , λ c → ≤-trans (+-mono (part₁ c) (part₂ c)) (≤-reflexive (total c))
      where
        K = K₁ ℕ.⊔ K₂
        eᵒ : (ℕ → ℕ → ∣A∣) → ℕ → ∣A∣
        eᵒ c = enum (rowzero N c)
        eʳ : (ℕ → ℕ → ∣A∣) → ℕ → ∣A∣
        eʳ c = enum (rowonly N c)
        inj-snd : ∀ i j → pair N i ≡.≡ pair N j → i ≡.≡ j
        inj-snd i j e = ≡.cong proj₂ (≡.trans (≡.sym (unpair-pair N i)) (≡.trans (≡.cong unpair e) (unpair-pair N j)))
        rowb : ∀ c m → eʳ c (pair N m) ≈ c N m
        rowb c m = trans (reflexive (≡.cong₂ (rowonly N c) (≡.cong proj₁ (unpair-pair N m)) (≡.cong proj₂ (unpair-pair N m))))
                         (rowonly-self N c m)
        part₁ : ∀ c → psum2 c N M ≤ psum (eᵒ c) K
        part₁ c = ≤-trans
          (≤-reflexive (psum2-cong-lt N M (λ n m n<N → sym (rowzero-other N c n m (λ p → ℕ.<-irrefl p n<N)))))
          (≤-trans (h (rowzero N c)) (psum-index-mono (eᵒ c) (ℕ.m≤m⊔n K₁ K₂)))
        part₂ : ∀ c → psum (c N) M ≤ psum (eʳ c) K
        part₂ c = ≤-trans (≤-reflexive (psum-cong (λ m → sym (rowb c m)) M))
          (≤-trans (inj-subsum M (pair N) K₂ (λ i j _ _ → inj-snd i j) r (eʳ c))
                   (psum-index-mono (eʳ c) (ℕ.m≤n⊔m K₁ K₂)))
        total : ∀ c → psum (eᵒ c) K + psum (eʳ c) K ≈ psum (enum c) K
        total c = trans (sym (psum-+ (eᵒ c) (eʳ c) K))
                        (psum-cong (λ k → sym (rowsplit N c (proj₁ (unpair k)) (proj₂ (unpair k)))) K)

  -- Tonelli along the Cantor enumeration
  ∑ᶠ-pair : ∀ a → ∑ᶠ (λ n → ∑ᶠ (a n)) ≈ ∑ᶠ (λ k → a (proj₁ (unpair k)) (proj₂ (unpair k)))
  ∑ᶠ-pair a = ≤-antisym lhs≤rhs rhs≤lhs
    where
      lhs≤rhs : ∑ᶠ (λ n → ∑ᶠ (a n)) ≤ ∑ᶠ (enum a)
      lhs≤rhs = ≤-trans (≤-reflexive (∑ᶠ-rows a))
        (⨆-lub _ (rowsup-inc a) (λ N → ⨆-lub _ (psum2-incM a N) (λ M →
          let K , h = dirB M N in ≤-trans (h a) (psum≤∑ᶠ (enum a) K))))
      rhs≤lhs : ∑ᶠ (enum a) ≤ ∑ᶠ (λ n → ∑ᶠ (a n))
      rhs≤lhs = ∑ᶠ-lub (λ K →
        let B , bd = bound-comp K in
        ≤-trans (dirA K B bd a)
          (≤-trans (⨆-ub _ (psum2-incM a B) B)
            (≤-trans (⨆-ub _ (rowsup-inc a) B) (≤-reflexive (sym (∑ᶠ-rows a))))))
