{-# OPTIONS --safe --without-K #-}

-- Integration of unbounded measurable functions `R → [0,∞]` against a (sub-probability) measure,
-- by dyadic truncation.  With `pw k = 2ᵏ` and `tr k a = 2⁻ᵏ · min (a, 2ᵏ)` (values in [0,1]):
--   FunInf h  :=  every truncation `tr k ∘ h` is a bounded measurable function (`Fun`),
--   Iinf m h  :=  ⨆ₖ 2ᵏ · ∫ (tr k ∘ h) dm.
-- Since `FunInf` is a predicate on values and `I` ignores the proof of measurability (`I-cong`),
-- `Iinf` does not depend on any choice of representation.  We prove that it extends `I`, is
-- monotone and additive, and satisfies monotone convergence.  Abstract in an `Arch` semiring with a
-- `Min` (for lower cuts: intersection, `Analysis/LowerRealsMin`); the only inputs are the
-- properties of `min` listed in `Analysis/Min`.
module QBS.Analysis.Unbounded where

open import Level using (zero; suc)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega
open import QBS.Analysis.Fun
open import QBS.Analysis.Measure
open import QBS.Analysis.Archimedean using (Arch; module ArchLemmas)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Min

module Unbounded (A : OmegaSemiring (suc zero)) (R : Arch A) (M : Min A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R
  open ArchLemmas R using (hp-≤)
  open HalfOrder A R using (half≤1; half-twice)
  open Min M
  open Measurable A
  open Integration A
  open Series A using (⨆-+-diag)
  open SetoidReasoning setoid
  private S = R₁

  ----------------------------------------------------------------------------
  -- the dyadic truncations

  -- 2ᵏ
  pw : ℕ → ∣A∣
  pw ℕ.zero = 1#
  pw (ℕ.suc k) = pw k + pw k

  hp-pw : ∀ k → hp k * pw k ≈ 1#
  hp-pw ℕ.zero = trans (*-identityʳ _) hp-zero
  hp-pw (ℕ.suc k) = begin
    hp (ℕ.suc k) * (pw k + pw k)                 ≈⟨ distribˡ _ _ _ ⟩
    hp (ℕ.suc k) * pw k + hp (ℕ.suc k) * pw k   ≈⟨ sym (distribʳ (pw k) (hp (ℕ.suc k)) (hp (ℕ.suc k))) ⟩
    (hp (ℕ.suc k) + hp (ℕ.suc k)) * pw k         ≈⟨ *-cong (hp-double k) refl ⟩
    hp k * pw k                                  ≈⟨ hp-pw k ⟩
    1# ∎

  hp≤1 : ∀ k → hp k ≤ 1#
  hp≤1 ℕ.zero = ≤-reflexive hp-zero
  hp≤1 (ℕ.suc k) = ≤-trans (hp-≤ k) (hp≤1 k)

  pw-≤ : ∀ k → pw k ≤ pw (ℕ.suc k)
  pw-≤ k = ≤-+ʳ

  1≤pw : ∀ k → 1# ≤ pw k
  1≤pw ℕ.zero = ≤-refl
  1≤pw (ℕ.suc k) = ≤-trans (1≤pw k) (pw-≤ k)

  mn-mono : ∀ {a a′ b b′} → a ≤ a′ → b ≤ b′ → mn a b ≤ mn a′ b′
  mn-mono p q = mn-glb (≤-trans mn-≤l p) (≤-trans mn-≤r q)

  mn-cong : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → mn a b ≈ mn a′ b′
  mn-cong p q = ≤-antisym (mn-mono (≤-reflexive p) (≤-reflexive q))
                          (mn-mono (≤-reflexive (sym p)) (≤-reflexive (sym q)))

  mn-self : ∀ {a b} → a ≤ b → mn a b ≈ a
  mn-self le = ≤-antisym mn-≤l (mn-glb ≤-refl le)

  -- tr k a = 2⁻ᵏ · min (a, 2ᵏ)
  tr : ℕ → ∣A∣ → ∣A∣
  tr k a = hp k * mn a (pw k)

  tr-≤1 : ∀ k a → tr k a ≤ 1#
  tr-≤1 k a = ≤-trans (*-mono (hp k) mn-≤r) (≤-reflexive (hp-pw k))

  tr-mono : ∀ k {a b} → a ≤ b → tr k a ≤ tr k b
  tr-mono k le = *-mono (hp k) (mn-mono le ≤-refl)

  tr-cong : ∀ k {a b} → a ≈ b → tr k a ≈ tr k b
  tr-cong k e = *-cong refl (mn-cong e refl)

  tr-bounded : ∀ k {a} → a ≤ 1# → tr k a ≈ hp k * a
  tr-bounded k a≤1 = *-cong refl (mn-self (≤-trans a≤1 (1≤pw k)))

  tr-⨆ : ∀ k c (inc : Increasing c) (inc′ : Increasing (λ n → tr k (c n))) →
    tr k (⨆ c inc) ≈ ⨆ (λ n → tr k (c n)) inc′
  tr-⨆ k c inc inc′ = ≤-antisym
    (≤-trans (*-mono (hp k) (mn-⨆ c inc (pw k) incM))
      (≤-reflexive (*-⨆ (hp k) (λ n → mn (c n) (pw k)) incM inc′)))
    (⨆-lub _ inc′ (λ n → tr-mono k (⨆-ub c inc n)))
    where
      incM : Increasing (λ n → mn (c n) (pw k))
      incM n = mn-mono (inc n) ≤-refl

  -- halving relates consecutive truncations
  half-hp : ∀ k → half * hp k ≈ hp (ℕ.suc k)
  half-hp k = trans (*-cong refl (sym (hp-double k))) (half-twice _)

  half-tr-eq : ∀ k a → half * tr k a ≈ hp (ℕ.suc k) * mn a (pw k)
  half-tr-eq k a = trans (sym (*-assoc half (hp k) (mn a (pw k)))) (*-cong (half-hp k) refl)

  half-tr : ∀ k a → half * tr k a ≤ tr (ℕ.suc k) a
  half-tr k a = ≤-trans (≤-reflexive (half-tr-eq k a))
    (*-mono (hp (ℕ.suc k)) (mn-mono ≤-refl (pw-≤ k)))

  -- additivity of the truncations, up to a factor ½
  tr-add-lo : ∀ k a b → half * tr k a + half * tr k b ≤ tr (ℕ.suc k) (a + b)
  tr-add-lo k a b = ≤-trans
    (≤-reflexive (trans (+-cong (half-tr-eq k a) (half-tr-eq k b)) (sym (distribˡ _ _ _))))
    (*-mono (hp (ℕ.suc k)) (mn-glb (+-mono mn-≤l mn-≤l) (+-mono mn-≤r mn-≤r)))

  tr-add-hi : ∀ k a b → tr k (a + b) ≤ tr k a + tr k b
  tr-add-hi k a b = ≤-trans (*-mono (hp k) mn-add) (≤-reflexive (distribˡ _ _ _))

  ----------------------------------------------------------------------------
  -- unbounded measurable functions and their integral

  FunInf : (S → ∣A∣) → Set₁
  FunInf h = ∀ k → Fun (λ x → tr k (h x))

  -- bounded functions are measurable
  FunInf-bounded : ∀ {h} → Fun h → FunInf h
  FunInf-bounded f k = Fun-ext (λ x → sym (tr-bounded k (Fun-≤1 f x))) (Fun-scale (hp k) (hp≤1 k) f)

  -- suprema of increasing sequences of measurable functions are measurable
  FunInf-sup : ∀ {h} (hs : ℕ → S → ∣A∣) (fs : ∀ n → FunInf (hs n))
    (inc : ∀ x → Increasing (λ n → hs n x)) → (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) → FunInf h
  FunInf-sup hs fs inc e k = supF (λ n x → tr k (hs n x)) (λ n → fs n k) (λ x n → tr-mono k (inc x n))
    (λ x → trans (tr-cong k (e x)) (tr-⨆ k (λ n → hs n x) (inc x) (λ n → tr-mono k (inc x n))))

  -- 2ᵏ⁺¹ · ½ x = 2ᵏ x
  half-pw : ∀ k x → pw (ℕ.suc k) * (half * x) ≈ pw k * x
  half-pw k x = begin
    pw (ℕ.suc k) * (half * x)   ≈⟨ sym (*-assoc _ _ _) ⟩
    (pw (ℕ.suc k) * half) * x   ≈⟨ *-cong (*-comm _ _) refl ⟩
    (half * pw (ℕ.suc k)) * x   ≈⟨ *-cong (half-twice (pw k)) refl ⟩
    pw k * x ∎

  pw-half-sum : ∀ k x y → pw (ℕ.suc k) * (half * x + half * y) ≈ pw k * x + pw k * y
  pw-half-sum k x y = trans (distribˡ _ _ _) (+-cong (half-pw k x) (half-pw k y))

  -- the k-th approximation 2ᵏ ∫ tr k h
  Iseq : Measure → ∀ h → FunInf h → ℕ → ∣A∣
  Iseq m h f k = pw k * I m (λ x → tr k (h x)) (f k)

  Itr-step : ∀ m h (f : FunInf h) k →
    half * I m (λ x → tr k (h x)) (f k) ≤ I m (λ x → tr (ℕ.suc k) (h x)) (f (ℕ.suc k))
  Itr-step m h f k = ≤-trans
    (≤-reflexive (sym (I-scale m half (f k) (Fun-scale half half≤1 (f k)) (λ x → refl))))
    (I-mono m (Fun-scale half half≤1 (f k)) (f (ℕ.suc k)) (λ x → half-tr k (h x)))

  Iseq-inc : ∀ m h (f : FunInf h) → Increasing (Iseq m h f)
  Iseq-inc m h f k = ≤-trans
    (≤-reflexive (sym (half-pw k (I m (λ x → tr k (h x)) (f k)))))
    (*-mono (pw (ℕ.suc k)) (Itr-step m h f k))

  -- the extended integral
  Iinf : Measure → ∀ h → FunInf h → ∣A∣
  Iinf m h f = ⨆ (Iseq m h f) (Iseq-inc m h f)

  Iseq-le : ∀ m {h} (f : FunInf h) k → Iseq m h f k ≤ Iinf m h f
  Iseq-le m f k = ⨆-ub _ (Iseq-inc m _ f) k

  -- it extends the bounded integral
  Iseq-bounded : ∀ m {h} (f : Fun h) (f∞ : FunInf h) k → Iseq m h f∞ k ≈ I m h f
  Iseq-bounded m {h} f f∞ k = begin
    pw k * I m (λ x → tr k (h x)) (f∞ k)  ≈⟨ *-cong refl (I-cong m (λ x → tr-bounded k (Fun-≤1 f x)) (f∞ k) fs) ⟩
    pw k * I m (λ x → hp k * h x) fs      ≈⟨ *-cong refl (I-scale m (hp k) f fs (λ x → refl)) ⟩
    pw k * (hp k * I m h f)               ≈⟨ sym (*-assoc _ _ _) ⟩
    (pw k * hp k) * I m h f               ≈⟨ *-cong (trans (*-comm _ _) (hp-pw k)) refl ⟩
    1# * I m h f                          ≈⟨ *-identityˡ _ ⟩
    I m h f ∎
    where fs = Fun-scale (hp k) (hp≤1 k) f

  Iinf-bounded : ∀ (m : Measure) {h} (f : Fun h) (f∞ : FunInf h) → Iinf m h f∞ ≈ I m h f
  Iinf-bounded m f f∞ = trans (⨆-cong (Iseq-inc m _ f∞) (λ _ → ≤-refl) (Iseq-bounded m f f∞))
                              (⨆-const _ (λ _ → ≤-refl))

  Iinf-mono : ∀ (m : Measure) {h h′} (f : FunInf h) (f′ : FunInf h′) → (∀ x → h x ≤ h′ x) →
    Iinf m h f ≤ Iinf m h′ f′
  Iinf-mono m f f′ le = ⨆-lub _ _ (λ k →
    ≤-trans (*-mono (pw k) (I-mono m (f k) (f′ k) (λ x → tr-mono k (le x)))) (Iseq-le m f′ k))

  -- monotone convergence
  Iinf-sup : ∀ (m : Measure) {h} (hs : ℕ → S → ∣A∣) (fs : ∀ n → FunInf (hs n))
    (inc : ∀ x → Increasing (λ n → hs n x)) (f : FunInf h) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
    Iinf m h f ≈ ⨆ (λ n → Iinf m (hs n) (fs n)) (λ n → Iinf-mono m (fs n) (fs (ℕ.suc n)) (λ x → inc x n))
  Iinf-sup m {h} hs fs inc f e = ≤-antisym (⨆-lub _ _ bound)
    (⨆-lub _ _ (λ n → Iinf-mono m (fs n) f (λ x → ≤-trans (⨆-ub (λ n → hs n x) (inc x) n) (≤-reflexive (sym (e x))))))
    where
      incI : ∀ k → ∀ n → I m (λ x → tr k (hs n x)) (fs n k) ≤ I m (λ x → tr k (hs (ℕ.suc n) x)) (fs (ℕ.suc n) k)
      incI k n = I-mono m (fs n k) (fs (ℕ.suc n) k) (λ x → tr-mono k (inc x n))

      incK : ∀ k → Increasing (λ n → pw k * I m (λ x → tr k (hs n x)) (fs n k))
      incK k n = *-mono (pw k) (incI k n)

      step : ∀ k → Iseq m h f k ≈ ⨆ (λ n → pw k * I m (λ x → tr k (hs n x)) (fs n k)) (incK k)
      step k = trans
        (*-cong refl (I-sup m (λ n x → tr k (hs n x)) (λ n → fs n k) (λ x n → tr-mono k (inc x n)) (f k)
          (λ x → trans (tr-cong k (e x)) (tr-⨆ k (λ n → hs n x) (inc x) (λ n → tr-mono k (inc x n))))))
        (*-⨆ (pw k) _ (incI k) (incK k))

      bound : ∀ k → Iseq m h f k ≤ ⨆ (λ n → Iinf m (hs n) (fs n)) (λ n → Iinf-mono m (fs n) (fs (ℕ.suc n)) (λ x → inc x n))
      bound k = ≤-trans (≤-reflexive (step k))
        (⨆-lub _ (incK k) (λ n → ≤-trans (Iseq-le m (fs n) k)
          (⨆-ub _ (λ n → Iinf-mono m (fs n) (fs (ℕ.suc n)) (λ x → inc x n)) n)))

  -- additivity
  Iinf-add : ∀ (m : Measure) {h h₁ h₂} (f : FunInf h) (f₁ : FunInf h₁) (f₂ : FunInf h₂) →
    (∀ x → h x ≈ h₁ x + h₂ x) → Iinf m h f ≈ Iinf m h₁ f₁ + Iinf m h₂ f₂
  Iinf-add m {h} {h₁} {h₂} f f₁ f₂ e = trans (≤-antisym
    (⨆-lub _ _ (λ k → ≤-trans (lo k) (⨆-ub _ incP k)))
    (⨆-lub _ incP hi))
    (sym (⨆-+-diag (Iseq-inc m h₁ f₁) (Iseq-inc m h₂ f₂) incP))
    where
      P : ℕ → ∣A∣
      P k = Iseq m h₁ f₁ k + Iseq m h₂ f₂ k

      incP : Increasing P
      incP k = +-mono (Iseq-inc m h₁ f₁ k) (Iseq-inc m h₂ f₂ k)

      -- the half-weighted sum of the two truncations is again bounded
      u : ℕ → S → ∣A∣
      u k x = half * tr k (h₁ x) + half * tr k (h₂ x)

      F₁ : ∀ k → Fun (λ x → half * tr k (h₁ x))
      F₁ k = Fun-scale half half≤1 (f₁ k)
      F₂′ : ∀ k → Fun (λ x → half * tr k (h₂ x))
      F₂′ k = Fun-scale half half≤1 (f₂ k)

      u≤1 : ∀ k x → u k x ≤ 1#
      u≤1 k x = ≤-trans (+-mono (*-mono half (tr-≤1 k (h₁ x))) (*-mono half (tr-≤1 k (h₂ x))))
        (≤-reflexive (trans (+-cong (*-identityʳ half) (*-identityʳ half)) half+half))

      Fu : ∀ k → Fun (u k)
      Fu k = sumF (F₁ k) (F₂′ k) (λ x → refl) (u≤1 k)

      Iu : ∀ k → I m (u k) (Fu k) ≈
        half * I m (λ x → tr k (h₁ x)) (f₁ k) + half * I m (λ x → tr k (h₂ x)) (f₂ k)
      Iu k = trans (I-add m (Fu k) (F₁ k) (F₂′ k) (λ x → refl))
        (+-cong (I-scale m half (f₁ k) (F₁ k) (λ x → refl)) (I-scale m half (f₂ k) (F₂′ k) (λ x → refl)))

      -- P k ≤ Iseq (k+1): half (t₁ + t₂) ≤ t_{k+1}(h₁ + h₂)
      hi : ∀ k → P k ≤ Iinf m h f
      hi k = ≤-trans
        (≤-reflexive (sym (trans (*-cong refl (Iu k)) (pw-half-sum k _ _))))
        (≤-trans (*-mono (pw (ℕ.suc k)) (I-mono m (Fu k) (f (ℕ.suc k))
            (λ x → ≤-trans (tr-add-lo k (h₁ x) (h₂ x)) (≤-reflexive (tr-cong (ℕ.suc k) (sym (e x)))))))
          (Iseq-le m f (ℕ.suc k)))

      -- Iseq k ≤ P k: t_k(h₁ + h₂) ≤ t_k h₁ + t_k h₂
      lo : ∀ k → Iseq m h f k ≤ P k
      lo k = ≤-trans
        (≤-reflexive (sym (half-pw k (I m (λ x → tr k (h x)) (f k)))))
        (≤-trans (*-mono (pw (ℕ.suc k)) (≤-trans
            (≤-reflexive (sym (I-scale m half (f k) (Fun-scale half half≤1 (f k)) (λ x → refl))))
            (≤-trans (I-mono m (Fun-scale half half≤1 (f k)) (Fu k) (λ x →
                ≤-trans (*-mono half (≤-trans (≤-reflexive (tr-cong k (e x))) (tr-add-hi k (h₁ x) (h₂ x))))
                        (≤-reflexive (distribˡ half _ _))))
              (≤-reflexive (Iu k)))))
          (≤-reflexive (pw-half-sum k _ _)))
