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
  open Pow A public
  open Measurable A
  open Integration A
  open Series A using (⨆-+-diag)
  open SetoidReasoning setoid
  private S = R₁

  ----------------------------------------------------------------------------
  -- the dyadic truncations

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
  -- the half-weighted sum of the two truncations is again bounded
  private
    hsum : ℕ → ∀ {h₁ h₂} → FunInf h₁ → FunInf h₂ → S → ∣A∣
    hsum k {h₁} {h₂} _ _ x = half * tr k (h₁ x) + half * tr k (h₂ x)

    hsum-fun : ∀ k {h₁ h₂} (f₁ : FunInf h₁) (f₂ : FunInf h₂) → Fun (hsum k f₁ f₂)
    hsum-fun k {h₁} {h₂} f₁ f₂ = sumF (Fun-scale half half≤1 (f₁ k)) (Fun-scale half half≤1 (f₂ k)) (λ x → refl)
      (λ x → ≤-trans (+-mono (*-mono half (tr-≤1 k (h₁ x))) (*-mono half (tr-≤1 k (h₂ x))))
        (≤-reflexive (trans (+-cong (*-identityʳ half) (*-identityʳ half)) half+half)))

    hsum-I : ∀ m k {h₁ h₂} (f₁ : FunInf h₁) (f₂ : FunInf h₂) → I m (hsum k f₁ f₂) (hsum-fun k f₁ f₂) ≈
      half * I m (λ x → tr k (h₁ x)) (f₁ k) + half * I m (λ x → tr k (h₂ x)) (f₂ k)
    hsum-I m k f₁ f₂ = trans (I-add m (hsum-fun k f₁ f₂) (Fun-scale half half≤1 (f₁ k)) (Fun-scale half half≤1 (f₂ k)) (λ x → refl))
      (+-cong (I-scale m half (f₁ k) (Fun-scale half half≤1 (f₁ k)) (λ x → refl))
              (I-scale m half (f₂ k) (Fun-scale half half≤1 (f₂ k)) (λ x → refl)))

    -- P k ≤ Iseq (k+1): half (t₁ + t₂) ≤ t_{k+1}(h₁ + h₂)
    add-hi : ∀ m {h h₁ h₂} (f : FunInf h) (f₁ : FunInf h₁) (f₂ : FunInf h₂) → (∀ x → h x ≈ h₁ x + h₂ x) →
      ∀ k → Iseq m h₁ f₁ k + Iseq m h₂ f₂ k ≤ Iinf m h f
    add-hi m {h} {h₁} {h₂} f f₁ f₂ e k = ≤-trans
      (≤-reflexive (sym (trans (*-cong refl (hsum-I m k f₁ f₂)) (pw-half-sum k _ _))))
      (≤-trans (*-mono (pw (ℕ.suc k)) (I-mono m (hsum-fun k f₁ f₂) (f (ℕ.suc k))
          (λ x → ≤-trans (tr-add-lo k (h₁ x) (h₂ x)) (≤-reflexive (tr-cong (ℕ.suc k) (sym (e x)))))))
        (Iseq-le m f (ℕ.suc k)))

    -- Iseq k ≤ P k: t_k(h₁ + h₂) ≤ t_k h₁ + t_k h₂
    add-lo : ∀ m {h h₁ h₂} (f : FunInf h) (f₁ : FunInf h₁) (f₂ : FunInf h₂) → (∀ x → h x ≈ h₁ x + h₂ x) →
      ∀ k → Iseq m h f k ≤ Iseq m h₁ f₁ k + Iseq m h₂ f₂ k
    add-lo m {h} {h₁} {h₂} f f₁ f₂ e k = ≤-trans
      (≤-reflexive (sym (half-pw k (I m (λ x → tr k (h x)) (f k)))))
      (≤-trans (*-mono (pw (ℕ.suc k)) (≤-trans
          (≤-reflexive (sym (I-scale m half (f k) (Fun-scale half half≤1 (f k)) (λ x → refl))))
          (≤-trans (I-mono m (Fun-scale half half≤1 (f k)) (hsum-fun k f₁ f₂) (λ x →
              ≤-trans (*-mono half (≤-trans (≤-reflexive (tr-cong k (e x))) (tr-add-hi k (h₁ x) (h₂ x))))
                      (≤-reflexive (distribˡ half _ _))))
            (≤-reflexive (hsum-I m k f₁ f₂)))))
        (≤-reflexive (pw-half-sum k _ _)))

  Iinf-add : ∀ (m : Measure) {h h₁ h₂} (f : FunInf h) (f₁ : FunInf h₁) (f₂ : FunInf h₂) →
    (∀ x → h x ≈ h₁ x + h₂ x) → Iinf m h f ≈ Iinf m h₁ f₁ + Iinf m h₂ f₂
  Iinf-add m {h} {h₁} {h₂} f f₁ f₂ e = trans (≤-antisym
    (⨆-lub _ _ (λ k → ≤-trans (add-lo m {h} {h₁} {h₂} f f₁ f₂ e k) (⨆-ub _ incP k)))
    (⨆-lub _ incP (add-hi m f f₁ f₂ e)))
    (sym (⨆-+-diag (Iseq-inc m h₁ f₁) (Iseq-inc m h₂ f₂) incP))
    where
      P : ℕ → ∣A∣
      P k = Iseq m h₁ f₁ k + Iseq m h₂ f₂ k

      incP : Increasing P
      incP k = +-mono (Iseq-inc m h₁ f₁ k) (Iseq-inc m h₂ f₂ k)

  ----------------------------------------------------------------------------
  -- linearity: Iinf (c · φ) = c · Iinf φ for every constant c ∈ [0,∞]

  -- the value does not depend on the witness of measurability
  Iinf-irrel : ∀ m {h} (f f′ : FunInf h) → Iinf m h f ≈ Iinf m h f′
  Iinf-irrel m f f′ = ⨆-cong (Iseq-inc m _ f) (Iseq-inc m _ f′)
    (λ k → *-cong refl (I-cong m (λ x → refl) (f k) (f′ k)))

  Iinf-cong : ∀ m {h h′} (f : FunInf h) (f′ : FunInf h′) → (∀ x → h x ≈ h′ x) → Iinf m h f ≈ Iinf m h′ f′
  Iinf-cong m f f′ e = ≤-antisym (Iinf-mono m f f′ (λ x → ≤-reflexive (e x)))
                                 (Iinf-mono m f′ f (λ x → ≤-reflexive (sym (e x))))

  pw-tr : ∀ k a → pw k * tr k a ≈ mn a (pw k)
  pw-tr k a = begin
    pw k * (hp k * mn a (pw k))   ≈⟨ sym (*-assoc _ _ _) ⟩
    (pw k * hp k) * mn a (pw k)   ≈⟨ *-cong (trans (*-comm _ _) (hp-pw k)) refl ⟩
    1# * mn a (pw k)              ≈⟨ *-identityˡ _ ⟩
    mn a (pw k) ∎


  -- the approximations φₙ = 2ⁿ · tr n φ ↑ φ
  φn : (S → ∣A∣) → ℕ → S → ∣A∣
  φn φ n x = pw n * tr n (φ x)

  incφ : ∀ φ x → Increasing (λ n → φn φ n x)
  incφ φ x n = ≤-trans (≤-reflexive (pw-tr n (φ x)))
    (≤-trans (mn-mono ≤-refl (pw-≤ n)) (≤-reflexive (sym (pw-tr (ℕ.suc n) (φ x)))))

  eqφ : ∀ φ x → φ x ≈ ⨆ (λ n → φn φ n x) (incφ φ x)
  eqφ φ x = ≤-antisym
    (≤-trans (mn-sup (φ x) (λ n → mn-mono ≤-refl (pw-≤ n)))
      (⨆-lub _ _ (λ n → ≤-trans (≤-reflexive (sym (pw-tr n (φ x)))) (⨆-ub _ (incφ φ x) n))))
    (⨆-lub _ _ (λ n → ≤-trans (≤-reflexive (pw-tr n (φ x))) mn-≤l))


  -- closure properties of measurability, supplied by the model
  record Closed : Set₁ where
    field
      cl-mul : ∀ c {h} → FunInf h → FunInf (λ x → c * h x)
      cl-add : ∀ {h₁ h₂} → FunInf h₁ → FunInf h₂ → FunInf (λ x → h₁ x + h₂ x)

  module Linear (C : Closed) where
    open Closed C

    -- the powers of two times a bounded function
    Iinf-pw : ∀ m j {f} (F : Fun f) (Fj : FunInf (λ x → pw j * f x)) →
      Iinf m (λ x → pw j * f x) Fj ≈ pw j * I m f F
    Iinf-pw m ℕ.zero {f} F Fj = begin
      Iinf m (λ x → 1# * f x) Fj                  ≈⟨ Iinf-cong m Fj (FunInf-bounded F) (λ x → *-identityˡ _) ⟩
      Iinf m f (FunInf-bounded F)                 ≈⟨ Iinf-bounded m F (FunInf-bounded F) ⟩
      I m f F                                     ≈⟨ sym (*-identityˡ _) ⟩
      1# * I m f F ∎
    Iinf-pw m (ℕ.suc j) {f} F Fj = begin
      Iinf m (λ x → (pw j + pw j) * f x) Fj
        ≈⟨ Iinf-add m Fj F₁ F₁ (λ x → distribʳ (f x) (pw j) (pw j)) ⟩
      Iinf m (λ x → pw j * f x) F₁ + Iinf m (λ x → pw j * f x) F₁
        ≈⟨ +-cong (Iinf-pw m j F F₁) (Iinf-pw m j F F₁) ⟩
      pw j * I m f F + pw j * I m f F
        ≈⟨ sym (distribʳ _ _ _) ⟩
      (pw j + pw j) * I m f F ∎
      where F₁ = cl-mul (pw j) (FunInf-bounded F)

    -- d · g for a bounded g and any constant d
    private
      mn-inc : ∀ d → Increasing (λ j → mn d (pw j))
      mn-inc d j = mn-mono ≤-refl (pw-≤ j)

      mn-⨆-d : ∀ d → d ≈ ⨆ (λ j → mn d (pw j)) (mn-inc d)
      mn-⨆-d d = ≤-antisym (mn-sup d (mn-inc d)) (⨆-lub _ (mn-inc d) (λ j → mn-≤l))

      -- multiplying on the right instead of the left
      comm-inc : ∀ a {c : ℕ → ∣A∣} → Increasing c → Increasing (λ j → c j * a)
      comm-inc a {c} inc j = ≤-trans (≤-reflexive (*-comm _ _))
        (≤-trans (*-mono a (inc j)) (≤-reflexive (*-comm _ _)))

    -- the pieces of `Iinf-scale-fun`: d · g = ⨆ⱼ mn d (2ʲ) · g, with each term integrating to mn d (2ʲ) · ∫ g
    private
      scale-incJ : ∀ d (g : S → ∣A∣) x → Increasing (λ j → mn d (pw j) * g x)
      scale-incJ d g x = comm-inc (g x) (mn-inc d)

      scale-fsj : ∀ d {g} (G : Fun g) j → FunInf (λ x → mn d (pw j) * g x)
      scale-fsj d G j = cl-mul (mn d (pw j)) (FunInf-bounded G)

      scale-eqJ : ∀ d (g : S → ∣A∣) x → d * g x ≈ ⨆ (λ j → mn d (pw j) * g x) (scale-incJ d g x)
      scale-eqJ d g x = begin
        d * g x                                          ≈⟨ *-cong (mn-⨆-d d) refl ⟩
        ⨆ (λ j → mn d (pw j)) (mn-inc d) * g x           ≈⟨ *-comm _ _ ⟩
        g x * ⨆ (λ j → mn d (pw j)) (mn-inc d)           ≈⟨ *-⨆ (g x) (λ j → mn d (pw j)) (mn-inc d) (λ j → *-mono (g x) (mn-inc d j)) ⟩
        ⨆ (λ j → g x * mn d (pw j)) (λ j → *-mono (g x) (mn-inc d j))
                                                         ≈⟨ ⨆-cong _ (scale-incJ d g x) (λ j → *-comm _ _) ⟩
        ⨆ (λ j → mn d (pw j) * g x) (scale-incJ d g x) ∎

      scale-termJ : ∀ m d {g} (G : Fun g) j →
        Iinf m (λ x → mn d (pw j) * g x) (scale-fsj d G j) ≈ mn d (pw j) * I m g G
      scale-termJ m d {g} G j = begin
        Iinf m (λ x → mn d (pw j) * g x) (scale-fsj d G j)
          ≈⟨ Iinf-cong m (scale-fsj d G j) (cl-mul (pw j) (FunInf-bounded Fu))
               (λ x → sym (trans (sym (*-assoc _ _ _)) (*-cong (pw-tr j d) refl))) ⟩
        Iinf m (λ x → pw j * (tr j d * g x)) (cl-mul (pw j) (FunInf-bounded Fu))
          ≈⟨ Iinf-pw m j Fu (cl-mul (pw j) (FunInf-bounded Fu)) ⟩
        pw j * I m (λ x → tr j d * g x) Fu
          ≈⟨ *-cong refl (I-scale m (tr j d) G Fu (λ x → refl)) ⟩
        pw j * (tr j d * I m g G)
          ≈⟨ sym (*-assoc _ _ _) ⟩
        (pw j * tr j d) * I m g G
          ≈⟨ *-cong (pw-tr j d) refl ⟩
        mn d (pw j) * I m g G ∎
        where Fu = Fun-scale (tr j d) (tr-≤1 j d) G

    Iinf-scale-fun : ∀ m d {g} (G : Fun g) (F : FunInf (λ x → d * g x)) →
      Iinf m (λ x → d * g x) F ≈ d * I m g G
    Iinf-scale-fun m d {g} G F = begin
      Iinf m (λ x → d * g x) F
        ≈⟨ Iinf-sup m (λ j x → mn d (pw j) * g x) (scale-fsj d G) (scale-incJ d g) F (scale-eqJ d g) ⟩
      ⨆ (λ j → Iinf m (λ x → mn d (pw j) * g x) (scale-fsj d G j)) _
        ≈⟨ ⨆-cong _ incK (scale-termJ m d G) ⟩
      ⨆ (λ j → mn d (pw j) * I m g G) incK
        ≈⟨ sym (⨆-cong incK′ incK (λ j → *-comm _ _)) ⟩
      ⨆ (λ j → I m g G * mn d (pw j)) incK′
        ≈⟨ sym (*-⨆ (I m g G) (λ j → mn d (pw j)) (mn-inc d) incK′) ⟩
      I m g G * ⨆ (λ j → mn d (pw j)) (mn-inc d)
        ≈⟨ *-comm _ _ ⟩
      ⨆ (λ j → mn d (pw j)) (mn-inc d) * I m g G
        ≈⟨ *-cong (sym (mn-⨆-d d)) refl ⟩
      d * I m g G ∎
      where
        incK : Increasing (λ j → mn d (pw j) * I m g G)
        incK = comm-inc (I m g G) (mn-inc d)

        incK′ : Increasing (λ j → I m g G * mn d (pw j))
        incK′ j = *-mono (I m g G) (mn-inc d j)

    -- scaling an unbounded function
    Iinf-scale : ∀ m c {φ} (f∞ : FunInf φ) →
      Iinf m (λ x → c * φ x) (cl-mul c f∞) ≈ c * Iinf m φ f∞
    Iinf-scale m c {φ} f∞ = begin
      Iinf m (λ x → c * φ x) (cl-mul c f∞)
        ≈⟨ Iinf-sup m (λ n x → c * φn φ n x) (λ n → cl-mul c (fn n)) (λ x n → *-mono c (incφ φ x n)) (cl-mul c f∞)
             (λ x → trans (*-cong refl (eqφ φ x)) (*-⨆ c (λ n → φn φ n x) (incφ φ x) (λ n → *-mono c (incφ φ x n)))) ⟩
      ⨆ (λ n → Iinf m (λ x → c * φn φ n x) (cl-mul c (fn n))) _
        ≈⟨ ⨆-cong _ (λ n → *-mono c (Iseq-inc m φ f∞ n)) termN ⟩
      ⨆ (λ n → c * Iseq m φ f∞ n) (λ n → *-mono c (Iseq-inc m φ f∞ n))
        ≈⟨ sym (*-⨆ c (Iseq m φ f∞) (Iseq-inc m φ f∞) (λ n → *-mono c (Iseq-inc m φ f∞ n))) ⟩
      c * Iinf m φ f∞ ∎
      where
        fn : ∀ n → FunInf (φn φ n)
        fn n = cl-mul (pw n) (FunInf-bounded (f∞ n))

        termN : ∀ n → Iinf m (λ x → c * φn φ n x) (cl-mul c (fn n)) ≈ c * Iseq m φ f∞ n
        termN n = begin
          Iinf m (λ x → c * φn φ n x) (cl-mul c (fn n))
            ≈⟨ Iinf-cong m (cl-mul c (fn n)) (cl-mul (c * pw n) (FunInf-bounded (f∞ n)))
                 (λ x → sym (*-assoc _ _ _)) ⟩
          Iinf m (λ x → (c * pw n) * tr n (φ x)) (cl-mul (c * pw n) (FunInf-bounded (f∞ n)))
            ≈⟨ Iinf-scale-fun m (c * pw n) (f∞ n) (cl-mul (c * pw n) (FunInf-bounded (f∞ n))) ⟩
          (c * pw n) * I m (λ x → tr n (φ x)) (f∞ n)
            ≈⟨ *-assoc _ _ _ ⟩
          c * Iseq m φ f∞ n ∎
