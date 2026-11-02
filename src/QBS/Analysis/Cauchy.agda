{-# OPTIONS --safe --without-K #-}

-- The Cauchy product of series in an `OmegaSemiring`: for every `a b : ℕ → A`,
-- `(∑ᶠ a) * (∑ᶠ b) ≈ ∑ᶠ n. (a₀ b_n + a₁ b_{n-1} + … + a_n b₀)`.
-- The diagonal sums are defined without subtraction on ℕ, by peeling off the last term:
-- `diag g 0 m = g 0 m`, `diag g (n+1) m = g (n+1) m + diag g n (m+1)` (so `diag g n m = ∑_{k≤n} g k (m+n-k)`).
-- The triangle `∑_{n<M} diag g n m` splits as a column plus a smaller triangle, and is sandwiched between
-- rectangles (`tri ≤ rect` and `rect ≤ tri` with twice the size), so the proof needs only the finite
-- sums of `Series` and a supremum lemma for products of increasing sequences (`⨆-*-lub`).
module QBS.Analysis.Cauchy where

import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Nat.Base using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Series

module Cauchy {ℓ} (A : OmegaSemiring ℓ) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Series A
  open SetoidReasoning setoid

  -- products of suprema
  ⨆-*-lub : ∀ {c d} (ic : Increasing c) (id : Increasing d) {b} →
    (∀ m n → c m * d n ≤ b) → ⨆ c ic * ⨆ d id ≤ b
  ⨆-*-lub {c} {d} ic id {b} h =
    ≤-trans (≤-reflexive (*-⨆ (⨆ c ic) d id incL)) (⨆-lub _ incL step)
    where
      incL : Increasing (λ n → ⨆ c ic * d n)
      incL n = *-mono _ (id n)
      step : ∀ n → ⨆ c ic * d n ≤ b
      step n = ≤-trans (≤-reflexive (trans (*-comm _ _) (*-⨆ (d n) c ic incR)))
                 (⨆-lub _ incR (λ m → ≤-trans (≤-reflexive (*-comm (d n) (c m))) (h m n)))
        where
          incR : Increasing (λ m → d n * c m)
          incR m = *-mono _ (ic m)

  module _ (g : ℕ → ℕ → ∣A∣) where

    -- ∑_{k<K} g k m
    col : ℕ → ℕ → ∣A∣
    col K m = psum (λ k → g k m) K

    -- the diagonal k + l = n + m
    diag : ℕ → ℕ → ∣A∣
    diag zero m = g 0 m
    diag (suc n) m = g (suc n) m + diag n (suc m)

    -- ∑_{n<M} diag n m
    tri : ℕ → ℕ → ∣A∣
    tri M m = psum (λ n → diag n m) M

    -- the rectangle of K rows and N columns starting at column m
    rect : ℕ → ℕ → ℕ → ∣A∣
    rect K N m = psum (λ l → col K (l ℕ.+ m)) N

    col-idx : ∀ K {i j} → i ≡.≡ j → col K i ≈ col K j
    col-idx K ≡.refl = refl

    col-mono : ∀ {K K′} m → K ℕ.≤ K′ → col K m ≤ col K′ m
    col-mono m h = psum-index-mono (λ k → g k m) h

    tri-suc : ∀ M m → tri (suc M) m ≈ col (suc M) m + tri M (suc m)
    tri-suc M m = begin
      tri (suc M) m
        ≈⟨ psum-shift (λ n → diag n m) M ⟩
      g 0 m + psum (λ n → g (suc n) m + diag n (suc m)) M
        ≈⟨ +-cong refl (psum-+ (λ n → g (suc n) m) (λ n → diag n (suc m)) M) ⟩
      g 0 m + (psum (λ n → g (suc n) m) M + tri M (suc m))
        ≈⟨ sym (+-assoc _ _ _) ⟩
      (g 0 m + psum (λ n → g (suc n) m) M) + tri M (suc m)
        ≈⟨ +-cong (sym (psum-shift (λ k → g k m) M)) refl ⟩
      col (suc M) m + tri M (suc m) ∎

    rect-suc : ∀ K N m → rect K (suc N) m ≈ col K m + rect K N (suc m)
    rect-suc K N m = trans (psum-shift (λ l → col K (l ℕ.+ m)) N)
      (+-cong refl (psum-cong (λ l → col-idx K (≡.sym (ℕ.+-suc l m))) N))

    -- the triangle lies in the rectangle
    tri≤rect : ∀ K M m → M ℕ.≤ K → tri M m ≤ rect K M m
    tri≤rect K zero m h = ≤-refl
    tri≤rect K (suc M) m h =
      ≤-trans (≤-reflexive (tri-suc M m))
        (≤-trans (+-mono (col-mono m h) (tri≤rect K M (suc m) (ℕ.<⇒≤ h)))
          (≤-reflexive (sym (rect-suc K M m))))

    -- and the rectangle lies in a larger triangle
    rect≤tri : ∀ K N m → rect K N m ≤ tri (N ℕ.+ K) m
    rect≤tri K zero m = 0-least
    rect≤tri K (suc N) m =
      ≤-trans (≤-reflexive (rect-suc K N m))
        (≤-trans (+-mono (col-mono m (ℕ.m≤n+m K N′)) (rect≤tri K N (suc m)))
          (≤-reflexive (sym (tri-suc (N ℕ.+ K) m))))
      where N′ = suc N

  ----------------------------------------------------------------------------
  -- the Cauchy product

  module Product (a b : ℕ → ∣A∣) where
    g : ℕ → ℕ → ∣A∣
    g i j = a i * b j

    conv : ℕ → ∣A∣
    conv n = diag g n 0

    rect-prod : ∀ K N → rect g K N 0 ≈ psum a K * psum b N
    rect-prod K N = begin
      psum (λ l → col g K (l ℕ.+ 0)) N
        ≈⟨ psum-cong (λ l → trans (col-idx g K (ℕ.+-identityʳ l)) (colK l)) N ⟩
      psum (λ l → psum a K * b l) N
        ≈⟨ psum-scale′ N ⟩
      psum a K * psum b N ∎
      where
        psum-scaleʳ : ∀ K l → psum a K * b l ≈ psum (λ k → a k * b l) K
        psum-scaleʳ K l = trans (*-comm _ _) (trans (sym (psum-scale (b l) a K)) (psum-cong (λ k → *-comm (b l) (a k)) K))
        colK : ∀ l → col g K l ≈ psum a K * b l
        colK l = sym (psum-scaleʳ K l)
        psum-scale′ : ∀ N → psum (λ l → psum a K * b l) N ≈ psum a K * psum b N
        psum-scale′ N = psum-scale (psum a K) b N

    cauchy : ∑ᶠ a * ∑ᶠ b ≈ ∑ᶠ conv
    cauchy = ≤-antisym
      (⨆-*-lub (psum-inc a) (psum-inc b) (λ m n →
        ≤-trans (≤-reflexive (sym (rect-prod m n)))
          (≤-trans (rect≤tri g m n 0) (psum≤∑ᶠ conv (n ℕ.+ m)))))
      (∑ᶠ-lub (λ M → ≤-trans (tri≤rect g M M 0 ℕ.≤-refl)
        (≤-trans (≤-reflexive (rect-prod M M))
          (≤-trans (*-mono _ (psum≤∑ᶠ b M))
            (≤-trans (≤-reflexive (*-comm _ _))
              (≤-trans (*-mono _ (psum≤∑ᶠ a M)) (≤-reflexive (*-comm _ _))))))))
