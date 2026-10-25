{-# OPTIONS --safe --without-K #-}

-- The unbounded integral of countable sums and mixtures: `J (∑ aₙ) = ∑ J aₙ` (monotone
-- convergence along the partial sums) and `J (∑ cₙ μₙ) = ∑ cₙ J μₙ`, and the geometric series
-- `∑ hp (n+1) = 1`.
module QBS.Analysis.JSum where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality.Core as ≡

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch; module ArchLemmas)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.SeriesSup using (module SeriesSup)
open import QBS.Analysis.MixtureN using (module MixtureN)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.JParam using (module JParam)

module JSum (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open JParam lem
  open Meas lem
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; ⨆; Increasing; refl; sym; trans; +-cong; *-cong; ⨆-cong;
    ≤-antisym; ≤-reflexive; ≤-trans; zeroˡ; *-identityˡ; *-assoc; *-comm; +-identityˡ)
  open Integration A using (Measure; I)
  open Series A
  open SeriesSup A using (∑ᶠ-⨆)
  open MixtureN A using (mixN)
  module AR = Arch (lowerRealsArch lem)
  open AR using (hp; hp-zero; hp-double; arch) public
  open ArchLemmas (lowerRealsArch lem) using (geo)

  ----------------------------------------------------------------------------
  -- measurability and integrals of countable sums

  Meas-psum : ∀ (a : ℕ → R₁ → Cut) → (∀ n → Meas (a n)) → ∀ N → Meas (λ x → psum (λ n → a n x) N)
  Meas-psum a ma ℕ.zero = Meas-const 0#
  Meas-psum a ma (ℕ.suc N) = Meas-⊕ {λ x → psum (λ n → a n x) N} {a N} (Meas-psum a ma N) (ma N)

  Meas-∑ : ∀ (a : ℕ → R₁ → Cut) → (∀ n → Meas (a n)) → Meas (λ x → ∑ᶠ (λ n → a n x))
  Meas-∑ a ma = Meas-⨆ {λ x → ∑ᶠ (λ n → a n x)} (λ N x → psum (λ n → a n x) N) (Meas-psum a ma) (λ x → ≋-refl {∑ᶠ (λ n → a n x)})

  J-psum : ∀ m (a : ℕ → R₁ → Cut) (ma : ∀ n → Meas (a n)) N →
    J m (λ x → psum (λ n → a n x) N) (Meas-psum a ma N) ≈ psum (λ n → J m (a n) (ma n)) N
  J-psum m a ma ℕ.zero = trans (J-cong m (Meas-const 0#) (Meas-⊗ {λ _ → 0#} {λ _ → 0#} (Meas-const 0#) (Meas-const 0#)) (λ x → sym (zeroˡ 0#)))
    (trans (J-scale m 0# {λ _ → 0#} (Meas-const 0#)) (zeroˡ _))
  J-psum m a ma (ℕ.suc N) = trans (J-add m {λ x → psum (λ n → a n x) N} {a N} (Meas-psum a ma N) (ma N))
    (+-cong (J-psum m a ma N) (refl {J m (a N) (ma N)}))

  J-∑ : ∀ m (a : ℕ → R₁ → Cut) (ma : ∀ n → Meas (a n)) →
    J m (λ x → ∑ᶠ (λ n → a n x)) (Meas-∑ a ma) ≈ ∑ᶠ (λ n → J m (a n) (ma n))
  J-∑ m a ma = trans
    (J-⨆ m {λ x → ∑ᶠ (λ n → a n x)} (λ N x → psum (λ n → a n x) N) (Meas-psum a ma)
       (λ x → psum-inc (λ n → a n x)) (Meas-∑ a ma) (λ x → refl {∑ᶠ (λ n → a n x)}))
    (⨆-cong (λ N → J-mono m (Meas-psum a ma N) (Meas-psum a ma (ℕ.suc N)) (λ x → psum-inc (λ n → a n x) N))
      (psum-inc (λ n → J m (a n) (ma n))) (J-psum m a ma))

  ----------------------------------------------------------------------------
  -- the geometric series ∑ hp (n+1) = 1

  hp-geo : ∀ N → psum (λ i → hp (ℕ.suc i)) N + hp N ≈ 1#
  hp-geo N = trans (+-cong (psum-cong (λ i → OmegaSemiring.reflexive A (≡.cong hp (≡.sym (ℕ.+-identityʳ (ℕ.suc i))))) N)
                           (OmegaSemiring.reflexive A (≡.cong hp (≡.sym (ℕ.+-identityʳ N)))))
    (trans (geo 0 N) hp-zero)

  ∑hp≤1 : ∑ᶠ (λ n → hp (ℕ.suc n)) ≤ 1#
  ∑hp≤1 = ∑ᶠ-lub (λ N → ≤-trans {psum (λ i → hp (ℕ.suc i)) N} {psum (λ i → hp (ℕ.suc i)) N + hp N} {1#}
    (OmegaSemiring.≤-+ʳ A {psum (λ i → hp (ℕ.suc i)) N} {hp N}) (≤-reflexive {psum (λ i → hp (ℕ.suc i)) N + hp N} {1#} (hp-geo N)))

  ∑hp≈1 : ∑ᶠ (λ n → hp (ℕ.suc n)) ≈ 1#
  ∑hp≈1 = ≤-antisym ∑hp≤1 (arch {1#} {∑ᶠ (λ n → hp (ℕ.suc n))} (λ n →
    ≤-trans {1#} {psum (λ i → hp (ℕ.suc i)) n + hp n} {∑ᶠ (λ n → hp (ℕ.suc n)) + hp n}
      (≤-reflexive {1#} {psum (λ i → hp (ℕ.suc i)) n + hp n} (sym (hp-geo n)))
      (OmegaSemiring.+-mono A (psum≤∑ᶠ (λ i → hp (ℕ.suc i)) n) (OmegaSemiring.≤-refl A {hp n}))))

  ----------------------------------------------------------------------------
  -- the integral against a countable mixture

  private
    swap : ∀ x y z → x * (y * z) ≈ y * (x * z)
    swap x y z = trans (sym (*-assoc x y z)) (trans (*-cong (*-comm x y) refl) (*-assoc y x z))

  J-mixN : ∀ c (sub : ∑ᶠ c ≤ 1#) (μ : ℕ → Measure) {φ} (p : Meas φ) →
    J (mixN c sub μ) φ p ≈ ∑ᶠ (λ n → c n * J (μ n) φ p)
  J-mixN c sub μ {φ} p = trans (J-def (mixN c sub μ) p)
    (trans (⨆-cong (Iseq-inc (mixN c sub μ) φ F) (λ k → ∑ᶠ-mono (λ n → ≤-trans (OmegaSemiring.≤-refl A) (incN n k))) pt)
      (trans (sym (∑ᶠ-⨆ aN incN)) (∑ᶠ-cong termN)))
    where
      F = FunInf-Meas p

      aN : ℕ → ℕ → Cut
      aN n k = c n * Iseq (μ n) φ F k

      incN : ∀ n → Increasing (aN n)
      incN n k = OmegaSemiring.*-mono A (c n) (Iseq-inc (μ n) φ F k)

      pt : ∀ k → Iseq (mixN c sub μ) φ F k ≈ ∑ᶠ (λ n → aN n k)
      pt k = trans (∑ᶠ-scale (pw k) _) (∑ᶠ-cong (λ n → swap (pw k) (c n) _))

      termN : ∀ n → ⨆ (aN n) (incN n) ≈ c n * J (μ n) φ p
      termN n = trans (sym (OmegaSemiring.*-⨆ A (c n) (Iseq (μ n) φ F) (Iseq-inc (μ n) φ F) (incN n)))
        (*-cong refl (sym (J-def (μ n) p)))
