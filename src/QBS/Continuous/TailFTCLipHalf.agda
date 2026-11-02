{-# OPTIONS --safe --without-K #-}

-- Integration by parts on the half-line, from the unit-interval identities (`Continuous/TailFTCLipJ`).
--
-- Take measurable tests h, k : [0,∞] ⇒ [0,∞] and G with the unit-interval identity on each [n, n+1]
--     ∫₀¹ h(n + u) du + G (n+1) = G n + ∫₀¹ k(n + u) du,
-- `G 0 = 0` and `G(N) → 0` (for every m, eventually `G N ≤ ½ᵐ`).  `∫ᴹ-leb` writes the Lebesgue integrals as the sums of
-- the unit-interval integrals, and the partial sums telescope: `Σ_{n<N} ∫₀¹ h(n+u) du + G N = Σ_{n<N} ∫₀¹ k(n+u) du`.
-- Hence `∫ h dλ ≈ ∫ k dλ` (`glue`).  An eventual (not just frequent) tail is needed because `G` need not be monotone.
module QBS.Continuous.TailFTCLipHalf where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _,_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)

module TailFTCLipHalf (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (arch; hp)
  open Lebesgue (lemOf lem₁) using (J)
  open Series A using (psum; psum-inc; ∑ᶠ; ∑ᶠ-lub; ∑ᶠ-cong; psum≤∑ᶠ)
  open Exp A using (natE)
  open FairCoin lem₁ using (fairCoin)
  open Weights (lemOf lem₁) using (WQ)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open QBS
  open Hom

  -- the telescoping identity `psum a N + G N = G 0 + psum b N` from the one-step identities
  tele-ibp : ∀ (a b g : ℕ → ∣A∣) → (∀ n → a n + g (suc n) ≈ g n + b n) → ∀ N → psum a N + g N ≈ g 0 + psum b N
  tele-ibp a b g e zero = trans (+-identityˡ _) (sym (+-identityʳ _))
  tele-ibp a b g e (suc N) = trans (+-assoc (psum a N) (a N) (g (suc N)))
    (trans (+-cong refl (e N))
      (trans (sym (+-assoc (psum a N) (g N) (b N)))
        (trans (+-cong (tele-ibp a b g e N) refl) (+-assoc (g 0) (psum b N) (b N)))))

  -- sums: `∑ a ≈ ∑ b` when `G 0 = 0` and G tends to 0 eventually
  sum-ibp : ∀ (a b g : ℕ → ∣A∣) → (∀ n → a n + g (suc n) ≈ g n + b n) → g 0 ≈ 0# →
    (∀ m → Σ ℕ (λ N → ∀ N′ → N ℕ.≤ N′ → g N′ ≤ hp m)) → ∑ᶠ a ≈ ∑ᶠ b
  sum-ibp a b g e g0 tl = ≤-antisym
    (∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-trans (≤-reflexive (psum-eq N)) (psum≤∑ᶠ b N))))
    (arch (λ m → ∑ᶠ-lub (λ N′ → go m (tl m) N′)))
    where
    psum-eq : ∀ N → psum a N + g N ≈ psum b N
    psum-eq N = trans (tele-ibp a b g e N) (trans (+-cong g0 refl) (+-identityˡ _))

    mono : ∀ N N′ → psum b N′ ≤ psum b (N ℕ.+ N′)
    mono zero N′ = ≤-refl
    mono (suc N) N′ = ≤-trans (mono N N′) (psum-inc b (N ℕ.+ N′))

    go : ∀ m → Σ ℕ (λ N → ∀ N′ → N ℕ.≤ N′ → g N′ ≤ hp m) → ∀ N′ → psum b N′ ≤ ∑ᶠ a + hp m
    go m (N , gb) N′ = ≤-trans (mono N N′) (≤-trans (≤-reflexive (sym (psum-eq (N ℕ.+ N′))))
      (+-mono (psum≤∑ᶠ a (N ℕ.+ N′)) (gb (N ℕ.+ N′) (ℕ.m≤m+n N N′))))

  module Glue (h k : Hom S WQ WQ) (G : ∣A∣ → ∣A∣)
    (unit : ∀ n → J fairCoin (λ r → map h ⟨$⟩ shiftPt n r) (Meas-hshift n h) + G (natE (suc n))
              ≈ G (natE n) + J fairCoin (λ r → map k ⟨$⟩ shiftPt n r) (Meas-hshift n k))
    (G0 : G 0# ≈ 0#) (tl : ∀ m → Σ ℕ (λ N → ∀ N′ → N ℕ.≤ N′ → G (natE N′) ≤ hp m)) where

    -- ∫ h dλ = ∫ k dλ
    glue : ∫ᴹ {WQ} lebPre h ≈ ∫ᴹ {WQ} lebPre k
    glue = trans (∫ᴹ-leb h) (trans (sum-ibp _ _ (λ n → G (natE n)) unit G0 tl) (sym (∫ᴹ-leb k)))
