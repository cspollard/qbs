{-# OPTIONS --safe --without-K #-}

-- The certificate calculus (`Analysis/Deriv`) feeds the tail FTC: from `Deriv` data to integration by parts.
--   * `Unit.ftc-unit`: from `Deriv 1 G h k` (data on the unit interval) and measurability of `h ∘ expansion`, `k ∘ expansion`,
--       ∫₀¹ h + G 1 ≈ G 0 + ∫₀¹ k.
--     The hypotheses of `LipJ` (`Continuous/TailFTCLipJ`) are the point-pair facts of `D` at the dyadic pieces: the sample point
--     `a + ½ⁿ x` is the pair (a, ½ⁿ x) and the piece itself the pair (a, ½ⁿ); the bounds are 4c ≤ 2ˢ for s = S + 2 where c ≤ 2ˢ.
--   * `OnHalfLine.unit`: from `Deriv (n+1) G h k` for every n (data on [0, n+1]) the unit-interval identities on every [n, n+1], by
--     `Dshift` (translation) and `Unit.ftc-unit`: exactly the hypotheses of `TailFTCLipHalf.Glue`.
--   * `OnHalfLine.glue-D`: `∫ h dλ ≈ ∫ k dλ` when G 0 = 0 and G(N) → 0 along a subsequence (`Glue.glue`);
--     `OnHalfLine.glue-D0`: `∫ h dλ ≈ G 0 + ∫ k dλ` without G 0 = 0 (`sum-ibp0`: the far-out partial sums, and continuity of `+`
--     along the supremum of partial sums).
module QBS.Continuous.DerivBridge where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Continuous.Sample using (S)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Series using (module Series)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.FairCoin using (module FairCoin)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.TailFTC using (module TailFTC)
open import QBS.Continuous.TailFTCLipJ using (module TailFTCLipJ)
open import QBS.Continuous.TailFTCLipHalf using (module TailFTCLipHalf)

module DerivBridge (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; arch; hp) renaming (half+half to hh)
  open AlgT A R using (P; Dy; dy-bound; hp≤1)
  open AlgD A R
  open Lebesgue (lemOf lem₁) using (J)
  open Meas (lemOf lem₁) using (Meas)
  open Weights (lemOf lem₁) using (WQ)
  open Expansion A half hh using (expansion; expansion≤1)
  open Exp A using (natE)
  open Series A using (psum; psum-inc; ∑ᶠ; ∑ᶠ-lub; psum≤∑ᶠ)
  open FairCoin lem₁ using (fairCoin)
  open SFinite (lemOf lem₁) using (∫ᴹ)
  open HalfLine lem₁ using (lebPre; shiftPt; Meas-hshift; ∫ᴹ-leb)
  open TailFTCLipJ lem₁ using (module LipJ)
  open TailFTCLipHalf lem₁ using (tele-ibp; psum-mono≤; module Glue)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the unit interval

  module Unit {G h k : ∣A∣ → ∣A∣} (dv : Deriv 1# G h k)
    (Mh : Meas (λ r → h (expansion r))) (Mk : Meas (λ r → k (expansion r))) where
    c : ∣A∣
    c = proj₁ dv

    s₀ : ℕ
    s₀ = proj₁ (proj₁ (proj₂ dv))

    cS : c ≤ P s₀
    cS = proj₂ (proj₁ (proj₂ dv))

    d : D 1# c G h k
    d = proj₂ (proj₂ dv)

    a≤1 : ∀ {n a} → Dy n a → a ≤ 1#
    a≤1 dy = ≤-trans ≤-+ʳ (dy-bound dy)

    hle : ∀ {n} x → x ≤ 1# → hp n * x ≤ hp n
    hle {n} x x1 = ≤-trans (*-mono (hp n) x1) (≤-reflexive (*-identityʳ _))

    pt : ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → a + hp n * x ≤ 1#
    pt dy x x1 = ≤-trans (+-mono ≤-refl (hle x x1)) (dy-bound dy)

    -- (½ⁿ x) c ≤ ½ⁿ c
    xc : ∀ {n} x → x ≤ 1# → (hp n * x) * c ≤ hp n * c
    xc {n} x x1 = ≤-trans (≤-reflexive (*-assoc (hp n) x c)) (*-mono (hp n) (wle x1 c))

    shU : ∀ {u} → LpU 1# c u → ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u (a + hp n * x) ≤ u a + hp n * c
    shU lp {n} dy x x1 = ≤-trans (lp (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n))) (+-mono ≤-refl (xc x x1))

    shD : ∀ {u} → LpD 1# c u → ∀ {n a} → Dy n a → ∀ x → x ≤ 1# → u a ≤ u (a + hp n * x) + hp n * c
    shD lp {n} dy x x1 = ≤-trans (lp (pt dy x x1) (≤-trans (hle x x1) (hp≤1 n))) (+-mono ≤-refl (xc x x1))

    c3 : c + (c + c) ≤ P (suc (suc s₀))
    c3 = +-mono (≤-trans cS ≤-+ʳ) (+-mono cS cS)

    bd : ∀ {u} → Bnd 1# c u → ∀ x → x ≤ 1# → u x + c ≤ P (suc (suc s₀))
    bd b x x1 = ≤-trans (+-mono (≤-trans (b x1) cS) cS) ≤-+ʳ

    module L = LipJ h k G (suc (suc s₀)) s₀ c (D-ch d) (D-ck d) (D-cG d) c3 (bd (D-bh d)) (bd (D-bk d))
      (shU (D-hU d)) (shD (D-hD d)) (shU (D-kU d)) (shD (D-kD d)) Mh Mk
      (λ dy → ≤-trans (D-bG d (a≤1 dy)) cS)
      (λ {n} {a} dy → D-c1 d {a} {hp n} (dy-bound dy) (hp≤1 n))
      (λ {n} {a} dy → D-c2 d {a} {hp n} (dy-bound dy) (hp≤1 n))

    -- ∫₀¹ h + G 1 = G 0 + ∫₀¹ k
    ftc-unit : J fairCoin (λ r → h (expansion r)) Mh + G 1# ≈ G 0# + J fairCoin (λ r → k (expansion r)) Mk
    ftc-unit = L.ftc-J

  ----------------------------------------------------------------------------
  -- sums with G 0 ≠ 0

  sum-ibp0 : ∀ (a b g : ℕ → ∣A∣) → (∀ n → a n + g (suc n) ≈ g n + b n) →
    (∀ m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × g N ≤ hp m)) → ∑ᶠ a ≈ g 0 + ∑ᶠ b
  sum-ibp0 a b g e tl = ≤-antisym
    (∑ᶠ-lub (λ N → ≤-trans ≤-+ʳ (≤-trans (≤-reflexive (tele-ibp a b g e N)) (+-mono ≤-refl (psum≤∑ᶠ b N)))))
    (arch (λ m → ≤-trans (≤-reflexive (+-⨆ (g 0) (psum b) (psum-inc b) inc′))
      (⨆-lub _ inc′ (λ N → far m N (tl m N)))))
    where
    inc′ : Increasing (λ n → g 0 + psum b n)
    inc′ n = +-mono ≤-refl (psum-inc b n)

    far : ∀ m N → Σ ℕ (λ N₁ → N ℕ.≤ N₁ × g N₁ ≤ hp m) → g 0 + psum b N ≤ ∑ᶠ a + hp m
    far m N (N₁ , le , gb) = ≤-trans (+-mono ≤-refl (psum-mono≤ b le))
      (≤-trans (≤-reflexive (sym (tele-ibp a b g e N₁))) (+-mono (psum≤∑ᶠ a N₁) gb))

  ----------------------------------------------------------------------------
  -- the half-line

  module OnHalfLine (h k : Hom S WQ WQ) (G : ∣A∣ → ∣A∣)
    (dv : ∀ n → Deriv (natE (suc n)) G (λ x → map h ⟨$⟩ x) (λ x → map k ⟨$⟩ x)) where

    -- ∫₀¹ h(n+u) du + G(n+1) = G(n) + ∫₀¹ k(n+u) du
    unit : ∀ n → J fairCoin (λ r → map h ⟨$⟩ shiftPt n r) (Meas-hshift n h) + G (natE (suc n))
      ≈ G (natE n) + J fairCoin (λ r → map k ⟨$⟩ shiftPt n r) (Meas-hshift n k)
    unit n = trans (Unit.ftc-unit {λ x → G (natE n + x)} {λ x → map h ⟨$⟩ (natE n + x)} {λ x → map k ⟨$⟩ (natE n + x)}
        (DFshift (natE n) ≤-refl (dv n)) (Meas-hshift n h) (Meas-hshift n k))
      (+-cong (D-cG (proj₂ (proj₂ (dv n))) (+-identityʳ (natE n))) refl)

    -- ∫ h dλ = ∫ k dλ
    glue-D : G 0# ≈ 0# → (∀ m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × G (natE N) ≤ hp m)) → ∫ᴹ {WQ} lebPre h ≈ ∫ᴹ {WQ} lebPre k
    glue-D G0 tl = Glue.glue h k G unit G0 tl

    -- ∫ h dλ = G 0 + ∫ k dλ
    glue-D0 : (∀ m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × G (natE N) ≤ hp m)) → ∫ᴹ {WQ} lebPre h ≈ G 0# + ∫ᴹ {WQ} lebPre k
    glue-D0 tl = trans (∫ᴹ-leb h)
      (trans (sum-ibp0 _ _ (λ n → G (natE n)) unit tl) (+-cong refl (sym (∫ᴹ-leb k))))
