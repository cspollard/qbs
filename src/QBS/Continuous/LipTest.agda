{-# OPTIONS --safe --without-K #-}

-- Locally Lipschitz functions are tests, and so is everything with `Deriv` data (plan 03, "Tests and the real line").
--   * `LocLip F`: on every [0, N+1], F (a + w) and F a differ by at most w c both ways (w ≤ 1, c finite);
--   * `lipH F : WQ ⇒ WQ` for F respecting ≈ with `LocLip F` (the value at ∞ is arbitrary);
--   * `derivH G h k dv`, `lipkH`, `liphH`: from `dv : ∀ N → Deriv (N+1) G h k` (`Analysis/Deriv`), G, h and k are tests
--     (`deriv-lipG` from the certificates `Ct1`/`Ct2` with h, k ≤ c; `deriv-lipk`, `deriv-liph` from `LpU`/`LpD`).
-- Route for `Meas-lip`: q ∈ F x for finite x iff some dyadic cell [m/2ⁿ, (m+1)/2ⁿ) ∋ x has q + c/2ⁿ ∈ F (m/2ⁿ) (F is
-- rounded, and within c/2ⁿ on the cell), so the threshold set is a countable union of cells intersected with decided
-- conditions (excluded middle), plus {∞} if q ∈ F ∞; cells and {∞} are Borel by `Intervals.ge-borel`.
--   Skeleton: holes first.
module QBS.Continuous.LipTest where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (Σ; _×_)

open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Deriv using (module AlgD)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.TailFTC using (module TailFTC)

module LipTest (lem₁ : LEM₁) where
  open TailFTC lem₁ using (A; R)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 1#) renaming (Carrier to ∣A∣)
  open Exp A using (natE)
  open Bounded A using (Bnd)
  open AlgD A R using (Deriv)
  open Meas (lemOf lem₁) using (Meas)
  open Weights (lemOf lem₁) using (WQ)
  open QBS
  open Hom

  -- Lipschitz on every bounded interval, both ways
  LocLip : (∣A∣ → ∣A∣) → Set₁
  LocLip F = ∀ N → Σ ∣A∣ λ c → Bnd c
    × (∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F (a + w) ≤ F a + w * c)
    × (∀ a w → a + w ≤ natE (suc N) → w ≤ 1# → F a ≤ F (a + w) + w * c)

  module _ (F : ∣A∣ → ∣A∣) (cF : ∀ {x y} → x ≈ y → F x ≈ F y) (lF : LocLip F) where

    Meas-lip : ∀ {α} → Meas α → Meas (λ r → F (α r))
    Meas-lip = ?

    lipH : Hom S WQ WQ
    lipH = record { map = record { to = F ; cong = cF } ; map-random = λ {γ} m → Meas-lip {γ ⟨$⟩_} m }

  module _ (G h k : ∣A∣ → ∣A∣) (dv : ∀ N → Deriv (natE (suc N)) G h k) where

    -- the certificate functions respect ≈
    deriv-cgG : ∀ {x y} → x ≈ y → G x ≈ G y
    deriv-cgG = ?

    deriv-cgh : ∀ {x y} → x ≈ y → h x ≈ h y
    deriv-cgh = ?

    deriv-cgk : ∀ {x y} → x ≈ y → k x ≈ k y
    deriv-cgk = ?

    -- and are locally Lipschitz
    deriv-lipG : LocLip G
    deriv-lipG = ?

    deriv-liph : LocLip h
    deriv-liph = ?

    deriv-lipk : LocLip k
    deriv-lipk = ?

    derivH liphH lipkH : Hom S WQ WQ
    derivH = lipH G deriv-cgG deriv-lipG
    liphH = lipH h deriv-cgh deriv-liph
    lipkH = lipH k deriv-cgk deriv-lipk
