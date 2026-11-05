{-# OPTIONS --safe --without-K #-}

-- Uniqueness for finite weighted pushforwards on Cantor space (plan 03, "Uniqueness on the half-line").  A probability
-- measure m, a `Meas` weight w and a measurable map x give the functional
--   Jw g = ∫ w(r) · g(x r) dm(r)
-- on the threshold-measurable g.  Two such functionals with equal finite mass that agree on every cylinder agree on
-- every `Meas` function (`uniqW`).  This extends `Analysis/Uniqueness` (probability measures, bounded `Fun`) by
--   * `wM`: a weighted pushforward of mass ≤ 1 is a `Measure`, with `I-wM` its integral;
--   * `uniqW-le1`: the case of mass ≤ 1, from `Uniqueness.agree-fun` applied to the two `wM`;
--   * `uniqW-fun`: finite mass, by scaling both weights by ½ʲ with `mass ≤ 2ʲ`;
--   * `uniqW`: unbounded g, by truncation and monotone convergence (`J-⨆`).
module QBS.Analysis.UniquenessWeighted where

open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (proj₁; proj₂)

open import QBS.Borel.Core using (Measurable)
open import QBS.Borel.Source using (R₁) renaming (down to downR)
open import QBS.Borel.PiLambda using (Cyl)
open import QBS.Borel.Merge using (Cyl-borel)
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Density using (module Density)
open import QBS.Analysis.Uniqueness using (module Uniqueness)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)

module UniquenessWeighted (lem : LEM₀) where
  open Lebesgue lem using (A; J; J-irrel; J-cong; J-scale; FunInf-Meas; pw; 1≤pw; hp-pw)
  open Arch (lowerRealsArch lem) using (hp)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; refl; sym; trans; *-cong; *-assoc; *-comm; *-identityˡ; *-identityʳ;
    ≤-trans; ≤-reflexive; *-mono; +-mono; 0-least; ⨆-cong) renaming (Carrier to ∣A∣)
  open Integration A using (Measure; I; push; mass)
  open Measurable A using (Fun; Fun-const)
  module D = Density lem
  open Meas lem using (Meas; Meas-⊗; Meas-pre; Meas-const)
  open LevelSets lem using (LS)
  open Indicators A lem using (χ; Fun-χ)
  open Bounded A using (Bnd; nat)

  -- the indicator of a cylinder, as a `Meas` function
  χM : ∀ {C} → Cyl C → Meas (χ C)
  χM c = LS (Fun-χ (Cyl-borel c))

  -- the weighted pushforward g ↦ ∫ w(r) · g(x r) dm(r)
  Jw : (m : Measure) {w : R₁ → ∣A∣} → Meas w → {x : R₁ → R₁} → Measurable (downR x) → ∀ g → Meas g → ∣A∣
  Jw m {w} mw {x} mx g mg = J m (λ r → w r * g (x r)) (Meas-⊗ {w} {λ r → g (x r)} mw (Meas-pre {g} {x} mg mx))

  -- its mass
  Mw : (m : Measure) {w : R₁ → ∣A∣} → Meas w → {x : R₁ → R₁} → Measurable (downR x) → ∣A∣
  Mw m mw mx = Jw m mw mx (λ _ → 1#) (Meas-const 1#)

  -- the mass bound, as the form `densM` wants
  1Mw : ∀ (m : Measure) {w} (mw : Meas w) {x} (mx : Measurable (downR x)) → Mw m mw mx ≤ 1# → 1# * J m w mw ≤ 1#
  1Mw m {w} mw mx b = ≤-trans (≤-reflexive (*-identityˡ _))
    (≤-trans (≤-reflexive (J-cong m mw _ (λ r → sym (*-identityʳ (w r))))) b)

  -- a weighted pushforward of mass at most 1 is a `Measure`
  wM : (m : Measure) {w : R₁ → ∣A∣} (mw : Meas w) {x : R₁ → R₁} (mx : Measurable (downR x)) → Mw m mw mx ≤ 1# → Measure
  wM m {w} mw {x} mx b = push {x} mx (D.densM m w mw 1# (1Mw m mw mx b))

  I-wM : ∀ (m : Measure) {w} (mw : Meas w) {x} (mx : Measurable (downR x)) (b : Mw m mw mx ≤ 1#) {h} (f : Fun h) →
    I (wM m mw mx b) h f ≈ Jw m mw mx h (LS f)
  I-wM m mw mx b f = trans (*-identityˡ _) (J-irrel m _ _)

  -- mass of `wM`
  mass-wM : ∀ (m : Measure) {w} (mw : Meas w) {x} (mx : Measurable (downR x)) (b : Mw m mw mx ≤ 1#) →
    mass (wM m mw mx b) ≈ Mw m mw mx
  mass-wM m mw mx b = trans (I-wM m mw mx b (Fun-const 1# (OmegaSemiring.≤-refl A))) (J-irrel m _ _)

  -- scaling the weight by a constant
  sw : ∀ c {w} → Meas w → Meas (λ r → c * w r)
  sw c {w} mw = Meas-⊗ {λ _ → c} {w} (Meas-const c) mw

  scaleJw : ∀ (m : Measure) c {w} (mw : Meas w) {x} (mx : Measurable (downR x)) {g} (mg : Meas g) →
    Jw m (sw c mw) mx g mg ≈ c * Jw m mw mx g mg
  scaleJw m c {w} mw {x} mx {g} mg = trans
    (J-cong m _ (Meas-⊗ {λ _ → c} {λ r → w r * g (x r)} (Meas-const c) (Meas-⊗ {w} {λ r → g (x r)} mw (Meas-pre {g} {x} mg mx)))
      (λ r → *-assoc c (w r) (g (x r))))
    (J-scale m c {λ r → w r * g (x r)} (Meas-⊗ {w} {λ r → g (x r)} mw (Meas-pre {g} {x} mg mx)))

  -- ½ᵏ · 2ᵏ = 1 and naturals are below powers of two
  nat≤pw : ∀ N → nat N ≤ pw N
  nat≤pw zero = 0-least
  nat≤pw (suc N) = +-mono (1≤pw N) (nat≤pw N)

  unscale : ∀ k {x y} → hp k * x ≈ hp k * y → x ≈ y
  unscale k {x} {y} e = trans (sym (back x)) (trans (*-cong refl e) (back y))
    where back : ∀ z → pw k * (hp k * z) ≈ z
          back z = trans (sym (*-assoc _ _ _)) (trans (*-cong (trans (*-comm _ _) (hp-pw k)) refl) (*-identityˡ z))

  -- mass at most 1: `Uniqueness.agree-fun` for the two `wM`
  le1 : ∀ (m m′ : Measure) {w w′} (mw : Meas w) (mw′ : Meas w′) {x x′} (mx : Measurable (downR x))
    (mx′ : Measurable (downR x′)) → Mw m mw mx ≈ Mw m′ mw′ mx′ →
    (∀ {C} (c : Cyl C) → Jw m mw mx (χ C) (χM c) ≈ Jw m′ mw′ mx′ (χ C) (χM c)) →
    Mw m mw mx ≤ 1# → ∀ {h} (f : Fun h) → Jw m mw mx h (LS f) ≈ Jw m′ mw′ mx′ h (LS f)
  le1 m m′ mw mw′ mx mx′ masses agree b f = trans (sym (I-wM m mw mx b f)) (trans
    (Uniqueness.agree-fun A lem (wM m mw mx b) (wM m′ mw′ mx′ b′) (trans (mass-wM m mw mx b)
       (trans masses (sym (mass-wM m′ mw′ mx′ b′))))
       (λ c → trans (I-wM m mw mx b _) (trans (agree c) (sym (I-wM m′ mw′ mx′ b′ _)))) f)
    (I-wM m′ mw′ mx′ b′ f))
    where b′ = ≤-trans (≤-reflexive (sym masses)) b

  module _ (m m′ : Measure) {w w′ : R₁ → ∣A∣} (mw : Meas w) (mw′ : Meas w′)
           {x x′ : R₁ → R₁} (mx : Measurable (downR x)) (mx′ : Measurable (downR x′))
           (fin : Bnd (Mw m mw mx)) (masses : Mw m mw mx ≈ Mw m′ mw′ mx′)
           (agree : ∀ {C} (c : Cyl C) → Jw m mw mx (χ C) (χM c) ≈ Jw m′ mw′ mx′ (χ C) (χM c)) where

    -- mass at most 1: `Uniqueness.agree-fun` for the two `wM`
    uniqW-le1 : Mw m mw mx ≤ 1# → ∀ {h} (f : Fun h) → Jw m mw mx h (LS f) ≈ Jw m′ mw′ mx′ h (LS f)
    uniqW-le1 = le1 m m′ mw mw′ mx mx′ masses agree

    -- finite mass: scale both weights by ½ʲ, where `Mw m mw mx ≤ 2ʲ`
    uniqW-fun : ∀ {h} (f : Fun h) → Jw m mw mx h (LS f) ≈ Jw m′ mw′ mx′ h (LS f)
    uniqW-fun {h} f = unscale N (trans (sym (scaleJw m c mw mx (LS f)))
      (trans (le1 m m′ (sw c mw) (sw c mw′) mx mx′ ms ag bd f) (scaleJw m′ c mw′ mx′ (LS f))))
      where
        N = proj₁ fin
        c = hp N
        ms = trans (scaleJw m c mw mx (Meas-const 1#)) (trans (*-cong refl masses) (sym (scaleJw m′ c mw′ mx′ (Meas-const 1#))))
        ag : ∀ {C} (cy : Cyl C) → Jw m (sw c mw) mx (χ C) (χM cy) ≈ Jw m′ (sw c mw′) mx′ (χ C) (χM cy)
        ag cy = trans (scaleJw m c mw mx (χM cy)) (trans (*-cong refl (agree cy)) (sym (scaleJw m′ c mw′ mx′ (χM cy))))
        bd : Mw m (sw c mw) mx ≤ 1#
        bd = ≤-trans (≤-reflexive (scaleJw m c mw mx (Meas-const 1#)))
          (≤-trans (*-mono c (≤-trans (proj₂ fin) (nat≤pw N))) (≤-reflexive (hp-pw N)))

    -- every threshold-measurable function: truncate and pass to the limit
    uniqW : ∀ {g} (mg : Meas g) → Jw m mw mx g mg ≈ Jw m′ mw′ mx′ g mg
    uniqW {g} mg = trans AM.J-approx (trans (⨆-cong AM.incJ AM′.incJ pt) (sym AM′.J-approx))
      where
        module AM = D.Approx m w mw {λ r → g (x r)} (Meas-pre {g} {x} mg mx)
        module AM′ = D.Approx m′ w′ mw′ {λ r → g (x′ r)} (Meas-pre {g} {x′} mg mx′)
        G = FunInf-Meas {g} mg
        pt : ∀ k → J m (AM.φs k) (AM.ps k) ≈ J m′ (AM′.φs k) (AM′.ps k)
        pt k = trans (AM.J-approx-pt k) (trans (*-cong refl (trans (J-irrel m _ _)
          (trans (uniqW-fun (G k)) (J-irrel m′ _ _)))) (sym (AM′.J-approx-pt k)))
