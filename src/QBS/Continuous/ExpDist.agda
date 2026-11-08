{-# OPTIONS --safe --without-K #-}

-- The exponential distribution `e^{−x} dλ(x)` on [0,∞) as a probability `Pre`.
--   * `expW = reweightPre negExpH lebPre : Pre (XW WQ)` (`Continuous/SFiniteReweight`) is Lebesgue measure with
--     density `e^{−x}`; `∫ᴹ-expW : ∫ᴹ expW f ≈ ∫ᴹ lebPre (e^{−x} · f)`;
--   * `massP-expW : massP expW ≈ 1#` from `HalfLineNorm.∫ᴹ-leb-negExp-norm`;
--   * `expDist = normPre expW 1# _ : C.Pre WQ`, with `∫-expDist : ∫ᴹ (ιPre expDist) f ≈ ∫ᴹ lebPre (e^{−x} · f)`;
--   * the total mass `∫-expDist-one ≈ 1#` and the mean `∫-expDist-id ≈ 1#` (the identity statistic), from
--     `HalfLineMomentFact.∫-x`.
-- Values are lower reals (no subtraction), so these are the multiplied-out statements.
module QBS.Continuous.ExpDist where


open import QBS.Core
open import QBS.Classical using (LEM₁)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.SFiniteIncl using (module SFiniteIncl)
open import QBS.Continuous.SFiniteNorm using (module SFiniteNorm)
open import QBS.Continuous.SFiniteReweight using (module SFiniteReweight)
open import QBS.Continuous.HalfLine using (module HalfLine)
open import QBS.Continuous.HalfLineNegExp using (module HalfLineNegExp)
open import QBS.Continuous.HalfLineNorm using (module HalfLineNorm)
open import QBS.Continuous.HalfLineMomentFact using (module HalfLineMomentFact)

module ExpDist (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _*_; 1#; refl; sym; trans; *-comm; *-identityˡ; *-identityʳ)
  open Weights (lemOf lem₁) using (WQ; constW)
  open SFinite (lemOf lem₁) using (module C; XW; ∫ᴹ; ∫ᴹ-cong)
  open SFiniteIncl (lemOf lem₁) using (ιPre)
  open SFiniteNorm (lemOf lem₁) using (massP; normPre; ∫-normPre)
  open SFiniteReweight (lemOf lem₁) using (mulH; reweightPre; ∫ᴹ-reweight)
  open HalfLine lem₁ using (lebPre)
  open HalfLineNegExp lem₁ using (negExpH)
  open HalfLineNorm lem₁ using (∫ᴹ-leb-negExp-norm)
  open HalfLineMomentFact lem₁ using (xNegExpH; ∫-x)
  open QBS
  open Hom

  -- Lebesgue measure with density `e^{−x}` (opaque: only its integrals are used afterwards)
  abstract
    expW : C.Pre (XW WQ)
    expW = reweightPre {WQ} negExpH lebPre

    -- the density-weighted integral
    ∫ᴹ-expW : ∀ (f : Hom S WQ WQ) → ∫ᴹ {WQ} expW f ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH f)
    ∫ᴹ-expW f = ∫ᴹ-reweight {WQ} negExpH lebPre f

  -- total mass 1
  massP-expW : massP {WQ} expW ≈ 1#
  massP-expW = trans (∫ᴹ-expW (constW 1#))
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH (constW 1#)} {negExpH} (λ x → *-identityʳ _))
      ∫ᴹ-leb-negExp-norm)

  mass-inv : massP {WQ} expW * 1# ≈ 1#
  mass-inv = trans (*-identityʳ _) massP-expW

  -- the exponential distribution
  abstract
    expDist : C.Pre WQ
    expDist = normPre {WQ} expW 1# mass-inv

    ∫-expDist : ∀ (f : Hom S WQ WQ) → ∫ᴹ {WQ} (ιPre {WQ} expDist) f ≈ ∫ᴹ {WQ} lebPre (mulH {WQ} negExpH f)
    ∫-expDist f = trans (∫-normPre {WQ} expW 1# mass-inv f) (trans (*-identityˡ _) (∫ᴹ-expW f))

  -- normalisation: the expectation of the constant 1
  ∫-expDist-one : ∫ᴹ {WQ} (ιPre {WQ} expDist) (constW 1#) ≈ 1#
  ∫-expDist-one = trans (∫-expDist (constW 1#))
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH (constW 1#)} {negExpH} (λ x → *-identityʳ _)) ∫ᴹ-leb-negExp-norm)

  -- the identity statistic
  idW : Hom S WQ WQ
  idW = record { map = record { to = λ x → x ; cong = λ e → e } ; map-random = λ m → m }

  -- the mean: `∫ x e^{−x} dx = 1`
  ∫-expDist-id : ∫ᴹ {WQ} (ιPre {WQ} expDist) idW ≈ 1#
  ∫-expDist-id = trans (∫-expDist idW)
    (trans (∫ᴹ-cong {WQ} lebPre {mulH {WQ} negExpH idW} {xNegExpH} (λ x → *-comm _ _)) ∫-x)
