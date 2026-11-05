{-# OPTIONS --safe --without-K #-}

-- Uniqueness of measures on the half-line `WQ = [0,∞]` (plan 03, "Uniqueness on the half-line"; `docs/UniquenessLit.md`).
-- Two measures `μ ν : Pre (XW WQ)` are equal (`uniqWQ : μ ≈ᴹ ν`) when
--   * they agree on every dyadic interval [m/2ⁿ, (m+1)/2ⁿ) (`agreeI`),
--   * μ is finite on each [k, k+1) (`finI`), and
--   * they agree on {∞} (`agreeInf`; Lebesgue measure and every density give it mass 0).
-- Route: every test h equals `(h ∘ decode) ∘ code` (`DigitCode.decode-code`), so `∫ᴹ μ h ≈ ∫ᴹ (mapM code μ) (h ∘ decode)`
-- (`SFinite.∫ᴹ-map`).  The pushforwards along `code` are measures on Cantor space whose cells and all-true point have the
-- masses of dyadic intervals and of {∞} (`pushCell`, `pushTop`), so `UniquenessR.uniqR` applies.
module QBS.Continuous.UniquenessWQ where

open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Nat.Base using (_+_; _*_; _^_)
open import Data.List.Base using (length; [])
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
import Relation.Binary.PropositionalEquality as ≡
open import Data.Nat.Properties using (*-identityʳ; +-identityʳ)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Cells using (borelBlk; borelCell; borelTop)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Indicators using (module Indicators)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.SFinite using (module SFinite)
open import QBS.Continuous.Intervals using (module Intervals)
open import QBS.Continuous.DigitCode using (module DigitCode)
open import QBS.Continuous.UniquenessR using (module UniquenessR)

module UniquenessWQ (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; refl; sym; trans; ≤-resp) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd)
  open Indicators A lem using (χ-cong)
  open Weights lem using (WQ)
  open SFinite lem using (XW; ∫ᴹ; _≈ᴹ_; mapM; ∫ᴹ-map; ∫ᴹ-cong; module C)
  open C using (Pre)
  open Intervals lem using (χI; χInf)
  open DigitCode lem using (ℛ; code; decode; val; decode-code; code-cell; code-top)
  open UniquenessR lem using (χR; χR-pt; uniqR)
  open QBS
  open Hom

  -- every test factors through the code
  test-factor : ∀ (h : Hom S WQ WQ) x → map h ⟨$⟩ x ≈ map (_∘H_ S (_∘H_ S h decode) code) ⟨$⟩ x
  test-factor h x = Func.cong (map h) (sym (decode-code x))

  -- the pushforward along the code: cells are dyadic intervals, blocks are unit intervals, the all-true point is ∞
  pushCell : ∀ (p : Pre (XW WQ)) k w →
    ∫ᴹ {ℛ} (mapM code p) (χR (borelCell k w)) ≈ ∫ᴹ {WQ} p (χI (length w) (k * 2 ^ length w + val w))
  pushCell p k w = trans (∫ᴹ-map code p (χR (borelCell k w)))
    (∫ᴹ-cong p (λ x → trans (χR-pt (borelCell k w) (map code ⟨$⟩ x)) (code-cell k w x)))

  pushBlk : ∀ (p : Pre (XW WQ)) k → ∫ᴹ {ℛ} (mapM code p) (χR (borelBlk k)) ≈ ∫ᴹ {WQ} p (χI 0 k)
  pushBlk p k = trans (∫ᴹ-map code p (χR (borelBlk k))) (∫ᴹ-cong p pt)
    where
      idx : k * 2 ^ 0 + 0 ≡.≡ k
      idx = ≡.trans (+-identityʳ _) (*-identityʳ k)
      pt : ∀ x → map (_∘H_ S (χR (borelBlk k)) code) ⟨$⟩ x ≈ map (χI 0 k) ⟨$⟩ x
      pt x = trans (χR-pt (borelBlk k) (map code ⟨$⟩ x))
        (trans (χ-cong (λ y → (λ b → b , tt) , (λ (b , _) → b)) (map code ⟨$⟩ x))
          (trans (code-cell k [] x) (≡.subst (λ j → map (χI 0 (k * 2 ^ 0 + 0)) ⟨$⟩ x ≈ map (χI 0 j) ⟨$⟩ x) idx refl)))

  pushTop : ∀ (p : Pre (XW WQ)) → ∫ᴹ {ℛ} (mapM code p) (χR borelTop) ≈ ∫ᴹ {WQ} p χInf
  pushTop p = trans (∫ᴹ-map code p (χR borelTop)) (∫ᴹ-cong p (λ x → trans (χR-pt borelTop (map code ⟨$⟩ x)) (code-top x)))

  module _ (μ ν : Pre (XW WQ))
           (agreeI : ∀ n m → ∫ᴹ {WQ} μ (χI n m) ≈ ∫ᴹ {WQ} ν (χI n m))
           (finI : ∀ k → Bnd (∫ᴹ {WQ} μ (χI 0 k)))
           (agreeInf : ∫ᴹ {WQ} μ χInf ≈ ∫ᴹ {WQ} ν χInf) where

    -- the pushforwards are equal as measures on Cantor space
    uniqPush : _≈ᴹ_ {ℛ} (mapM code μ) (mapM code ν)
    uniqPush = uniqR (mapM code μ) (mapM code ν)
      (λ k w → trans (pushCell μ k w) (trans (agreeI _ _) (sym (pushCell ν k w))))
      (λ k → let (n , b) = finI k in n , ≤-resp (sym (pushBlk μ k)) refl b)
      (trans (pushTop μ) (trans agreeInf (sym (pushTop ν))))

    uniqWQ : _≈ᴹ_ {WQ} μ ν
    uniqWQ h = trans (∫ᴹ-cong μ (test-factor h))
      (trans (sym (∫ᴹ-map code μ (_∘H_ S h decode)))
        (trans (uniqPush (_∘H_ S h decode))
          (trans (∫ᴹ-map code ν (_∘H_ S h decode)) (sym (∫ᴹ-cong ν (test-factor h))))))
