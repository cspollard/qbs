{-# OPTIONS --safe --without-K #-}

-- The measure with density `v : R → [0,∞]` against a measure `m`, scaled by a constant `d`:
-- `I h = d · J m (v · h)`.  It is a sub-probability measure when `d · ∫v dm ≤ 1`, and a probability
-- measure when this is an equality.  Its integral of an unbounded function is again `d · J m (v · φ)`.
module QBS.Analysis.Density where

open import Level using (suc; zero)
open import Function.Base using (const)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.JParam using (module JParam)

module Density (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open JParam lem
  open Meas lem
  open LevelSets lem using (LS)
  open OmegaSemiring A using (_≈_; _≤_; _*_; _+_; 1#; ⨆; Increasing; refl; sym; trans; *-cong; +-cong; ⨆-cong;
    *-mono; ≤-trans; ≤-reflexive; *-identityʳ; *-assoc; *-comm; distribˡ; *-⨆; ⨆-lub; ≤-antisym; 0#; zeroʳ)
  open Integration A using (Measure; IsProb; I; mass)
  open Measurable A using (Fun; Fun-const)
  module M = Measure

  private
    swap : ∀ x y z → x * (y * z) ≈ y * (x * z)
    swap x y z = trans (sym (*-assoc x y z)) (trans (*-cong (*-comm x y) refl) (*-assoc y x z))

  -- v · h is measurable when v is and h is a bounded measurable function
  Mvh : ∀ {v h} → Meas v → Fun h → Meas (λ r → v r * h r)
  Mvh {v} {h} mv f = Meas-⊗ {v} {h} mv (LS f)

  -- monotone convergence for the density measure
  densSup : ∀ (m : Measure) (v : R₁ → Cut) (mv : Meas v) (d : Cut) {h} (hs : ℕ → R₁ → Cut)
    (fs : ∀ n → Fun (hs n)) (inc : ∀ x → Increasing (λ n → hs n x)) (f : Fun h) →
    (∀ x → h x ≈ ⨆ (λ n → hs n x) (inc x)) →
    d * J m (λ r → v r * h r) (Mvh {v} {h} mv f) ≈
      ⨆ (λ n → d * J m (λ r → v r * hs n r) (Mvh {v} {hs n} mv (fs n)))
        (λ n → *-mono d
            (J-mono m (Mvh {v} {hs n} mv (fs n)) (Mvh {v} {hs (ℕ.suc n)} mv (fs (ℕ.suc n))) (λ r → *-mono (v r) (inc r n))))
  densSup m v mv d {h} hs fs inc f e = trans
    (*-cong refl (J-⨆ m {λ r → v r * h r} (λ n r → v r * hs n r) (λ n → Mvh {v} {hs n} mv (fs n))
      (λ r n → *-mono (v r) (inc r n)) (Mvh {v} {h} mv f)
      (λ r → trans (*-cong refl (e r)) (*-⨆ (v r) (λ n → hs n r) (inc r) (λ n → *-mono (v r) (inc r n))))))
    (*-⨆ d (λ n → J m (λ r → v r * hs n r) (Mvh {v} {hs n} mv (fs n)))
       (λ n → J-mono m (Mvh {v} {hs n} mv (fs n)) (Mvh {v} {hs (ℕ.suc n)} mv (fs (ℕ.suc n))) (λ r → *-mono (v r) (inc r n)))
       (λ n → *-mono d
           (J-mono m (Mvh {v} {hs n} mv (fs n)) (Mvh {v} {hs (ℕ.suc n)} mv (fs (ℕ.suc n))) (λ r → *-mono (v r) (inc r n)))))

  densM : ∀ (m : Measure) (v : R₁ → Cut) (mv : Meas v) (d : Cut) → d * J m v mv ≤ 1# → Measure
  densM m v mv d bd = record
    { I = λ h f → d * J m (λ r → v r * h r) (Mvh {v} {h} mv f)
    ; I-mono = λ {h} {h′} f f′ le → *-mono d
        (J-mono m (Mvh {v} {h} mv f) (Mvh {v} {h′} mv f′) (λ r → *-mono (v r) (le r)))
    ; I-add = λ {h} {h₁} {h₂} f f₁ f₂ e →
        trans (*-cong refl (trans
          (J-cong m (Mvh {v} {h} mv f) (Meas-⊕ {λ r → v r * h₁ r} {λ r → v r * h₂ r} (Mvh {v} {h₁} mv f₁) (Mvh {v} {h₂} mv f₂))
             (λ r → trans (*-cong refl (e r)) (distribˡ (v r) (h₁ r) (h₂ r))))
          (J-add m {λ r → v r * h₁ r} {λ r → v r * h₂ r} (Mvh {v} {h₁} mv f₁) (Mvh {v} {h₂} mv f₂))))
          (distribˡ d (J m (λ r → v r * h₁ r) (Mvh {v} {h₁} mv f₁)) (J m (λ r → v r * h₂ r) (Mvh {v} {h₂} mv f₂)))
    ; I-scale = λ {h} {h′} c f f′ e →
        trans (*-cong refl (trans
          (J-cong m (Mvh {v} {h′} mv f′) (Meas-⊗ {λ _ → c} {λ r → v r * h r} (Meas-const c) (Mvh {v} {h} mv f))
             (λ r → trans (*-cong refl (e r)) (swap (v r) c (h r))))
          (J-scale m c {λ r → v r * h r} (Mvh {v} {h} mv f))))
          (swap d c (J m (λ r → v r * h r) (Mvh {v} {h} mv f)))
    ; I-sup = λ {h} hs fs inc f e → densSup m v mv d {h} hs fs inc f e
    ; I-sub = λ f → ≤-trans (*-mono d (J-mono m (Mvh {v} {const 1#} mv f) mv (λ r → ≤-reflexive (*-identityʳ (v r))))) bd
    }

  -- `v · φ` is the supremum of the bounded approximations `v · (pw k · tr k φ)`, whose integrals
  -- against `m` therefore increase to `J m (v · φ)`.
  module Approx (m : Measure) (v : R₁ → Cut) (mv : Meas v) {φ} (p : Meas φ) where
    F = FunInf-Meas {φ} p

    φs : ℕ → R₁ → Cut
    φs k r = v r * (pw k * tr k (φ r))

    ps : ∀ k → Meas (φs k)
    ps k = Meas-⊗ {v} {λ r → pw k * tr k (φ r)} mv (Meas-⊗ {λ _ → pw k} {λ r → tr k (φ r)} (Meas-const (pw k)) (LS (F k)))

    incv : ∀ r → Increasing (λ k → φs k r)
    incv r k = *-mono (v r) (incφ φ r k)

    ev : ∀ r → v r * φ r ≈ ⨆ (λ k → φs k r) (incv r)
    ev r = trans (*-cong refl (eqφ φ r)) (*-⨆ (v r) (λ k → pw k * tr k (φ r)) (incφ φ r) (incv r))

    incJ : Increasing (λ k → J m (φs k) (ps k))
    incJ k = J-mono m (ps k) (ps (ℕ.suc k)) (λ r → incv r k)

    -- `J m (v · φ)` is the supremum of the approximations' integrals
    J-approx : J m (λ r → v r * φ r) (Meas-⊗ {v} {φ} mv p) ≈ ⨆ (λ k → J m (φs k) (ps k)) incJ
    J-approx = J-⨆ m {λ r → v r * φ r} φs ps incv (Meas-⊗ {v} {φ} mv p) ev

    -- each approximation is again an integral against `m`, after pulling out the constant `2ᵏ`
    J-approx-pt : ∀ k → J m (φs k) (ps k) ≈ pw k * J m (λ r → v r * tr k (φ r)) (Mvh {v} {λ r → tr k (φ r)} mv (F k))
    J-approx-pt k = trans
      (J-cong m (ps k) (Meas-⊗ {λ _ → pw k} {λ r → v r * tr k (φ r)} (Meas-const (pw k)) (Mvh {v} {λ r → tr k (φ r)} mv (F k)))
         (λ r → swap (v r) (pw k) (tr k (φ r))))
      (J-scale m (pw k) {λ r → v r * tr k (φ r)} (Mvh {v} {λ r → tr k (φ r)} mv (F k)))

  -- the integral of an unbounded function against the density measure
  J-dens : ∀ (m : Measure) (v : R₁ → Cut) (mv : Meas v) (d : Cut) (bd : d * J m v mv ≤ 1#) {φ} (p : Meas φ) →
    J (densM m v mv d bd) φ p ≈ d * J m (λ r → v r * φ r) (Meas-⊗ {v} {φ} mv p)
  J-dens m v mv d bd {φ} p = trans (J-def (densM m v mv d bd) p)
    (sym (trans (*-cong refl J-approx)
      (trans (*-⨆ d (λ k → J m (φs k) (ps k)) incJ (λ k → *-mono d (incJ k)))
        (⨆-cong (λ k → *-mono d (incJ k)) (Iseq-inc (densM m v mv d bd) φ F) pt))))
    where
      open Approx m v mv p

      pt : ∀ k → d * J m (φs k) (ps k) ≈ Iseq (densM m v mv d bd) φ F k
      pt k = trans (*-cong refl (J-approx-pt k)) (swap d (pw k) _)

  -- a null density integrates everything to 0, even `∞`
  J-null : ∀ (m : Measure) (v : R₁ → Cut) (mv : Meas v) {φ} (p : Meas φ) →
    J m v mv ≈ 0# → J m (λ r → v r * φ r) (Meas-⊗ {v} {φ} mv p) ≈ 0#
  J-null m v mv {φ} p z = ≤-antisym
    (≤-trans (≤-reflexive J-approx) (⨆-lub (λ k → J m (φs k) (ps k)) incJ bound))
    (OmegaSemiring.0-least A)
    where
      open Approx m v mv p

      -- each approximation is below `2ᵏ · v`, which has integral 0
      bound : ∀ k → J m (φs k) (ps k) ≤ 0#
      bound k = ≤-trans
        (J-mono m (ps k) (Meas-⊗ {λ _ → pw k} {v} (Meas-const (pw k)) mv)
           (λ r → ≤-trans (≤-reflexive (swap (v r) (pw k) (tr k (φ r))))
                    (≤-trans (*-mono (pw k) (≤-trans (*-mono (v r) (tr-≤1 k (φ r))) (≤-reflexive (*-identityʳ (v r)))))
                       (≤-reflexive refl))))
        (≤-reflexive (trans (J-scale m (pw k) {v} mv) (trans (*-cong refl z) (zeroʳ (pw k)))))
