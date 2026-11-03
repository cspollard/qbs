{-# OPTIONS --safe --without-K #-}

-- Algebra of scaling the tests of Lebesgue measure (helper for `LebesgueScale`): for c · c′ ≈ 1,
--   `Ge a (c x) ↔ Ge (a c′) x`, hence `χ[a,b)(c x) ≈ χ[a c′, b c′)(x)` (`χIv-scale`),
-- and for c finite, `c x = ∞ ↔ x = ∞` (`χInf-scale`).
module QBS.Continuous.LebesgueScaleAlg where

open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base as ℕ using ()
open import Data.Product.Base using (_,_; proj₁; proj₂)

open import QBS.Core
open import QBS.Analysis.LowerReals using (mk⊑; _⊑_)
open import QBS.Classical using (LEM₀)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Continuous.LebesgueDyadicAlg using (module LebesgueDyadicAlg)
open import QBS.Continuous.Weights using (module Weights)
open import QBS.Continuous.Intervals using (module Intervals)

module LebesgueScaleAlg (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _*_; 1#; refl; sym; trans; *-cong; *-assoc; *-comm; *-identityˡ; *-mono; ≤-trans; ≤-reflexive; zeroʳ)
    renaming (Carrier to ∣A∣)
  open Weights lem using (WQ)
  open Intervals lem using (Ge; InIv; χIv; χInf; InInf; InInf-resp; tv-cong)
  open Bounded A using (Bnd; nat; nat-*)
  open Exp A using (natE)
  open LebesgueDyadicAlg lem using (natE≈nat)
  open QBS
  open Hom

  ge⇒≤ : ∀ a x → Ge a x → a ≤ x
  ge⇒≤ a x g = mk⊑ {a} {x} g

  ≤⇒ge : ∀ a x → a ≤ x → Ge a x
  ≤⇒ge a x g = _⊑_.ap {a} {x} g

  -- c′ (c x) ≈ x
  cancelˡ : ∀ c c′ x → c * c′ ≈ 1# → c′ * (c * x) ≈ x
  cancelˡ c c′ x e = trans (sym (*-assoc c′ c x)) (trans (*-cong (trans (*-comm c′ c) e) refl) (*-identityˡ x))

  ge-scale : ∀ c c′ a x → c * c′ ≈ 1# → Ge a (c * x) → Ge (a * c′) x
  ge-scale c c′ a x e g = ≤⇒ge (a * c′) x (≤-trans (≤-reflexive (*-comm a c′))
    (≤-trans (*-mono c′ (ge⇒≤ a (c * x) g)) (≤-reflexive (cancelˡ c c′ x e))))

  ge-unscale : ∀ c c′ a x → c * c′ ≈ 1# → Ge (a * c′) x → Ge a (c * x)
  ge-unscale c c′ a x e g = ≤⇒ge a (c * x) (≤-trans (≤-reflexive (sym (cancelˡ c′ c a (trans (*-comm c′ c) e))))
    (≤-trans (≤-reflexive (*-cong refl (*-comm c′ a)))
    (≤-trans (*-mono c (ge⇒≤ (a * c′) x g)) (≤-reflexive refl))))

  χIv-scale : ∀ c c′ a b x → c * c′ ≈ 1# → map (χIv a b) ⟨$⟩ (c * x) ≈ map (χIv (a * c′) (b * c′)) ⟨$⟩ x
  χIv-scale c c′ a b x e = tv-cong {InIv a b (c * x)} {InIv (a * c′) (b * c′) x}
    (λ (g , n) → ge-scale c c′ a x e g , (λ h → n (ge-unscale c c′ b x e h)))
    (λ (g , n) → ge-unscale c c′ a x e g , (λ h → n (ge-scale c c′ b x e h)))

  -- c k ≤ m k, for c ≤ m, as naturals
  mul-nat : ∀ c m k → c ≤ nat m → c * natE k ≤ natE (m ℕ.* k)
  mul-nat c m k hc = ≤-trans (≤-reflexive (*-comm c (natE k))) (≤-trans (*-mono (natE k) hc)
    (≤-reflexive (trans (*-cong (natE≈nat k) refl) (trans (*-comm (nat k) (nat m))
      (trans (sym (nat-* m k)) (sym (natE≈nat (m ℕ.* k))))))))

  inf-down : ∀ c c′ x → c * c′ ≈ 1# → Bnd c → InInf (c * x) → InInf x
  inf-down c c′ x e (m , hc) g k = ≤⇒ge (natE k) x (≤-trans (≤-reflexive (sym (cancelˡ c c′ (natE k) e)))
    (≤-trans (*-mono c′ (≤-trans (mul-nat c m k hc) (ge⇒≤ (natE (m ℕ.* k)) (c * x) (g (m ℕ.* k)))))
             (≤-reflexive (cancelˡ c c′ x e))))

  inf-up : ∀ c c′ x → c * c′ ≈ 1# → Bnd c′ → InInf x → InInf (c * x)
  inf-up c c′ x e b g = inf-down c′ c (c * x) (trans (*-comm c′ c) e) b
    (InInf-resp (sym (cancelˡ c c′ x e)) g)

  χInf-scale : ∀ c c′ x → c * c′ ≈ 1# → Bnd c → Bnd c′ → map χInf ⟨$⟩ (c * x) ≈ map χInf ⟨$⟩ x
  χInf-scale c c′ x e b b′ = tv-cong {InInf (c * x)} {InInf x} (inf-down c c′ x e b) (inf-up c c′ x e b′)
