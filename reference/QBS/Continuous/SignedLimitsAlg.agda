{-# OPTIONS --safe --without-K #-}

-- Algebra behind `SignedLimits`: inequalities in an `OmegaSemiring` with finite elements.
--   * `cancel-le`: c + x ≤ c + y gives x ≤ y for a finite c (`LowerRealsNear.cancel-bnd-⊑`);
--   * `cong-le`: the tolerance form of `≃` invariance: from A + M ≤ L + B + h and the cross-added equalities of
--     a ≃ a′ (witness c) and l ≃ l′ (witness d), A′ + M′ ≤ L′ + B′ + h (add the finite X = B + c + M + d, cancel);
--   * `two-hp`: 2ʲ · ½ʲ⁺ᵏ ≈ ½ᵏ, hence `small-scale`: (p + n) · ½ᵐ⁺ᵏ ≤ ½ᵏ when p + n ≤ m;
--   * `scale-ineq`: for a signed constant c = c⁺ − c⁻ the tolerance of a − b → u − v scales to that of c·a − c·b.
-- Route: each step is a ring identity (`solve`) between monotone steps; `two-hp` by induction on j with `double-half`.
module QBS.Continuous.SignedLimitsAlg where

open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open import QBS.Classical using (LEM₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.CoinIntegral using (lemOf)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.LowerRealsNear using (module Near)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Signed using (SubSemiring)
open import QBS.Continuous.LebesgueShiftAlg using (module LebesgueShiftAlg)

module SignedLimitsAlg (lem₁ : LEM₁) where
  open Lebesgue (lemOf lem₁) using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; refl; sym; trans; +-cong; *-cong; *-comm; *-identityˡ; +-identityʳ; +-mono;
    *-mono; ≤-trans; ≤-reflexive; commutativeSemiring) renaming (Carrier to ∣A∣)
  open Bounded A using (Bnd; nat; nat-+; finite)
  open SubSemiring finite using (Is-+)
  open Arch (lowerRealsArch (lemOf lem₁)) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open BoundedCancel A half hh using (suc≤2^; nat-mono; double-half; 2^-suc)
  open Near (lemOf lem₁) using (cancel-bnd-⊑)
  open LebesgueShiftAlg (lemOf lem₁) using (bnd-rat)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  cancel-le : ∀ {c x y} → Bnd c → c + x ≤ c + y → x ≤ y
  cancel-le {c} bc = cancel-bnd-⊑ {c} (bnd-rat c bc)

  -- the algebra of `cong-le`, as two chains
  cong-lhs : ∀ A B A′ B′ L M L′ M′ c d → A + B′ + c ≈ A′ + B + c → L + M′ + d ≈ L′ + M + d →
    (B + c + M + d) + (A′ + M′) ≈ (A + M) + (B′ + c + M′ + d)
  cong-lhs A B A′ B′ L M L′ M′ c d e₃ e₄ = trans (solve 8 (λ A′ B c M′ M d x y → (B :+ c :+ M :+ d) :+ (A′ :+ M′) :=
      (A′ :+ B :+ c) :+ M′ :+ (M :+ d)) refl A′ B c M′ M d A′ A′)
    (trans (+-cong (+-cong (sym e₃) refl) refl) (solve 7 (λ A B′ c M′ M d x → (A :+ B′ :+ c) :+ M′ :+ (M :+ d) :=
      (A :+ M) :+ (B′ :+ c :+ M′ :+ d)) refl A B′ c M′ M d A))

  cong-rhs : ∀ B B′ L M L′ M′ c d h → L + M′ + d ≈ L′ + M + d →
    (L + B + h) + (B′ + c + M′ + d) ≈ (B + c + M + d) + (L′ + B′ + h)
  cong-rhs B B′ L M L′ M′ c d h e₄ = trans (solve 9 (λ L B h B′ c M′ d x y → (L :+ B :+ h) :+ (B′ :+ c :+ M′ :+ d) :=
      (L :+ M′ :+ d) :+ (B :+ B′ :+ c :+ h)) refl L B h B′ c M′ d L L)
    (trans (+-cong e₄ refl) (solve 9 (λ L′ M d B B′ c h x y → (L′ :+ M :+ d) :+ (B :+ B′ :+ c :+ h) :=
      (B :+ c :+ M :+ d) :+ (L′ :+ B′ :+ h)) refl L′ M d B B′ c h L′ L′))

  cong-le : ∀ A B A′ B′ L M L′ M′ c d h → Bnd B → Bnd M → Bnd c → Bnd d → A + M ≤ L + B + h →
    A + B′ + c ≈ A′ + B + c → L + M′ + d ≈ L′ + M + d → A′ + M′ ≤ L′ + B′ + h
  cong-le A B A′ B′ L M L′ M′ c d h bB bM bc bd le e₃ e₄ =
    cancel-le {B + c + M + d} (Is-+ {_} {_} (Is-+ {_} {_} (Is-+ {_} {_} bB bc) bM) bd)
      (≤-trans (≤-reflexive (cong-lhs A B A′ B′ L M L′ M′ c d e₃ e₄))
        (≤-trans (+-mono le (≤-reflexive refl)) (≤-reflexive (cong-rhs B B′ L M L′ M′ c d h e₄))))

  -- 2ʲ · ½ʲ⁺ᵏ = ½ᵏ
  nat≈ : ∀ {n m} → n ≡ m → nat n ≈ nat m
  nat≈ e = ≡.subst (λ m → nat _ ≈ nat m) e refl

  two-hp : ∀ j k → nat (2 ℕ.^ j) * hp (j ℕ.+ k) ≈ hp k
  two-hp zero k = trans (*-cong (+-identityʳ 1#) refl) (*-identityˡ _)
    where open OmegaSemiring A using (1#)
  two-hp (suc j) k = trans (*-cong (trans (nat≈ (2^-suc j)) (nat-+ _ _)) refl)
    (trans (solve 3 (λ n h t → (n :+ n) :* (h :* t) := h :* (n :* t) :+ h :* (n :* t)) refl (nat (2 ℕ.^ j)) half (hp (j ℕ.+ k)))
      (trans (+-cong (*-cong refl (two-hp j k)) (*-cong refl (two-hp j k))) (double-half _)))

  small-scale : ∀ {s} k m → s ≤ nat m → s * hp (m ℕ.+ k) ≤ hp k
  small-scale {s} k m le = ≤-trans (≤-reflexive (*-comm s _)) (≤-trans (*-mono (hp (m ℕ.+ k)) (≤-trans le
    (nat-mono (ℕP.≤-trans (ℕP.n≤1+n m) (suc≤2^ m))))) (≤-reflexive (trans (*-comm _ _) (two-hp m k))))

  -- scaling the tolerance by c = c⁺ − c⁻ (with (c⁺ + c⁻) · h′ ≤ hk)
  scale-ineq : ∀ cp cn A B L M h′ hk → (cp + cn) * h′ ≤ hk → A + M ≤ L + B + h′ → L + B ≤ A + M + h′ →
    (cp * A + cn * B) + (cp * M + cn * L) ≤ (cp * L + cn * M) + (cp * B + cn * A) + hk
  scale-ineq cp cn A B L M h′ hk sm h₁ h₂ = ≤-trans (≤-reflexive (solve 6 (λ cp cn A B L M →
      (cp :* A :+ cn :* B) :+ (cp :* M :+ cn :* L) := cp :* (A :+ M) :+ cn :* (L :+ B)) refl cp cn A B L M))
    (≤-trans (+-mono (*-mono cp h₁) (*-mono cn h₂)) (≤-trans (≤-reflexive (solve 7 (λ cp cn A B L M h →
      cp :* (L :+ B :+ h) :+ cn :* (A :+ M :+ h) := (cp :* L :+ cn :* M) :+ (cp :* B :+ cn :* A) :+ (cp :+ cn) :* h)
      refl cp cn A B L M h′)) (+-mono (≤-reflexive refl) sm)))
