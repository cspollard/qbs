{-# OPTIONS --safe --without-K #-}

-- Algebra of the shifted binary expansion `natE j + expansion r` against dyadic intervals (for `LebesgueDyadic`).
--   * `expansion-lt`: off the all-true point, `expansion r` is strictly below 1, so `natE j + expansion r` is not above
--     `natE (j+1)`: some bit is false, and then `expansion r + 2⁻⁽ᵏ⁺¹⁾ ≤ 1` (`expE`), against `hp-pos`;
--   * `shift-cons`: `natE j + expansion (b :: r) = ½ (natE (2j+b) + expansion r)` and `χI-scale`, halving a point halves
--     the dyadic interval, so `χI (n+1) m (½ y) = χI n m y` (via the order isomorphism `HalfOrder.false-iff`);
--   * the pointwise values at level 0: the unit interval `[j, j+1)` and the other `[m, m+1)` off the all-true point.
module QBS.Continuous.LebesgueDyadicAlg where

open import Level using (lift; lower)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Cells using (Top)
open import QBS.Borel.Cons using (consR)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Clopen using (cons)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Fun using (module Measurable)
open import QBS.Analysis.LowerReals using (mk⊑; _⊑_)
open _⊑_ using (ap)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Analysis.HalfOrder using (module HalfOrder)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.BinaryExpansion using (module Expansion)
open import QBS.Analysis.ExpansionCons using (module ExpansionCons)
open import QBS.Analysis.Threshold using (module Threshold)
open import QBS.Continuous.Intervals using (module Intervals)

module LebesgueDyadicAlg (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-trans; ≤-reflexive; ≤-antisym;
    +-mono; *-mono; ≤-+ʳ; ≤-refl; 0-least; +-identityˡ; +-identityʳ; *-identityʳ; distribˡ; +-comm; +-assoc; *-assoc; *-comm)
    renaming (Carrier to ∣A∣)
  open Arch (lowerRealsArch lem) using (half; cancel≤) renaming (half+half to hh)
  open Half A half hh using (hp; hp-double)
  open Exp A using (natE)
  open Bounded A using (nat; Bnd)
  open BoundedCancel A half hh using (cancel-bnd; half-nat; nat-mono)
  open Expansion A half hh using (expansion; expansion≤1; Fun-expansion; sel)
  open ExpansionCons A half hh using (expansion-cons)
  open HalfOrder A (lowerRealsArch lem) using (half≤1; false-iff)
  open Threshold lem using (half≰0)
  open Measurable A using (Fun-resp)
  open Intervals lem using (Ge; InIv; dy; χI; χInf; tv; χIv-cong; tv-cong; χIv-in; χIv-out; χInf-out)
  open QBS
  open Hom

  ----------------------------------------------------------------------------
  -- the naturals, and the positivity of ½ⁿ

  natE≈nat : ∀ j → natE j ≈ nat j
  natE≈nat zero = refl
  natE≈nat (suc j) = trans (+-cong (natE≈nat j) refl) (+-comm _ _)

  bnd-natE : ∀ j → Bnd (natE j)
  bnd-natE j = j , ≤-reflexive (natE≈nat j)

  natE-mono : ∀ {a b} → a ℕ.≤ b → natE a ≤ natE b
  natE-mono {a} {b} h = ≤-trans (≤-reflexive (natE≈nat a)) (≤-trans (nat-mono h) (≤-reflexive (sym (natE≈nat b))))

  one≉zero : 1# ≈ 0# → ⊥
  one≉zero e = half≰0 (≤-trans half≤1 (≤-reflexive e))

  hp-pos : ∀ n → hp (suc n) ≤ 0# → ⊥
  hp-pos zero h = half≰0 (≤-trans (≤-reflexive (sym (*-identityʳ half))) h)
  hp-pos (suc n) h = hp-pos n (≤-trans (≤-reflexive (sym (hp-double (suc n))))
    (≤-trans (+-mono h h) (≤-reflexive (+-identityˡ 0#))))

  ----------------------------------------------------------------------------
  -- a false bit keeps the expansion below 1

  tailR : R₁ → R₁
  tailR r = lift (λ n → lower r (suc n))

  exp-split : ∀ r → expansion r ≈ sel (lower r 0) half + half * expansion (tailR r)
  exp-split r = trans (sym (Fun-resp lem Fun-expansion {x = consR (lower r 0) (tailR r)} {y = r} pt))
    (expansion-cons (lower r 0) (tailR r))
    where
      pt : ∀ n → cons (lower r 0) (lower (tailR r)) n ≡ lower r n
      pt zero = ≡.refl
      pt (suc n) = ≡.refl

  sel-bound : ∀ b → sel b half + half * 1# ≤ 1#
  sel-bound true = ≤-reflexive (trans (+-cong refl (*-identityʳ half)) hh)
  sel-bound false = ≤-trans (≤-reflexive (trans (+-identityˡ _) (*-identityʳ half))) half≤1

  step-e : ∀ b {e e′ p} → e ≈ sel b half + half * e′ → e′ + p ≤ 1# → e + half * p ≤ 1#
  step-e b {e} {e′} {p} eq c = ≤-trans
    (≤-reflexive (trans (+-cong eq refl) (trans (+-assoc _ _ _) (+-cong refl (sym (distribˡ half e′ p))))))
    (≤-trans (+-mono ≤-refl (*-mono half c)) (sel-bound b))

  expE : ∀ k r → lower r k ≡ false → expansion r + hp (suc k) ≤ 1#
  expE zero r e0 = ≤-trans (≤-reflexive (+-cong eq refl))
    (≤-trans (+-mono (*-mono half (expansion≤1 _)) ≤-refl) (≤-reflexive (hp-double 0)))
    where
      eq : expansion r ≈ half * expansion (tailR r)
      eq = trans (exp-split r)
        (≡.subst (λ b → sel b half + half * expansion (tailR r) ≈ half * expansion (tailR r)) (≡.sym e0) (+-identityˡ _))
  expE (suc k) r ek = step-e (lower r 0) (exp-split r) (expE k (tailR r) ek)

  not-top : ∀ (r : R₁) → (Top (lower r) → ⊥) → Σ ℕ (λ k → lower r k ≡ false)
  not-top r nt with lem (Σ ℕ (λ k → lower r k ≡ false))
  ... | inj₁ w = w
  ... | inj₂ none = ⊥-elim (nt all)
    where
      all : ∀ i → lower r i ≡ true
      all i with lower r i in e
      ... | true = ≡.refl
      ... | false = ⊥-elim (none (i , e))

  -- off the all-true point, `natE j + expansion r` is below `natE (j+1)`
  expansion-lt-k : ∀ j (r : R₁) k → lower r k ≡ false → Ge (natE (suc j)) (natE j + expansion r) → ⊥
  expansion-lt-k j r k ek g = hp-pos k (cancel≤ {1#} {hp (suc k)} {0#} ≤-refl step)
    where
      eq : natE j + 1# ≈ natE j + expansion r
      eq = ≤-antisym {natE j + 1#} {natE j + expansion r} (mk⊑ g) (+-mono ≤-refl (expansion≤1 r))
      one≈e : 1# ≈ expansion r
      one≈e = cancel-bnd {natE j} {1#} {expansion r} (bnd-natE j) eq
      s1 : 1# + hp (suc k) ≈ expansion r + hp (suc k)
      s1 = +-cong one≈e refl
      step : 1# + hp (suc k) ≤ 1# + 0#
      step = ≤-trans (≤-reflexive s1) (≤-trans (expE k r ek) (≤-reflexive (sym (+-identityʳ 1#))))

  expansion-lt : ∀ j (r : R₁) → (Top (lower r) → ⊥) → Ge (natE (suc j)) (natE j + expansion r) → ⊥
  expansion-lt j r nt g = expansion-lt-k j r (proj₁ (not-top r nt)) (proj₂ (not-top r nt)) g

  ----------------------------------------------------------------------------
  -- halving: the first bit and the dyadic intervals

  jb : ℕ → Bool → ℕ
  jb j true = suc (2 ℕ.* j)
  jb j false = 2 ℕ.* j

  half-natE : ∀ j → half * natE (2 ℕ.* j) ≈ natE j
  half-natE j = ≡.subst (λ k → half * natE k ≈ natE j) (≡.sym (≡.cong (j ℕ.+_) (ℕ.+-identityʳ j)))
    (trans (*-cong refl (natE≈nat (j ℕ.+ j))) (trans (half-nat j) (sym (natE≈nat j))))

  sel-nat : ∀ j b → natE j + sel b half ≈ half * natE (jb j b)
  sel-nat j false = trans (+-identityʳ _) (sym (half-natE j))
  sel-nat j true = trans (+-cong (sym (half-natE j)) (sym (*-identityʳ half))) (sym (distribˡ half _ _))

  shift-cons : ∀ j b r → natE j + expansion (consR b r) ≈ half * (natE (jb j b) + expansion r)
  shift-cons j b r = trans (+-cong refl (expansion-cons b r)) (trans (sym (+-assoc _ _ _))
    (trans (+-cong (sel-nat j b) refl) (sym (distribˡ half _ _))))

  dy-half : ∀ n m → dy (suc n) m ≈ half * dy n m
  dy-half n m = trans (sym (*-assoc _ _ _)) (trans (*-cong (*-comm _ _) refl) (*-assoc _ _ _))

  -- the dyadic interval at level n+1 at ½y is the one at level n at y
  χI-scale : ∀ n m y → map (χI (suc n) m) ⟨$⟩ (half * y) ≈ map (χI n m) ⟨$⟩ y
  χI-scale n m y = trans (χIv-cong (half * y) (dy-half n m) (dy-half n (suc m))) (tv-cong f g)
    where
      a = dy n m
      b = dy n (suc m)
      f : InIv (half * a) (half * b) (half * y) → InIv a b y
      f (g₁ , nb) = ap (proj₁ (false-iff {x = a} {y = y} refl) (mk⊑ g₁))
        , (λ h → nb (ap (proj₂ (false-iff {x = b} {y = y} refl) (mk⊑ h))))
      g : InIv a b y → InIv (half * a) (half * b) (half * y)
      g (g₁ , nb) = ap (proj₂ (false-iff {x = a} {y = y} refl) (mk⊑ g₁))
        , (λ h → nb (ap (proj₁ (false-iff {x = b} {y = y} refl) (mk⊑ h))))

  ----------------------------------------------------------------------------
  -- level 0: `natE j + expansion r` against [m, m+1)

  dy0 : ∀ m → dy 0 m ≈ natE m
  dy0 m = *-identityʳ _

  ge-mono : ∀ {a b x} → a ≤ b → Ge b x → Ge a x
  ge-mono le g q m = g q (ap le q m)

  le→Ge : ∀ {a x} → a ≤ x → Ge a x
  le→Ge h = ap h

  base-in : ∀ j (r : R₁) → (Top (lower r) → ⊥) → map (χI 0 j) ⟨$⟩ (natE j + expansion r) ≈ 1#
  base-in j r nt = χIv-in (dy 0 j) (dy 0 (suc j)) (natE j + expansion r) (g₁ , g₂)
    where
      g₁ : Ge (dy 0 j) (natE j + expansion r)
      g₁ = le→Ge (≤-trans (≤-reflexive (dy0 j)) (≤-+ʳ {natE j} {expansion r}))
      g₂ : Ge (dy 0 (suc j)) (natE j + expansion r) → ⊥
      g₂ g = expansion-lt j r nt (ge-mono {natE (suc j)} {dy 0 (suc j)} {natE j + expansion r} (≤-reflexive (sym (dy0 (suc j)))) g)

  base-lt : ∀ j m (r : R₁) → suc m ℕ.≤ j → map (χI 0 m) ⟨$⟩ (natE j + expansion r) ≈ 0#
  base-lt j m r lt = χIv-out (dy 0 m) (dy 0 (suc m)) (natE j + expansion r) f
    where
      f : InIv (dy 0 m) (dy 0 (suc m)) (natE j + expansion r) → ⊥
      f (_ , n) = n (le→Ge (≤-trans (≤-reflexive (dy0 (suc m))) (≤-trans (natE-mono lt) (≤-+ʳ {natE j} {expansion r}))))

  base-gt : ∀ j m (r : R₁) → suc j ℕ.≤ m → (Top (lower r) → ⊥) → map (χI 0 m) ⟨$⟩ (natE j + expansion r) ≈ 0#
  base-gt j m r gt nt = χIv-out (dy 0 m) (dy 0 (suc m)) (natE j + expansion r) f
    where
      le : natE (suc j) ≤ dy 0 m
      le = ≤-trans (natE-mono gt) (≤-reflexive (sym (dy0 m)))
      f : InIv (dy 0 m) (dy 0 (suc m)) (natE j + expansion r) → ⊥
      f (g , _) = expansion-lt j r nt (ge-mono {natE (suc j)} {dy 0 m} {natE j + expansion r} le g)

  tv≤1 : ∀ P → tv P ≤ 1#
  tv≤1 P with lem P
  ... | inj₁ _ = ≤-refl
  ... | inj₂ _ = 0-least

  χI≤1 : ∀ n m x → map (χI n m) ⟨$⟩ x ≤ 1#
  χI≤1 n m x = tv≤1 _

  ----------------------------------------------------------------------------
  -- ∞ is never reached: natE j + expansion r ≤ natE (j+1)

  no-succ : ∀ j → natE (suc j) ≤ natE j → ⊥
  no-succ j h = one≉zero (cancel-bnd (bnd-natE j)
    (≤-antisym (≤-trans h (≤-reflexive (sym (+-identityʳ _)))) (+-mono ≤-refl 0-least)))

  inf-out : ∀ j (r : R₁) → map χInf ⟨$⟩ (natE j + expansion r) ≈ 0#
  inf-out j r = χInf-out _ (λ f → no-succ (suc j) (≤-trans (mk⊑ (f (suc (suc j)))) (+-mono ≤-refl (expansion≤1 r))))

  -- halving the first bit: the shifted point at `b :: r` against level n+1 is the shifted point at `r` against level n
  step-pt : ∀ n m j b (r : R₁) → map (χI (suc n) m) ⟨$⟩ (natE j + expansion (consR b r)) ≈
    map (χI n m) ⟨$⟩ (natE (jb j b) + expansion r)
  step-pt n m j b r = trans (Func.cong (map (χI (suc n) m)) (shift-cons j b r)) (χI-scale n m _)
