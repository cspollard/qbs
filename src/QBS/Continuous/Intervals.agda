{-# OPTIONS --safe --without-K #-}

-- Interval tests on `WQ = [0,∞]` (plan 03, "Uniqueness on the half-line").
--   * `χIv a b`, the indicator of [a, b) (for cuts a, b), and `χInf`, the indicator of {∞};
--   * `dy n m = m / 2ⁿ` and the dyadic intervals `χI n m = χIv (dy n m) (dy n (m+1))`, with `χI-split`, the halving of a
--     dyadic interval.
-- Membership `a ≤ x` (`Ge`, the order of cuts at the level of `Set`) is decided by excluded middle.  The tests are
-- measurable because `{r | a ≤ h r}` is Borel for every threshold-measurable h: it is the countable intersection of the
-- threshold sets {r | q ∈ h r} over the rationals q ∈ a (`ge-borel`).
module QBS.Continuous.Intervals where

open import Level using (lift)
open import Function.Bundles using (_⟨$⟩_)
open import Data.Nat.Base using (ℕ; suc; _*_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

open import QBS.Core
open import QBS.Classical using (LEM₀)
open import QBS.Borel.Core using (Borel; ⋂; compl; inter₂; resp)
open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.LowerReals using (module Cut; _⊑_)
open Cut using (mem)
open _⊑_ using (ap)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.LevelSets using (module LevelSets)
open import QBS.Analysis.DyadicAlg using (module AlgDy)
import Data.Nat.Properties as ℕ
open import QBS.Analysis.DigitAlg using (module AlgDigit)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Half using (module Half)
open import QBS.Continuous.Sample using (S)
open import QBS.Continuous.Weights using (module Weights)

module Intervals (lem : LEM₀) where
  open Lebesgue lem using (A)
  open OmegaSemiring A using (_≈_; _≤_; _+_; 0#; 1#; refl; sym; trans; +-cong; +-identityˡ; +-identityʳ; ≤-trans; ≤-reflexive) renaming (Carrier to ∣A∣; _*_ to _·_)
  open Meas lem using (Meas; all-enum; imp-borel)
  open LevelSets lem using (LS-ind)
  open Exp A using (natE)
  open Arch (lowerRealsArch lem) using (half) renaming (half+half to hh)
  open Half A half hh using (hp)
  open AlgDigit A half hh using (dy-dbl; dy-mono; dbl-*2)
  open AlgDy A half hh using (dbl)
  open Weights lem using (WQ)
  open QBS
  open Hom

  -- `a ≤ x`, at the level of `Set` (it is `_≤_` of the cuts, unfolded to membership, so that it can be a Borel predicate)
  Ge : ∣A∣ → ∣A∣ → Set
  Ge a x = ∀ q → mem a q → mem x q

  -- membership of a point of [0,∞] in [a, b), and in {∞}
  InIv : ∣A∣ → ∣A∣ → ∣A∣ → Set
  InIv a b x = Ge a x × (Ge b x → ⊥)

  InInf : ∣A∣ → Set
  InInf x = ∀ k → Ge (natE k) x

  -- `a ≤ h r` is a Borel condition on r
  ge-borel : ∀ a {h : R₁ → ∣A∣} → Meas h → Borel (λ c → Ge a (h (lift c)))
  ge-borel a {h} m = all-enum (λ ρ c → mem a ρ → mem (h (lift c)) ρ) (λ ρ → imp-borel (mem a ρ) (m ρ))

  ----------------------------------------------------------------------------
  -- the indicator tests

  -- the truth value of a proposition, `1#` or `0#` (by excluded middle)
  tv : Set → ∣A∣
  tv P with lem P
  ... | inj₁ _ = 1#
  ... | inj₂ _ = 0#

  tv-in : ∀ {P} → P → tv P ≈ 1#
  tv-in {P} p with lem P
  ... | inj₁ _ = refl
  ... | inj₂ np = ⊥-elim (np p)

  tv-out : ∀ {P} → (P → ⊥) → tv P ≈ 0#
  tv-out {P} np with lem P
  ... | inj₁ p = ⊥-elim (np p)
  ... | inj₂ _ = refl

  tv-cong : ∀ {P Q} → (P → Q) → (Q → P) → tv P ≈ tv Q
  tv-cong {P} {Q} f g = [ (λ p → trans (tv-in p) (sym (tv-in (f p))))
                        , (λ np → trans (tv-out np) (sym (tv-out (λ q → np (g q))))) ]′ (lem P)

  -- a test from a predicate on points that respects `≈` and is Borel along measurable probes
  indH : (P : ∣A∣ → Set) → (∀ {x y} → x ≈ y → P x → P y) →
    (∀ {α : R₁ → ∣A∣} → Meas α → Borel (λ c → P (α (lift c)))) → Hom S WQ WQ
  indH P pr bP = record
    { map = record { to = λ x → tv (P x); cong = λ e → tv-cong (pr e) (pr (OmegaSemiring.sym A e)) }
    ; map-random = λ {α} m → LS-ind {λ c → P (α ⟨$⟩ lift c)} {λ r → tv (P (α ⟨$⟩ r))} 1# (bP m)
        (λ x p → tv-in p) (λ x np → tv-out np) }

  Ge-resp : ∀ {a x y} → x ≈ y → Ge a x → Ge a y
  Ge-resp e g q m = ap (proj₁ e) q (g q m)

  Ge-≈ : ∀ {a a′ x} → a ≈ a′ → Ge a x → Ge a′ x
  Ge-≈ e g q m = g q (ap (proj₂ e) q m)

  InIv-resp : ∀ a b {x y} → x ≈ y → InIv a b x → InIv a b y
  InIv-resp a b e (g , n) = Ge-resp {a} e g , (λ h → n (Ge-resp {b} (OmegaSemiring.sym A e) h))

  χIv : ∣A∣ → ∣A∣ → Hom S WQ WQ
  χIv a b = indH (InIv a b) (InIv-resp a b)
    (λ m → inter₂ (ge-borel a m) (compl (ge-borel b m)))

  χIv-in : ∀ a b x → InIv a b x → map (χIv a b) ⟨$⟩ x ≈ 1#
  χIv-in a b x = tv-in

  χIv-out : ∀ a b x → (InIv a b x → ⊥) → map (χIv a b) ⟨$⟩ x ≈ 0#
  χIv-out a b x = tv-out

  InInf-resp : ∀ {x y} → x ≈ y → InInf x → InInf y
  InInf-resp e f k = Ge-resp {natE k} e (f k)

  χInf : Hom S WQ WQ
  χInf = indH InInf InInf-resp (λ m → ⋂ (λ k → ge-borel (natE k) m))

  χInf-in : ∀ x → InInf x → map χInf ⟨$⟩ x ≈ 1#
  χInf-in x = tv-in

  χInf-out : ∀ x → (InInf x → ⊥) → map χInf ⟨$⟩ x ≈ 0#
  χInf-out x = tv-out

  ----------------------------------------------------------------------------
  -- dyadic intervals

  dy : ℕ → ℕ → ∣A∣
  dy n m = natE m · hp n

  χI : ℕ → ℕ → Hom S WQ WQ
  χI n m = χIv (dy n m) (dy n (suc m))

  -- [m/2ⁿ, (m+1)/2ⁿ) is the disjoint union of its two halves
  χIv-cong : ∀ {a a′ b b′} x → a ≈ a′ → b ≈ b′ → map (χIv a b) ⟨$⟩ x ≈ map (χIv a′ b′) ⟨$⟩ x
  χIv-cong {a} {a′} {b} {b′} x ea eb = tv-cong f g
    where
      f : InIv a b x → InIv a′ b′ x
      f (g₁ , n) = Ge-≈ {x = x} ea g₁ , (λ h → n (Ge-≈ {x = x} (OmegaSemiring.sym A eb) h))
      g : InIv a′ b′ x → InIv a b x
      g (g₁ , n) = Ge-≈ {x = x} (OmegaSemiring.sym A ea) g₁ , (λ h → n (Ge-≈ {x = x} eb h))

  -- [a, b) is the union of [a, c) and [c, b) when a ≤ c ≤ b
  split-iv : ∀ a c b x → Ge a c → Ge c b → map (χIv a b) ⟨$⟩ x ≈ (map (χIv a c) ⟨$⟩ x) + (map (χIv c b) ⟨$⟩ x)
  split-iv a c b x ac cb with lem (Ge c x) | lem (Ge b x) | lem (Ge a x)
  ... | inj₁ cx | inj₁ bx | _ = trans (χIv-out a b x (λ (_ , n) → n bx))
      (sym (trans (+-cong (χIv-out a c x (λ (_ , n) → n cx)) (χIv-out c b x (λ (_ , n) → n bx))) (+-identityˡ 0#)))
  ... | inj₁ cx | inj₂ nb | _ = trans (χIv-in a b x ((λ q m → cx q (ac q m)) , nb))
      (sym (trans (+-cong (χIv-out a c x (λ (_ , n) → n cx)) (χIv-in c b x (cx , nb))) (+-identityˡ 1#)))
  ... | inj₂ nc | inj₁ bx | _ = ⊥-elim (nc (λ q m → bx q (cb q m)))
  ... | inj₂ nc | inj₂ nb | inj₁ ax = trans (χIv-in a b x (ax , nb))
      (sym (trans (+-cong (χIv-in a c x (ax , nc)) (χIv-out c b x (λ (g , _) → nc g))) (+-identityʳ 1#)))
  ... | inj₂ nc | inj₂ nb | inj₂ na = trans (χIv-out a b x (λ (g , _) → na g))
      (sym (trans (+-cong (χIv-out a c x (λ (g , _) → na g)) (χIv-out c b x (λ (g , _) → nc g))) (+-identityˡ 0#)))

  dbl≡ : ∀ m → dbl m ≡ 2 * m
  dbl≡ m = ≡.trans (dbl-*2 m) (ℕ.*-comm m 2)

  dy-dbl′ : ∀ m n → dy (suc n) (2 * m) ≈ dy n m
  dy-dbl′ m n = ≡.subst (λ k → natE k · hp (suc n) ≈ natE m · hp n) (dbl≡ m) (dy-dbl m n)

  dy-dbl″ : ∀ m n → dy (suc n) (suc (suc (2 * m))) ≈ dy n (suc m)
  dy-dbl″ m n = ≡.subst (λ k → dy (suc n) (suc (suc k)) ≈ dy n (suc m)) (dbl≡ m) (dy-dbl (suc m) n)

  χI-split : ∀ n m x → map (χI n m) ⟨$⟩ x ≈ (map (χI (suc n) (2 * m)) ⟨$⟩ x) + (map (χI (suc n) (suc (2 * m))) ⟨$⟩ x)
  χI-split n m x = trans (split-iv lo c hi x (ap lo≤c) (ap c≤hi))
    (+-cong (χIv-cong x (sym (dy-dbl′ m n)) refl) (χIv-cong x refl (sym (dy-dbl″ m n))))
    where
      lo = dy n m
      c = dy (suc n) (suc (2 * m))
      hi = dy n (suc m)
      lo≤c : lo ≤ c
      lo≤c = ≤-trans (≤-reflexive (sym (dy-dbl′ m n))) (dy-mono (suc n) (ℕ.n≤1+n _))
      c≤hi : c ≤ hi
      c≤hi = ≤-trans (dy-mono (suc n) (ℕ.n≤1+n _)) (≤-reflexive (dy-dbl″ m n))
