{-# OPTIONS --safe --without-K #-}

-- The tail `xᵉ e^{−x} → 0` at the integers, along the multiples of ι = e + 1 (a frequent, not eventual, tail).
--
-- Over an abstract Archimedean ω-semiring A with E (the exponential e^{−x}) satisfying E x ≤ 1, E 0 = 1,
-- `E (a + b) = E a · E b` at naturals and `E L · L ≤ 1` (from `1 + L ≤ e^L`), at N = ι L:
--   Nᵉ e^{−N} = ιᵉ Lᵉ (e^{−L})^{ι} = ιᵉ (L e^{−L})ᵉ e^{−L} ≤ ιᵉ e^{−L},
-- and `e^{−L} ≤ ½ᶻ` once L ≥ 2ᶻ (from `e^{−L} L ≤ 1`, unscaling by ½ᶻ).  So for every m and N₀ there is N ≥ N₀ with
-- `Nᵉ e^{−N} ≤ ½ᵐ` (`tail`: take L = N₀ + 2^{K+m} with ιᵉ ≤ 2ᴷ).
module QBS.Analysis.ExpTail where

import Level as L
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)

open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.Exp using (module Exp)
open import QBS.Analysis.TailFTC using (module AlgT)
open import QBS.Analysis.TailFTCLip using (module AlgL)
open import QBS.Analysis.PolyExpCert using (module AlgP)

module AlgTail (A : OmegaSemiring (L.suc L.zero)) (R : Arch A) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Arch R using (half; hp)
  open AlgT A R using (P)
  open AlgL A R using (P*hp)
  open AlgP A R using (pw; pw-mono; pwB; natE≤P; natE-+; natE-*; pnat; natE-pnat; pw-mul; pw-one; Phz; *-mono₂; *-monoʳ)
  open Exp A using (natE)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring

  module Tail (E : ∣A∣ → ∣A∣) (E≤1 : ∀ x → E x ≤ 1#) (E-zero : E 0# ≈ 1#)
    (E-cong : ∀ {x y} → x ≈ y → E x ≈ E y)
    (E-addN : ∀ a b → E (natE a + natE b) ≈ E (natE a) * E (natE b))
    (E-L : ∀ n → E (natE n) * natE n ≤ 1#) where

    pw-cong : ∀ e {x y} → x ≈ y → pw e x ≈ pw e y
    pw-cong e xy = ≤-antisym (pw-mono e (≤-reflexive xy)) (pw-mono e (≤-reflexive (sym xy)))

    -- e^{−kL} = (e^{−L})ᵏ
    y-iter : ∀ L k → E (natE (k ℕ.* L)) ≈ pw k (E (natE L))
    y-iter L zero = E-zero
    y-iter L (suc k) = trans (E-cong (natE-+ L (k ℕ.* L))) (trans (E-addN L (k ℕ.* L)) (*-cong refl (y-iter L k)))

    -- e^{−L} ≤ ½ˢ once 2ˢ ≤ L
    small : ∀ n s → P s ≤ natE n → E (natE n) ≤ hp s
    small n s ps = ≤-trans (≤-reflexive (sym eq)) (≤-trans (*-mono (hp s) h) (≤-reflexive (*-identityʳ (hp s))))
      where
      h : P s * E (natE n) ≤ 1#
      h = ≤-trans (*-monoʳ (E (natE n)) ps) (≤-trans (≤-reflexive (*-comm _ _)) (E-L n))
      eq : hp s * (P s * E (natE n)) ≈ E (natE n)
      eq = trans (sym (*-assoc _ _ _)) (trans (*-cong (trans (*-comm _ _) (P*hp s)) refl) (*-identityˡ _))

    tail : ∀ e m N₀ → Σ ℕ (λ N → N₀ ℕ.≤ N × pw e (natE N) * E (natE N) ≤ hp m)
    tail e m N₀ = N , N₀≤N , bound
      where
      ι : ℕ
      ι = suc e
      K : ℕ
      K = proj₁ (pwB {natE ι} ι (natE≤P ι) e)
      pbd : pw e (natE ι) ≤ P K
      pbd = proj₂ (pwB {natE ι} ι (natE≤P ι) e) ≤-refl
      p Lc N : ℕ
      p = pnat (K ℕ.+ m)
      Lc = N₀ ℕ.+ p
      N = ι ℕ.* Lc
      y : ∣A∣
      y = E (natE Lc)

      N₀≤N : N₀ ℕ.≤ N
      N₀≤N = ℕ.≤-trans (ℕ.m≤m+n N₀ p) (ℕ.m≤m+n Lc (e ℕ.* Lc))

      P≤L : P (K ℕ.+ m) ≤ natE Lc
      P≤L = ≤-trans (≤-reflexive (sym (natE-pnat (K ℕ.+ m)))) (≤-trans ≤-+ʳ
        (≤-trans (≤-reflexive (+-comm (natE p) (natE N₀))) (≤-reflexive (sym (natE-+ N₀ p)))))

      yb : y ≤ hp (K ℕ.+ m)
      yb = small Lc (K ℕ.+ m) P≤L

      Ly : pw e (natE Lc) * pw e y ≤ 1#
      Ly = ≤-trans (≤-reflexive (sym (pw-mul e (natE Lc) y)))
        (≤-trans (pw-mono e (≤-trans (≤-reflexive (*-comm _ _)) (E-L Lc))) (≤-reflexive (pw-one e)))

      bound : pw e (natE N) * E (natE N) ≤ hp m
      bound = ≤-trans (≤-reflexive (trans (*-cong (pw-cong e (natE-* ι Lc)) (y-iter Lc ι))
          (trans (*-cong (pw-mul e (natE ι) (natE Lc)) refl)
            (solve 4 (λ a b c d → (a :* b) :* (d :* c) := (a :* (b :* c)) :* d) refl (pw e (natE ι)) (pw e (natE Lc)) (pw e y) y))))
        (≤-trans (*-mono₂ (≤-trans (*-mono (pw e (natE ι)) Ly) (≤-trans (≤-reflexive (*-identityʳ _)) pbd)) (≤-refl {y}))
          (≤-trans (*-mono₂ (≤-refl {P K}) yb) (≤-reflexive (Phz K m))))
