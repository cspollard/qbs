{-# OPTIONS --safe --without-K #-}

-- The exponential function on an `OmegaSemiring`: `exp x = ⨆ₙ ∑_{k<n} x^k / k!`, the supremum of the
-- increasing partial sums.  There is no division in general, so the coefficients `1/k!` are built from a
-- family `inv n` of reciprocals `1/(n+1)` given as module parameters (`inv n * (n+1) ≈ 1`; for lower cuts
-- of the rationals these are the rational cuts `qC (1/(n+1))`), as `ι 0 = 1`, `ι (n+1) = inv n * ι n`.
-- This keeps the construction abstract: it works in any `OmegaSemiring` where the natural numbers are
-- invertible, and needs no rational arithmetic here.  (The parameters are plain functions, not a record:
-- records inside parameterised modules were expensive to check in `Inference/Sampler`.)
-- Proved: `exp 0 ≈ 1`, monotonicity, congruence, `1 + x ≤ exp x`, and the addition law
-- `exp (x + y) ≈ exp x * exp y`, from the Cauchy product (`Analysis/Cauchy`) and the binomial identity
-- `∑_{i+j=n} (xⁱ/i!)(yʲ/j!) = (x+y)ⁿ/n!`, proved without the binomial theorem by the recurrence
-- `(n+1) · T(n+1) = (x+y) · T(n)`, cancelled with `inv n`.
module QBS.Analysis.Exp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality.Core as ≡
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Analysis.Omega
open import QBS.Analysis.Series
open import QBS.Analysis.Cauchy

module Exp {ℓ} (A : OmegaSemiring ℓ) where
  open OmegaSemiring A renaming (Carrier to ∣A∣)
  open Series A
  module C = Cauchy A
  open SetoidReasoning setoid
  open import Algebra.Solver.Ring.NaturalCoefficients.Default commutativeSemiring
    using (solve; _:+_; _:*_; _:=_; con)

  -- powers and natural numbers
  pw : ∣A∣ → ℕ → ∣A∣
  pw x zero = 1#
  pw x (suc k) = x * pw x k

  natE : ℕ → ∣A∣
  natE zero = 0#
  natE (suc n) = natE n + 1#

  pw-mono : ∀ {x y} k → x ≤ y → pw x k ≤ pw y k
  pw-mono zero h = ≤-refl
  pw-mono {x} {y} (suc k) h =
    ≤-trans (*-mono x (pw-mono k h))
      (≤-trans (≤-reflexive (*-comm x (pw y k)))
        (≤-trans (*-mono (pw y k) h) (≤-reflexive (*-comm (pw y k) y))))

  -- the algebra of one step: if `I * N = 1` then `N · (I L)(X P) = X (L P)`
  step : ∀ N I L X P → I * N ≈ 1# → N * ((I * L) * (X * P)) ≈ X * (L * P)
  step N I L X P e = begin
    N * ((I * L) * (X * P))   ≈⟨ solve 5 (λ N I L X P → N :* ((I :* L) :* (X :* P)) := (I :* N) :* (X :* (L :* P))) refl N I L X P ⟩
    (I * N) * (X * (L * P))   ≈⟨ *-cong e refl ⟩
    1# * (X * (L * P))        ≈⟨ *-identityˡ _ ⟩
    X * (L * P) ∎

  -- weights: natE (a+1) + natE (b+2) = natE (a+2) + natE (b+1)
  wt-shift : ∀ a b → natE (suc a) + natE (suc (suc b)) ≈ natE (suc (suc a)) + natE (suc b)
  wt-shift a b = solve 3 (λ a b o → (a :+ o) :+ ((b :+ o) :+ o) := ((a :+ o) :+ o) :+ (b :+ o)) refl (natE a) (natE b) 1#

  wt-one : ∀ b → natE 1 + natE (suc b) ≈ natE (suc (suc b))
  wt-one b = trans (+-cong (+-identityˡ 1#) refl) (+-comm 1# (natE (suc b)))

  wt-two : ∀ a → natE (suc (suc a)) ≈ natE (suc a) + natE 1
  wt-two a = sym (+-cong refl (+-identityˡ 1#))

  module WithInv (inv : ℕ → ∣A∣) (inv-ok : ∀ n → inv n * natE (suc n) ≈ 1#) where

    -- 1/n!
    ι : ℕ → ∣A∣
    ι zero = 1#
    ι (suc n) = inv n * ι n

    -- the n-th term xⁿ / n!
    term : ∣A∣ → ℕ → ∣A∣
    term x n = ι n * pw x n

    exp : ∣A∣ → ∣A∣
    exp x = ∑ᶠ (term x)

    inv0 : inv 0 ≈ 1#
    inv0 = trans (sym (*-identityʳ _)) (trans (*-cong refl (sym (+-identityˡ 1#))) (inv-ok 0))

    term-mono : ∀ {x y} → x ≤ y → ∀ n → term x n ≤ term y n
    term-mono {x} {y} h n = *-mono (ι n) (pw-mono n h)

    exp-mono : ∀ {x y} → x ≤ y → exp x ≤ exp y
    exp-mono h = ∑ᶠ-mono (term-mono h)

    exp-cong : ∀ {x y} → x ≈ y → exp x ≈ exp y
    exp-cong e = ≤-antisym (exp-mono (≤-reflexive e)) (exp-mono (≤-reflexive (sym e)))

    exp-zero : exp 0# ≈ 1#
    exp-zero = trans (∑ᶠ-single 0 other) (*-identityˡ 1#)
      where
        other : ∀ n → (n ≡.≡ 0 → ⊥) → term 0# n ≈ 0#
        other zero n≢0 = ⊥-elim (n≢0 ≡.refl)
        other (suc k) _ = trans (*-cong refl (zeroˡ _)) (zeroʳ _)

    1+≤exp : ∀ x → 1# + x ≤ exp x
    1+≤exp x = ≤-trans (≤-reflexive (sym (+-cong (trans (+-identityˡ _) (*-identityˡ 1#)) e1))) (psum≤∑ᶠ (term x) 2)
      where
        e1 : term x 1 ≈ x
        e1 = trans (*-cong (trans (*-identityʳ _) inv0) (*-identityʳ x)) (*-identityˡ x)

    module Add (x y : ∣A∣) where
      module P = C.Product (term x) (term y)
      g : ℕ → ℕ → ∣A∣
      g = P.g
      D : ℕ → ℕ → ∣A∣
      D = C.diag g

      tx : ∀ z k → natE (suc k) * term z (suc k) ≈ z * term z k
      tx z k = step _ _ _ _ _ (inv-ok k)

      g-x : ∀ n m → natE (suc n) * g (suc n) m ≈ x * g n m
      g-x n m = trans (sym (*-assoc _ _ _)) (trans (*-cong (tx x n) refl) (*-assoc _ _ _))

      g-y : ∀ n m → natE (suc m) * g n (suc m) ≈ y * g n m
      g-y n m = begin
        natE (suc m) * (term x n * term y (suc m))
          ≈⟨ solve 3 (λ N T U → N :* (T :* U) := T :* (N :* U)) refl (natE (suc m)) (term x n) (term y (suc m)) ⟩
        term x n * (natE (suc m) * term y (suc m))
          ≈⟨ *-cong refl (tx y m) ⟩
        term x n * (y * term y m)
          ≈⟨ solve 3 (λ T Y U → T :* (Y :* U) := Y :* (T :* U)) refl (term x n) y (term y m) ⟩
        y * (term x n * term y m) ∎

      -- the weighted recurrence off the boundary
      head : ∀ n m → (natE (suc n) + natE (suc m)) * g (suc n) (suc m) ≈ x * g n (suc m) + y * g (suc n) m
      head n m = trans (distribʳ _ _ _) (+-cong (g-x n (suc m)) (g-y (suc n) m))

      P-zero : ∀ m → (natE 1 + natE (suc m)) * D 1 (suc m) ≈ x * D 0 (suc m) + y * D 1 m
      P-zero m = trans (distribˡ _ _ _) (trans (+-cong (head 0 m) tailZ) final)
        where
          tailZ : (natE 1 + natE (suc m)) * g 0 (suc (suc m)) ≈ y * g 0 (suc m)
          tailZ = trans (*-cong (wt-one m) refl) (g-y 0 (suc m))
          final : (x * g 0 (suc m) + y * g 1 m) + y * g 0 (suc m) ≈ x * g 0 (suc m) + y * (g 1 m + g 0 (suc m))
          final = solve 5 (λ x y A B C → (x :* A :+ y :* B) :+ y :* C := x :* A :+ y :* (B :+ C))
                    refl x y (g 0 (suc m)) (g 1 m) (g 0 (suc m))

      P-step : ∀ n m → (natE (suc (suc n)) + natE (suc m)) * D (suc n) (suc (suc m)) ≈
                       x * D n (suc (suc m)) + y * D (suc n) (suc m) →
               (natE (suc (suc n)) + natE (suc m)) * D (suc (suc n)) (suc m) ≈
                 x * D (suc n) (suc m) + y * D (suc (suc n)) m
      P-step n m ih = trans (distribˡ _ _ _) (trans (+-cong (head (suc n) m) ih) final)
        where
          final : (x * g (suc n) (suc m) + y * g (suc (suc n)) m) + (x * D n (suc (suc m)) + y * D (suc n) (suc m)) ≈
                  x * D (suc n) (suc m) + y * D (suc (suc n)) m
          final = solve 5 (λ x y Gx Gy R → (x :* Gx :+ y :* Gy) :+ (x :* R :+ y :* (Gx :+ R)) := x :* (Gx :+ R) :+ y :* (Gy :+ (Gx :+ R)))
                    refl x y (g (suc n) (suc m)) (g (suc (suc n)) m) (D n (suc (suc m)))

      P : ∀ n m → (natE (suc n) + natE (suc m)) * D (suc n) (suc m) ≈ x * D n (suc m) + y * D (suc n) m
      P zero m = P-zero m
      P (suc n) m = P-step n m (trans (*-cong (sym (wt-shift n m)) refl) (P n (suc m)))

      -- the recurrence on the boundary column
      Z : ∀ n → natE (suc n) * D (suc n) 0 ≈ (x + y) * D n 0
      Z zero = trans (distribˡ _ _ _) (trans (+-cong (g-x 0 0) (g-y 0 0)) (sym (distribʳ _ _ _)))
      Z (suc n) = trans (distribˡ _ _ _) (trans (+-cong (g-x (suc n) 0) tailB) final)
        where
          tailB : natE (suc (suc n)) * D (suc n) 1 ≈ x * D n 1 + y * D (suc n) 0
          tailB = trans (*-cong (wt-two n) refl) (P n 0)
          final : x * g (suc n) 0 + (x * D n 1 + y * D (suc n) 0) ≈ (x + y) * D (suc n) 0
          final = solve 4 (λ x y G R → x :* G :+ (x :* R :+ y :* (G :+ R)) := (x :+ y) :* (G :+ R))
                    refl x y (g (suc n) 0) (D n 1)

      binomial : ∀ n → D n 0 ≈ term (x + y) n
      binomial zero = trans (*-cong (*-identityˡ 1#) (*-identityˡ 1#)) (trans (*-identityˡ 1#) (sym (*-identityˡ 1#)))
      binomial (suc n) = begin
        D (suc n) 0
          ≈⟨ sym (trans (*-cong (inv-ok n) refl) (*-identityˡ _)) ⟩
        (inv n * natE (suc n)) * D (suc n) 0
          ≈⟨ *-assoc _ _ _ ⟩
        inv n * (natE (suc n) * D (suc n) 0)
          ≈⟨ *-cong refl (Z n) ⟩
        inv n * ((x + y) * D n 0)
          ≈⟨ *-cong refl (*-cong refl (binomial n)) ⟩
        inv n * ((x + y) * (ι n * pw (x + y) n))
          ≈⟨ solve 4 (λ I S L Q → I :* (S :* (L :* Q)) := (I :* L) :* (S :* Q)) refl (inv n) (x + y) (ι n) (pw (x + y) n) ⟩
        term (x + y) (suc n) ∎

      exp-add : exp (x + y) ≈ exp x * exp y
      exp-add = sym (trans (P.cauchy) (∑ᶠ-cong binomial))

