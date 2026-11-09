{-# OPTIONS --safe --without-K #-}

-- Semiring identities for exponential families, used by `Continuous/ExpFamilyAux` and `Continuous/ExpFamily`, over an
-- abstract commutative semiring.
--   * `scale-+-alg`: p (a + b) + n (a′ + b′) ≈ (p a + n a′) + (p b + n b′), the parts of `scaleT c (f +T g)`;
--   * `scale-0-alg`: p · 0 + n · 0 ≈ 0, `zero-scale-alg`: 0 · a + 0 · b ≈ 0, and `+-0-alg`: 0 ≈ 0 + 0;
--   * `prodF N a = a₀ · (a₁ · (… · 1))` (the recursion of `FinProd.∏ⁿ`), with `prodF-mul` (∏ aᵢ · ∏ bᵢ ≈ ∏ aᵢ bᵢ),
--     `prodF-one` (∏ 1 ≈ 1) and `prodF-cong`.
-- Route: the ring solver of `Algebra.Solver.Ring.NaturalCoefficients.Default`; `prodF-mul` by induction on N with
-- `Algebra.Properties.CommutativeSemigroup.interchange`.
module QBS.Continuous.ExpFamilyAlg where

open import Algebra.Bundles using (CommutativeSemiring)
open import Algebra.Properties.CommutativeSemigroup using (interchange)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (zero; suc)

module ExpFamilyAlg {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (Carrier; _≈_; _+_; _*_; 0#; 1#; refl; trans; *-cong; *-identityˡ;
    *-commutativeSemigroup)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R using (solve; _:+_; _:*_; _:=_; con)

  scale-+-alg : ∀ p n a a′ b b′ → p * (a + b) + n * (a′ + b′) ≈ (p * a + n * a′) + (p * b + n * b′)
  scale-+-alg = solve 6 (λ p n a a′ b b′ →
    p :* (a :+ b) :+ n :* (a′ :+ b′) := (p :* a :+ n :* a′) :+ (p :* b :+ n :* b′)) refl

  scale-0-alg : ∀ p n → p * 0# + n * 0# ≈ 0#
  scale-0-alg = solve 2 (λ p n → p :* con 0 :+ n :* con 0 := con 0) refl

  zero-scale-alg : ∀ a b → 0# * a + 0# * b ≈ 0#
  zero-scale-alg = solve 2 (λ a b → con 0 :* a :+ con 0 :* b := con 0) refl

  +-0-alg : 0# ≈ 0# + 0#
  +-0-alg = solve 0 (con 0 := con 0 :+ con 0) refl

  -- ∏ᵢ aᵢ, by the recursion of `FinProd.∏ⁿ`
  prodF : ∀ N → (Fin N → Carrier) → Carrier
  prodF zero a = 1#
  prodF (suc N) a = a zero * prodF N (λ j → a (suc j))

  prodF-cong : ∀ N {a b : Fin N → Carrier} → (∀ i → a i ≈ b i) → prodF N a ≈ prodF N b
  prodF-cong zero e = refl
  prodF-cong (suc N) e = *-cong (e zero) (prodF-cong N (λ j → e (suc j)))

  prodF-mul : ∀ N (a b : Fin N → Carrier) → prodF N a * prodF N b ≈ prodF N (λ i → a i * b i)
  prodF-mul zero a b = *-identityˡ 1#
  prodF-mul (suc N) a b = trans (interchange *-commutativeSemigroup (a zero) _ (b zero) _)
    (*-cong refl (prodF-mul N (λ j → a (suc j)) (λ j → b (suc j))))

  prodF-one : ∀ N → prodF N (λ _ → 1#) ≈ 1#
  prodF-one zero = refl
  prodF-one (suc N) = trans (*-cong refl (prodF-one N)) (*-identityˡ 1#)
