{-# OPTIONS --safe --without-K #-}

-- Ring identities for the unbiased estimators of signed tests (used by `SgSampleAlg`, `SgSample`).
--   * `SRing`, over an abstract commutative ring (instantiated at the signed values): the arithmetic of the induction
--     steps for E Sₙ = n μ, E Sₙ² = n σ² + n² μ², Var Sₙ = n σ² and E (n Qₙ − Sₙ²) = (n² − n) σ² (`plus1`, `zero-S`,
--     `var-step`, `var-final`, `ss-final`), as in `Analysis/Estimator`;
--   * `DRing`, over an abstract commutative semiring: the identities on parts behind h (g + s) ≐ h g + h s and h · 0 ≐ 0
--     (`dist-cross`, `dist-sums`, `zero-cross`, `zero-sums`).
-- Route: one `solve` of the natural-coefficient ring solver each, over an abstract ring so the solver normalises small
-- terms; the identities involving negation use `-‿inverseˡ` and cancellation by hand.
module QBS.Continuous.SgSampleRing where

open import Algebra using (CommutativeRing; CommutativeSemiring)
open import Data.Product.Base using (_,_)
import Algebra.Properties.Ring
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver
open import QBS.Continuous.SignedVarRing using (module Ring)

module SRing {c ℓ} (S : CommutativeRing c ℓ) where
  module S = CommutativeRing S
  module SP = Algebra.Properties.Ring S.ring
  module SolveS = Solver S.commutativeSemiring

  -- y + a y = (1 + a) y
  plus1 : ∀ a y → y S.+ a S.* y S.≈ (S.1# S.+ a) S.* y
  plus1 = SolveS.solve 2 (λ a y → y :+ a :* y := (con 1 :+ a) :* y) S.refl
    where open SolveS using (_:+_; _:*_; _:=_; con)

  zero-S : ∀ q y → S.0# S.≈ S.0# S.* q S.+ S.0# S.* S.0# S.* y
  zero-S = SolveS.solve 2 (λ q y → con 0 := con 0 :* q :+ con 0 :* con 0 :* y) S.refl
    where open SolveS using (_:+_; _:*_; _:=_; con)

  -- ((σ² + m) + a m) + (a m + (a σ² + a² m)) = (1 + a) σ² + (1 + a)² m
  var-step : ∀ a q m → ((q S.+ m) S.+ a S.* m) S.+ (a S.* m S.+ (a S.* q S.+ a S.* a S.* m)) S.≈
                       (S.1# S.+ a) S.* q S.+ (S.1# S.+ a) S.* (S.1# S.+ a) S.* m
  var-step = SolveS.solve 3 (λ a q m → ((q :+ m) :+ a :* m) :+ (a :* m :+ (a :* q :+ a :* a :* m)) :=
    (con 1 :+ a) :* q :+ (con 1 :+ a) :* (con 1 :+ a) :* m) S.refl
    where open SolveS using (_:+_; _:*_; _:=_; con)

  -- (x + y) − y = x
  cancel : ∀ x y → (x S.+ y) S.+ S.- y S.≈ x
  cancel x y = S.trans (S.+-assoc x y (S.- y)) (S.trans (S.+-cong S.refl (S.-‿inverseʳ y)) (S.+-identityʳ x))

  sq-S : ∀ a y → (a S.* y) S.* (a S.* y) S.≈ a S.* a S.* (y S.* y)
  sq-S = SolveS.solve 2 (λ a y → (a :* y) :* (a :* y) := a :* a :* (y :* y)) S.refl
    where open SolveS using (_:+_; _:*_; _:=_; con)

  -- (a σ² + a² m) − (a μ)² = a σ² when m = μ²
  var-final : ∀ a q μ → (a S.* q S.+ a S.* a S.* (μ S.* μ)) S.+ S.- ((a S.* μ) S.* (a S.* μ)) S.≈ a S.* q
  var-final a q μ = S.trans (S.+-cong S.refl (S.-‿cong (sq-S a μ))) (cancel _ _)

  -- a (a (q + m)) = (a² q − a q) + (a q + a² m)
  split-sq : ∀ a q m → a S.* (a S.* (q S.+ m)) S.≈ (a S.* a S.* q S.+ S.- (a S.* q)) S.+ (a S.* q S.+ a S.* a S.* m)
  split-sq a q m = S.trans (SolveS.solve 3 expand S.refl a q m)
    (S.sym (S.trans (S.+-assoc _ _ _) (S.trans (S.+-cong S.refl (S.sym (S.+-assoc _ _ _)))
      (S.trans (S.+-cong S.refl (S.+-cong (S.-‿inverseˡ (a S.* q)) S.refl)) (S.+-cong S.refl (S.+-identityˡ _))))))
    where open SolveS using (_:+_; _:*_; _:=_)
          expand = λ a q m → a :* (a :* (q :+ m)) := (a :* a :* q :+ a :* a :* m)

  -- a (a (q + m)) − (a q + a² m) = (a² − a) q
  ss-final : ∀ a q m → a S.* (a S.* (q S.+ m)) S.+ S.- (a S.* q S.+ a S.* a S.* m) S.≈ (a S.* a S.+ S.- a) S.* q
  ss-final a q m = S.trans (S.+-cong (split-sq a q m) S.refl) (S.trans (cancel _ _)
    (S.trans (S.+-cong S.refl (SP.-‿distribˡ-* a q)) (S.sym (S.distribʳ q (a S.* a) (S.- a)))))

module DRing {c ℓ} (R : CommutativeSemiring c ℓ) where
  open CommutativeSemiring R using (refl; 0#)
  open Ring R using (Pr; _⊕_; _⊗_; cross; sums; Pa; _⊕ᵃ_; _⊗ᵃ_; crossᵃ; sumsᵃ)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default R

  -- h (g + s) and h g + h s
  DL DR : ∀ {n} → Pr n → Pr n → Pr n → Pr n
  DL h g s = h ⊗ (g ⊕ s)
  DR h g s = (h ⊗ g) ⊕ (h ⊗ s)

  DLᵃ DRᵃ : Pa → Pa → Pa → Pa
  DLᵃ h g s = h ⊗ᵃ (g ⊕ᵃ s)
  DRᵃ h g s = (h ⊗ᵃ g) ⊕ᵃ (h ⊗ᵃ s)

  dist-cross : ∀ a b c d e f → crossᵃ (DLᵃ (a , b) (c , d) (e , f)) (DRᵃ (a , b) (c , d) (e , f))
  dist-cross a b c d e f = solve 6
    (λ a b c d e f → cross (DL (a , b) (c , d) (e , f)) (DR (a , b) (c , d) (e , f))) refl a b c d e f

  dist-sums : ∀ a b c d e f → sumsᵃ (DLᵃ (a , b) (c , d) (e , f)) (DRᵃ (a , b) (c , d) (e , f))
  dist-sums a b c d e f = solve 6
    (λ a b c d e f → sums (DL (a , b) (c , d) (e , f)) (DR (a , b) (c , d) (e , f))) refl a b c d e f

  -- h · 0 and 0
  zero-cross : ∀ a b → crossᵃ ((a , b) ⊗ᵃ (0# , 0#)) (0# , 0#)
  zero-cross a b = solve 2 (λ a b → cross ((a , b) ⊗ (con 0 , con 0)) (con 0 , con 0)) refl a b

  zero-sums : ∀ a b → sumsᵃ ((a , b) ⊗ᵃ (0# , 0#)) (0# , 0#)
  zero-sums a b = solve 2 (λ a b → sums ((a , b) ⊗ (con 0 , con 0)) (con 0 , con 0)) refl a b
