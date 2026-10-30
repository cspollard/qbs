{-# OPTIONS --safe --without-K #-}

-- The generic estimator theorem, over an abstract ring of random variables.
--
-- `R` is a commutative ring of (bounded, signed) random variables and `E : R → S` an additive expectation into a
-- commutative ring `S` of values.  For `X₀, X₁, …` with `E Xᵢ = μ`, `E Xᵢ² = σ² + μ²` and `E XᵢXⱼ = μ²` (i < j), and
-- `Sₙ = X₀ + … + X_{n−1}`, `Qₙ = X₀² + … + X_{n−1}²`:
--   E Sₙ = n μ                        (the sample mean is unbiased)
--   E Sₙ² = n σ² + n² μ²              (so Var Sₙ = n σ², i.e. Var x̄ = σ²/n)
--   E (n Qₙ − Sₙ²) = n (n − 1) σ²     (n Qₙ − Sₙ² = n² · (the biased sample variance), so the sample variance
--                                      s² = (n Qₙ − Sₙ²) / (n (n − 1)) is unbiased)
-- Divisions are avoided: the values have no inverses of naturals in general.  Nothing here depends on the model;
-- `Analysis/BoundedRing` instantiates `R` with bounded signed functions on a probability space.
module QBS.Analysis.Estimator where

open import Level using (Level; _⊔_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≤; ≤-refl)
open import Data.Product.Base using (_,_)
import Algebra.Properties.Ring
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Estimator {c ℓ c′ ℓ′} (S : CommutativeRing c ℓ) (R : CommutativeRing c′ ℓ′)
  (E : CommutativeRing.Carrier R → CommutativeRing.Carrier S)
  (E-cong : ∀ {x y} → CommutativeRing._≈_ R x y → CommutativeRing._≈_ S (E x) (E y))
  (E-+ : ∀ x y → CommutativeRing._≈_ S (E (CommutativeRing._+_ R x y)) (CommutativeRing._+_ S (E x) (E y)))
  where

  module S = CommutativeRing S
  module R = CommutativeRing R
  module SP = Algebra.Properties.Ring S.ring
  open SetoidReasoning S.setoid

  module SolveR = Solver R.commutativeSemiring
  module SolveS = Solver S.commutativeSemiring

  -- the natural numbers in each ring
  natS : ℕ → S.Carrier
  natS zero = S.0#
  natS (suc n) = natS n S.+ S.1#

  natR : ℕ → R.Carrier
  natR zero = R.0#
  natR (suc n) = natR n R.+ R.1#

  -- partial sums of a sequence
  sumR : (ℕ → R.Carrier) → ℕ → R.Carrier
  sumR f zero = R.0#
  sumR f (suc n) = sumR f n R.+ f n

  -- the moment hypotheses
  record Moments (X : ℕ → R.Carrier) (μ σ² : S.Carrier) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
    field
      mean : ∀ i → E (X i) S.≈ μ
      second : ∀ i → E (X i R.* X i) S.≈ σ² S.+ μ S.* μ
      uncorr : ∀ i j → i < j → E (X i R.* X j) S.≈ μ S.* μ

  -- the sum of squares
  sq : (ℕ → R.Carrier) → ℕ → R.Carrier
  sq X i = X i R.* X i

  -- n Qₙ − Sₙ²
  SS : (ℕ → R.Carrier) → ℕ → R.Carrier
  SS X n = natR n R.* sumR (sq X) n R.+ R.- (sumR X n R.* sumR X n)

  -- ring facts used below, stated once over abstract variables
  suc-S : ∀ a y → a S.* y S.+ y S.≈ (a S.+ S.1#) S.* y
  suc-S = SolveS.solve 2 (λ a y → a SolveS.:* y SolveS.:+ y SolveS.:= (a SolveS.:+ SolveS.con 1) SolveS.:* y) S.refl

  suc-R : ∀ a x → (a R.+ R.1#) R.* x R.≈ a R.* x R.+ x
  suc-R = SolveR.solve 2 (λ a x → (a SolveR.:+ SolveR.con 1) SolveR.:* x SolveR.:= a SolveR.:* x SolveR.:+ x) R.refl

  add-R : ∀ s x y → (s R.+ x) R.* y R.≈ s R.* y R.+ x R.* y
  add-R = SolveR.solve 3 (λ s x y → (s SolveR.:+ x) SolveR.:* y SolveR.:= s SolveR.:* y SolveR.:+ x SolveR.:* y) R.refl

  sq-R : ∀ s x → (s R.+ x) R.* (s R.+ x) R.≈ s R.* s R.+ ((s R.* x R.+ s R.* x) R.+ x R.* x)
  sq-R = SolveR.solve 2 (λ s x →
    (s :+ x) :* (s :+ x) := s :* s :+ ((s :* x :+ s :* x) :+ x :* x)) R.refl
    where open SolveR using (_:+_; _:*_; _:=_)

  sq-S : ∀ a y → (a S.* y) S.* (a S.* y) S.≈ a S.* a S.* (y S.* y)
  sq-S = SolveS.solve 2
      (λ a y → (a SolveS.:* y) SolveS.:* (a SolveS.:* y) SolveS.:= a SolveS.:* a SolveS.:* (y SolveS.:* y)) S.refl

  -- (a q + a² m) + ((a m + a m) + (q + m)) = (a + 1) q + (a + 1)² m
  step-S : ∀ a q m → (a S.* q S.+ a S.* a S.* m) S.+ ((a S.* m S.+ a S.* m) S.+ (q S.+ m)) S.≈
                     (a S.+ S.1#) S.* q S.+ (a S.+ S.1#) S.* (a S.+ S.1#) S.* m
  step-S = SolveS.solve 3 (λ a q m →
    (a :* q :+ a :* a :* m) :+ ((a :* m :+ a :* m) :+ (q :+ m)) :=
    (a :+ con 1) :* q :+ (a :+ con 1) :* (a :+ con 1) :* m) S.refl
    where open SolveS using (_:+_; _:*_; _:=_; con)

  zero-S : ∀ q y → S.0# S.≈ S.0# S.* q S.+ S.0# S.* S.0# S.* y
  zero-S = SolveS.solve 2
      (λ q y → SolveS.con 0 SolveS.:= SolveS.con 0 SolveS.:* q SolveS.:+ SolveS.con 0 SolveS.:* SolveS.con 0 SolveS.:* y) S.refl

  module _ {X : ℕ → R.Carrier} {μ σ² : S.Carrier} (M : Moments X μ σ²) where
    open Moments M

    private
      m = μ S.* μ

    -- E of zero, of negations, and of n-fold multiples
    E-0 : E R.0# S.≈ S.0#
    E-0 = S.trans (S.sym (S.+-identityˡ _)) (S.trans (S.+-cong (S.sym (S.-‿inverseˡ x)) S.refl)
      (S.trans (S.+-assoc _ x x) (S.trans (S.+-cong S.refl (S.sym h)) (S.-‿inverseˡ x))))
      where
        x = E R.0#
        h : x S.≈ x S.+ x
        h = S.trans (E-cong (R.sym (R.+-identityˡ R.0#))) (E-+ R.0# R.0#)

    E-neg : ∀ x → E (R.- x) S.≈ S.- (E x)
    E-neg x = S.trans (S.sym (S.+-identityˡ _)) (S.trans (S.+-cong (S.sym (S.-‿inverseˡ (E x))) S.refl)
      (S.trans (S.+-assoc _ _ _) (S.trans (S.+-cong S.refl h) (S.+-identityʳ _))))
      where
        h : E x S.+ E (R.- x) S.≈ S.0#
        h = S.trans (S.sym (E-+ x (R.- x))) (S.trans (E-cong (R.-‿inverseʳ x)) E-0)

    E-natR : ∀ n x → E (natR n R.* x) S.≈ natS n S.* E x
    E-natR zero x = S.trans (E-cong (R.zeroˡ x)) (S.trans E-0 (S.sym (S.zeroˡ _)))
    E-natR (suc n) x = S.trans (E-cong (suc-R (natR n) x))
      (S.trans (E-+ (natR n R.* x) x)
        (S.trans (S.+-cong (E-natR n x) S.refl)
          (suc-S (natS n) (E x))))

    -- E Sₙ = n μ
    E-sum : ∀ n → E (sumR X n) S.≈ natS n S.* μ
    E-sum zero = S.trans E-0 (S.sym (S.zeroˡ _))
    E-sum (suc n) = S.trans (E-+ (sumR X n) (X n))
      (S.trans (S.+-cong (E-sum n) (mean n))
        (suc-S (natS n) μ))

    -- E (Sₖ · Xₙ) = k μ² for k ≤ n
    E-cross : ∀ n k → k ≤ n → E (sumR X k R.* X n) S.≈ natS k S.* m
    E-cross n zero _ = S.trans (E-cong (R.zeroˡ (X n))) (S.trans E-0 (S.sym (S.zeroˡ _)))
    E-cross n (suc k) h = S.trans (E-cong (add-R (sumR X k) (X k) (X n)))
      (S.trans (E-+ (sumR X k R.* X n) (X k R.* X n))
        (S.trans (S.+-cong (E-cross n k (<⇒≤ h)) (uncorr k n h))
          (suc-S (natS k) m)))

    -- E (2 Sₙ Xₙ + Xₙ²) = 2 n μ² + (σ² + μ²)
    E-mid : ∀ n → E ((sumR X n R.* X n R.+ sumR X n R.* X n) R.+ X n R.* X n) S.≈ (natS n S.* m S.+ natS n S.* m) S.+ (σ² S.+ m)
    E-mid n = S.trans (E-+ (sumR X n R.* X n R.+ sumR X n R.* X n) (X n R.* X n))
      (S.+-cong (S.trans (E-+ (sumR X n R.* X n) (sumR X n R.* X n))
          (S.+-cong (E-cross n n ≤-refl) (E-cross n n ≤-refl))) (second n))

    -- E Sₙ² = n σ² + n² μ²
    E-sum² : ∀ n → E (sumR X n R.* sumR X n) S.≈ natS n S.* σ² S.+ natS n S.* natS n S.* m
    E-sum² zero = S.trans (E-cong (R.zeroˡ R.0#)) (S.trans E-0 (zero-S σ² m))
    E-sum² (suc n) = S.trans (E-cong (sq-R (sumR X n) (X n)))
      (S.trans (E-+ (sumR X n R.* sumR X n) ((sumR X n R.* X n R.+ sumR X n R.* X n) R.+ X n R.* X n))
        (S.trans (S.+-cong (E-sum² n) (E-mid n)) (step-S (natS n) σ² m)))

    -- E Qₙ = n (σ² + μ²)
    E-sumsq : ∀ n → E (sumR (sq X) n) S.≈ natS n S.* (σ² S.+ m)
    E-sumsq zero = S.trans E-0 (S.sym (S.zeroˡ _))
    E-sumsq (suc n) = S.trans (E-+ (sumR (sq X) n) (sq X n))
      (S.trans (S.+-cong (E-sumsq n) (second n))
        (suc-S (natS n) (σ² S.+ m)))

    -- (x + y) − y = x
    cancel : ∀ x y → (x S.+ y) S.+ S.- y S.≈ x
    cancel x y = S.trans (S.+-assoc x y (S.- y)) (S.trans (S.+-cong S.refl (S.-‿inverseʳ y)) (S.+-identityʳ x))

    -- a (a (q + m)) = (a² q − a q) + (a q + a² m)
    split-sq : ∀ a q m → a S.* (a S.* (q S.+ m)) S.≈ (a S.* a S.* q S.+ S.- (a S.* q)) S.+ (a S.* q S.+ a S.* a S.* m)
    split-sq a q m = S.trans
      (SolveS.solve 3 expand S.refl a q m)
      (S.sym (S.trans (S.+-assoc _ _ _) (S.trans (S.+-cong S.refl (S.sym (S.+-assoc _ _ _)))
        (S.trans (S.+-cong S.refl (S.+-cong (S.-‿inverseˡ (a S.* q)) S.refl)) (S.+-cong S.refl (S.+-identityˡ _))))))
      where
        open SolveS using (_:+_; _:*_; _:=_)
        expand = λ a q m → a :* (a :* (q :+ m)) := (a :* a :* q :+ a :* a :* m)

    -- Var Sₙ = E Sₙ² − (E Sₙ)² = n σ²
    var-sum : ∀ n → E (sumR X n R.* sumR X n) S.+ S.- (E (sumR X n) S.* E (sumR X n)) S.≈ natS n S.* σ²
    var-sum n = begin
      E (sumR X n R.* sumR X n) S.+ S.- (E (sumR X n) S.* E (sumR X n))
        ≈⟨ S.+-cong (E-sum² n) (S.-‿cong (S.*-cong (E-sum n) (E-sum n))) ⟩
      (natS n S.* σ² S.+ natS n S.* natS n S.* m) S.+ S.- ((natS n S.* μ) S.* (natS n S.* μ))
        ≈⟨ S.+-cong S.refl (S.-‿cong (sq-S (natS n) μ)) ⟩
      (natS n S.* σ² S.+ natS n S.* natS n S.* m) S.+ S.- (natS n S.* natS n S.* m)
        ≈⟨ cancel _ _ ⟩
      natS n S.* σ² ∎

    -- E (n Qₙ − Sₙ²) = (n² − n) σ²
    E-SS : ∀ n → E (SS X n) S.≈ (natS n S.* natS n S.+ S.- (natS n)) S.* σ²
    E-SS n = begin
      E (SS X n)
        ≈⟨ E-+ (natR n R.* sumR (sq X) n) (R.- (sumR X n R.* sumR X n)) ⟩
      E (natR n R.* sumR (sq X) n) S.+ E (R.- (sumR X n R.* sumR X n))
        ≈⟨ S.+-cong (S.trans (E-natR n _) (S.*-cong S.refl (E-sumsq n))) (S.trans (E-neg _) (S.-‿cong (E-sum² n))) ⟩
      natS n S.* (natS n S.* (σ² S.+ m)) S.+ S.- (natS n S.* σ² S.+ natS n S.* natS n S.* m)
        ≈⟨ S.+-cong (split-sq (natS n) σ² m) S.refl ⟩
      ((natS n S.* natS n S.* σ² S.+ u) S.+ T) S.+ S.- T
        ≈⟨ cancel _ _ ⟩
      natS n S.* natS n S.* σ² S.+ u
        ≈⟨ S.+-cong S.refl (SP.-‿distribˡ-* (natS n) σ²) ⟩
      natS n S.* natS n S.* σ² S.+ (S.- (natS n)) S.* σ²
        ≈⟨ S.sym (S.distribʳ σ² (natS n S.* natS n) (S.- (natS n))) ⟩
      (natS n S.* natS n S.+ S.- (natS n)) S.* σ² ∎
      where
        u = S.- (natS n S.* σ²)
        T = natS n S.* σ² S.+ natS n S.* natS n S.* m

  -- Affine images Yᵢ = a + c·Xᵢ, for a constant embedding κ with E (κ s) = s and E (κ s · x) = s · E x:
  -- the moments become μ′ = a + c μ and σ′² = c² σ².
  module Affine (κ : S.Carrier → R.Carrier)
    (E-κ : ∀ s → E (κ s) S.≈ s) (E-κ* : ∀ s x → E (κ s R.* x) S.≈ s S.* E x) where

    affine : (ℕ → R.Carrier) → S.Carrier → S.Carrier → ℕ → R.Carrier
    affine X a c i = κ a R.+ κ c R.* X i

    -- (a + c Xᵢ)(a + c Xⱼ) = a a + (a (c Xⱼ) + a (c Xᵢ)) + c (c (Xᵢ Xⱼ))
    prod-R : ∀ ka kc x y → (ka R.+ kc R.* x) R.* (ka R.+ kc R.* y) R.≈
             ka R.* ka R.+ (ka R.* (kc R.* y) R.+ ka R.* (kc R.* x)) R.+ kc R.* (kc R.* (x R.* y))
    prod-R = SolveR.solve 4 (λ ka kc x y →
      (ka :+ kc :* x) :* (ka :+ kc :* y) :=
      ka :* ka :+ (ka :* (kc :* y) :+ ka :* (kc :* x)) :+ kc :* (kc :* (x :* y))) R.refl
      where open SolveR using (_:+_; _:*_; _:=_)

    -- E of that, in terms of E x, E y, E (x y)
    E-prod : ∀ a c x y → E ((κ a R.+ κ c R.* x) R.* (κ a R.+ κ c R.* y)) S.≈
             a S.* a S.+ (a S.* (c S.* E y) S.+ a S.* (c S.* E x)) S.+ c S.* (c S.* E (x R.* y))
    E-prod a c x y = begin
      E ((κ a R.+ κ c R.* x) R.* (κ a R.+ κ c R.* y))
        ≈⟨ E-cong (prod-R (κ a) (κ c) x y) ⟩
      E (κ a R.* κ a R.+ (κ a R.* (κ c R.* y) R.+ κ a R.* (κ c R.* x)) R.+ κ c R.* (κ c R.* (x R.* y)))
        ≈⟨ E-+ _ _ ⟩
      E (κ a R.* κ a R.+ (κ a R.* (κ c R.* y) R.+ κ a R.* (κ c R.* x))) S.+ E (κ c R.* (κ c R.* (x R.* y)))
        ≈⟨ S.+-cong (E-+ _ _) (S.trans (E-κ* c _) (S.*-cong S.refl (E-κ* c _))) ⟩
      (E (κ a R.* κ a) S.+ E (κ a R.* (κ c R.* y) R.+ κ a R.* (κ c R.* x))) S.+ c S.* (c S.* E (x R.* y))
        ≈⟨ S.+-cong (S.+-cong (S.trans (E-κ* a _) (S.*-cong S.refl (E-κ a)))
                      (S.trans (E-+ _ _) (S.+-cong (S.trans (E-κ* a _) (S.*-cong S.refl (E-κ* c y)))
                                                   (S.trans (E-κ* a _) (S.*-cong S.refl (E-κ* c x)))))) S.refl ⟩
      a S.* a S.+ (a S.* (c S.* E y) S.+ a S.* (c S.* E x)) S.+ c S.* (c S.* E (x R.* y)) ∎

    E-affine : ∀ a c x → E (κ a R.+ κ c R.* x) S.≈ a S.+ c S.* E x
    E-affine a c x = S.trans (E-+ _ _) (S.+-cong (E-κ a) (E-κ* c x))

    arith-second : ∀ a c μ q → a S.* a S.+ (a S.* (c S.* μ) S.+ a S.* (c S.* μ)) S.+ c S.* (c S.* (q S.+ μ S.* μ)) S.≈
                   c S.* c S.* q S.+ (a S.+ c S.* μ) S.* (a S.+ c S.* μ)
    arith-second = SolveS.solve 4 (λ a c μ q →
      a :* a :+ (a :* (c :* μ) :+ a :* (c :* μ)) :+ c :* (c :* (q :+ μ :* μ)) :=
      c :* c :* q :+ (a :+ c :* μ) :* (a :+ c :* μ)) S.refl
      where open SolveS using (_:+_; _:*_; _:=_)

    arith-cross : ∀ a c μ → a S.* a S.+ (a S.* (c S.* μ) S.+ a S.* (c S.* μ)) S.+ c S.* (c S.* (μ S.* μ)) S.≈
                  (a S.+ c S.* μ) S.* (a S.+ c S.* μ)
    arith-cross = SolveS.solve 3 (λ a c μ →
      a :* a :+ (a :* (c :* μ) :+ a :* (c :* μ)) :+ c :* (c :* (μ :* μ)) :=
      (a :+ c :* μ) :* (a :+ c :* μ)) S.refl
      where open SolveS using (_:+_; _:*_; _:=_)

    affine-moments : ∀ {X μ σ²} → Moments X μ σ² → ∀ a c → Moments (affine X a c) (a S.+ c S.* μ) (c S.* c S.* σ²)
    affine-moments {X} {μ} {σ²} M a c = record
      { mean = λ i → S.trans (E-affine a c (X i)) (S.+-cong S.refl (S.*-cong S.refl (mean i)))
      ; second = λ i → S.trans (E-prod a c (X i) (X i))
          (S.trans (S.+-cong (S.+-cong S.refl (S.+-cong (S.*-cong S.refl (S.*-cong S.refl (mean i)))
                                                         (S.*-cong S.refl (S.*-cong S.refl (mean i)))))
                             (S.*-cong S.refl (S.*-cong S.refl (second i))))
                   (arith-second a c μ σ²))
      ; uncorr = λ i j h → S.trans (E-prod a c (X i) (X j))
          (S.trans (S.+-cong (S.+-cong S.refl (S.+-cong (S.*-cong S.refl (S.*-cong S.refl (mean j)))
                                                         (S.*-cong S.refl (S.*-cong S.refl (mean i)))))
                             (S.*-cong S.refl (S.*-cong S.refl (uncorr i j h))))
                   (arith-cross a c μ)) }
      where open Moments M
