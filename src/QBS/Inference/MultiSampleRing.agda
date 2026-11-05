{-# OPTIONS --safe --without-K #-}

-- Ring identities for samples of random vectors (plan 05, item 54; helper for `MultiSample`), over an abstract
-- commutative ring (instantiated at the signed values), with the finite sums of `Analysis/SgLinAlg`.
--   * `nt n`, the natural number n in the ring; `Σ-const`: Σᵢ x = n x;
--   * `dbl`: a double sum Σᵢ Σⱼ Eᵢⱼ with Eᵢᵢ = e and Eᵢⱼ = m for i ≢ j is N e + (N² − N) m, for N ≈ n;
--   * `cov-final`: (n e + (n² − n) a b) − (n a)(n b) = n (e − a b), the covariance of the sum;
--   * `ss-final`: n (n e) − (n e + (n² − n) m) = (n² − n)(e − m), the sample cross-product matrix.
-- Route: `row` by induction on the length with the position of the diagonal entry (the other entries are m);
-- `dbl` from `row` and `Σ-const`; the identities with negation use `-‿distribˡ-*`, `-‿distribʳ-*` to move negatives
-- onto single terms, then one solver call and cancellation by hand (as `RandomVectorSumRing`).
module QBS.Inference.MultiSampleRing where

open import Algebra using (CommutativeRing)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality.Core using (_≢_; refl)
import Algebra.Properties.Ring
import Algebra.Properties.AbelianGroup
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)

module MRing {c ℓ} (R : CommutativeRing c ℓ) where
  module R = CommutativeRing R
  open SgLinAlg R using (Σ; Σ-cong)
  module RP = Algebra.Properties.Ring R.ring
  module AG = Algebra.Properties.AbelianGroup R.+-abelianGroup
  module SolveR = Solver R.commutativeSemiring
  open SolveR using (_:+_; _:*_; _:=_; con)

  nt : ℕ → R.Carrier
  nt zero = R.0#
  nt (suc n) = R.1# R.+ nt n

  Σ-const : ∀ n x → Σ n (λ _ → x) R.≈ nt n R.* x
  Σ-const zero x = R.sym (R.zeroˡ x)
  Σ-const (suc n) x = R.trans (R.+-cong R.refl (Σ-const n x))
    (SolveR.solve 2 (λ N x → x :+ N :* x := (con 1 :+ N) :* x) R.refl (nt n) x)

  cancelˡ : ∀ x y → (x R.+ y) R.+ R.- x R.≈ y
  cancelˡ x y = R.trans (R.+-cong (R.+-comm x y) R.refl) (R.trans (R.+-assoc y x (R.- x))
    (R.trans (R.+-cong R.refl (R.-‿inverseʳ x)) (R.+-identityʳ y)))

  -- (1 + N)(1 + N) − (1 + N) = (1 + N) N
  K-eq : ∀ N → ((R.1# R.+ N) R.* (R.1# R.+ N) R.+ R.- (R.1# R.+ N)) R.≈ (R.1# R.+ N) R.* N
  K-eq N = R.trans (R.+-cong (SolveR.solve 1 (λ N → (con 1 :+ N) :* (con 1 :+ N) := (con 1 :+ N) :+ (con 1 :+ N) :* N) R.refl N)
    R.refl) (cancelˡ (R.1# R.+ N) ((R.1# R.+ N) R.* N))

  -- a row with the diagonal entry e at position i and m elsewhere
  row : ∀ n (r : Fin (suc n) → R.Carrier) i e m → r i R.≈ e → (∀ j → i ≢ j → r j R.≈ m) →
    Σ (suc n) r R.≈ e R.+ nt n R.* m
  row n r zero e m d o = R.+-cong d (R.trans (Σ-cong n (λ j → o (suc j) (λ ()))) (Σ-const n m))
  row zero r (suc ()) e m d o
  row (suc n) r (suc i) e m d o = R.trans (R.+-cong (o zero (λ ())) (row n (λ j → r (suc j)) i e m d
    (λ j ne → o (suc j) (λ { refl → ne refl }))))
    (SolveR.solve 3 (λ m e N → m :+ (e :+ N :* m) := e :+ (con 1 :+ N) :* m) R.refl m e (nt n))

  dbl′ : ∀ n (E : Fin n → Fin n → R.Carrier) e m → (∀ i → E i i R.≈ e) → (∀ i j → i ≢ j → E i j R.≈ m) →
    Σ n (λ i → Σ n (E i)) R.≈ nt n R.* e R.+ (nt n R.* nt n R.+ R.- nt n) R.* m
  dbl′ zero E e m d o = R.sym (R.trans (R.+-cong (R.zeroˡ e) (R.trans (R.*-cong (R.trans (R.+-cong (R.zeroˡ R.0#) AG.ε⁻¹≈ε)
    (R.+-identityˡ R.0#)) R.refl) (R.zeroˡ m))) (R.+-identityˡ R.0#))
  dbl′ (suc n) E e m d o = R.trans (Σ-cong (suc n) (λ i → row n (E i) i e m (d i) (o i)))
    (R.trans (Σ-const (suc n) (e R.+ nt n R.* m)) (R.trans
      (SolveR.solve 3 (λ N e m → (con 1 :+ N) :* (e :+ N :* m) := (con 1 :+ N) :* e :+ (con 1 :+ N) :* N :* m) R.refl (nt n) e m)
      (R.+-cong R.refl (R.*-cong (R.sym (K-eq (nt n))) R.refl))))

  -- with n replaced by any N ≈ nt n
  dbl : ∀ n N (E : Fin n → Fin n → R.Carrier) e m → nt n R.≈ N → (∀ i → E i i R.≈ e) →
    (∀ i j → i ≢ j → E i j R.≈ m) → Σ n (λ i → Σ n (E i)) R.≈ N R.* e R.+ (N R.* N R.+ R.- N) R.* m
  dbl n N E e m h d o = R.trans (dbl′ n E e m d o) (R.+-cong (R.*-cong h R.refl)
    (R.*-cong (R.+-cong (R.*-cong h h) (R.-‿cong h)) R.refl))

  cancelT : ∀ A T B → (A R.+ (T R.+ B)) R.+ R.- T R.≈ A R.+ B
  cancelT A T B = R.trans (SolveR.solve 4 (λ A T B nT → (A :+ (T :+ B)) :+ nT := (A :+ B) :+ (T :+ nT)) R.refl A T B (R.- T))
    (R.trans (R.+-cong R.refl (R.-‿inverseʳ T)) (R.+-identityʳ _))

  -- (N e + (N² − N) a b) − (N a)(N b) = N (e − a b)
  cov-final : ∀ N e a b → (N R.* e R.+ (N R.* N R.+ R.- N) R.* (a R.* b)) R.+ R.- ((N R.* a) R.* (N R.* b)) R.≈
    N R.* (e R.+ R.- (a R.* b))
  cov-final N e a b = R.trans (R.+-cong (R.+-cong R.refl (R.trans
      (SolveR.solve 4 (λ N nN a b → (N :* N :+ nN) :* (a :* b) := (N :* N) :* (a :* b) :+ nN :* (a :* b)) R.refl N (R.- N) a b)
      (R.+-cong R.refl (R.trans (R.sym (RP.-‿distribˡ-* N (a R.* b))) (RP.-‿distribʳ-* N (a R.* b))))))
    (R.-‿cong (SolveR.solve 4 (λ N a b c → (N :* a) :* (N :* b) := (N :* N) :* (a :* b)) R.refl N a b N)))
    (R.trans (cancelT (N R.* e) ((N R.* N) R.* (a R.* b)) (N R.* R.- (a R.* b)))
      (SolveR.solve 3 (λ N e q → N :* e :+ N :* q := N :* (e :+ q)) R.refl N e (R.- (a R.* b))))

  -- N (N e) − (N e + (N² − N) m) = (N² − N)(e − m)
  ss-final : ∀ N e m → N R.* (N R.* e) R.+ R.- (N R.* e R.+ (N R.* N R.+ R.- N) R.* m) R.≈
    (N R.* N R.+ R.- N) R.* (e R.+ R.- m)
  ss-final N e m = R.trans (R.+-cong R.refl (R.trans (R.sym (AG.⁻¹-∙-comm (N R.* e) _))
      (R.+-cong (RP.-‿distribˡ-* N e) (RP.-‿distribʳ-* (N R.* N R.+ R.- N) m))))
    (SolveR.solve 4 (λ N nN e nm → N :* (N :* e) :+ (nN :* e :+ (N :* N :+ nN) :* nm) := (N :* N :+ nN) :* (e :+ nm))
      R.refl N (R.- N) e (R.- m))
