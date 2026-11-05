{-# OPTIONS --safe --without-K #-}

-- Ring identities for sums of covariances (plan 05, item 52; helper for `RandomVector`), over an abstract commutative
-- ring (instantiated at the signed values), with the finite sums of `Analysis/SgLinAlg`.
--   * `Σ-neg`, `row`, `rowʳ`: Σⱼ (aⱼ − m xⱼ) = Σ a − m Σ x, and Σᵢ (aᵢ − xᵢ T) = Σ a − (Σ x) T;
--   * `var-sum-ring`: Σᵢ Σⱼ (aᵢⱼ − mᵢ mⱼ) = Σᵢ Σⱼ aᵢⱼ − (Σ m)²;
--   * `cov-ring`: the covariance of two shifted linear forms, (X + (d Aₖ + (c Aₗ + c d))) − (Aₖ + c)(Aₗ + d) with
--     X = Σᵢ Σⱼ (Mₖᵢ Mₗⱼ) aᵢⱼ, equals Σₚ (Σ_q Mₖ_q (a_qp − m_q m_p)) Mₗₚ.
-- Route: induction-free, from `Σ-+`, `Σ-scale`, `Σ-scaleʳ`, `Σ-swap`, `Σ-cong` of `SgLinAlg` and solver calls on
-- single terms; negation is handled by `-‿distribʳ-*` and cancellation by hand.
module QBS.Continuous.RandomVectorSumRing where

open import Algebra using (CommutativeRing)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
import Algebra.Properties.Ring
import Algebra.Properties.AbelianGroup
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver
open import QBS.Analysis.SgLinAlg using (module SgLinAlg)

module RSum {c ℓ} (R : CommutativeRing c ℓ) where
  module R = CommutativeRing R
  open SgLinAlg R using (Σ; Σ-cong; Σ-+; Σ-scale; Σ-scaleʳ; Σ-swap)
  module RP = Algebra.Properties.Ring R.ring
  module AG = Algebra.Properties.AbelianGroup R.+-abelianGroup
  module SolveR = Solver R.commutativeSemiring
  open SolveR using (_:+_; _:*_; _:=_; con)

  Σ-neg : ∀ n (f : Fin n → R.Carrier) → Σ n (λ i → R.- f i) R.≈ R.- Σ n f
  Σ-neg n f = R.trans (Σ-cong n (λ i → R.sym (RP.-1*x≈-x (f i)))) (R.trans (R.sym (Σ-scale n (R.- R.1#) f)) (RP.-1*x≈-x _))

  row : ∀ n (a : Fin n → R.Carrier) m (x : Fin n → R.Carrier) →
    Σ n (λ j → a j R.+ R.- (m R.* x j)) R.≈ Σ n a R.+ R.- (m R.* Σ n x)
  row n a m x = R.trans (Σ-+ n a (λ j → R.- (m R.* x j)))
    (R.+-cong R.refl (R.trans (Σ-neg n (λ j → m R.* x j)) (R.-‿cong (R.sym (Σ-scale n m x)))))

  rowʳ : ∀ n (a : Fin n → R.Carrier) (x : Fin n → R.Carrier) T →
    Σ n (λ i → a i R.+ R.- (x i R.* T)) R.≈ Σ n a R.+ R.- (Σ n x R.* T)
  rowʳ n a x T = R.trans (Σ-+ n a (λ i → R.- (x i R.* T)))
    (R.+-cong R.refl (R.trans (Σ-neg n (λ i → x i R.* T)) (R.-‿cong (R.sym (Σ-scaleʳ n T x)))))

  var-sum-ring : ∀ n (a : Fin n → Fin n → R.Carrier) (m : Fin n → R.Carrier) →
    Σ n (λ i → Σ n (λ j → a i j R.+ R.- (m i R.* m j))) R.≈ Σ n (λ i → Σ n (λ j → a i j)) R.+ R.- (Σ n m R.* Σ n m)
  var-sum-ring n a m = R.trans (Σ-cong n (λ i → row n (a i) (m i) m)) (rowʳ n (λ i → Σ n (a i)) m (Σ n m))

  -- (x (a − u)) y = (x y) a − (x m)(y m′) when u = m m′
  elem : ∀ x y a m m′ → (x R.* (a R.+ R.- (m R.* m′))) R.* y R.≈ (x R.* y) R.* a R.+ R.- ((x R.* m) R.* (y R.* m′))
  elem x y a m m′ = R.trans (SolveR.solve 4 (λ x y a N → (x :* (a :+ N)) :* y := (x :* y) :* a :+ (x :* y) :* N)
      R.refl x y a (R.- (m R.* m′)))
    (R.+-cong R.refl (R.trans (R.sym (RP.-‿distribʳ-* (x R.* y) (m R.* m′))) (R.-‿cong
      (SolveR.solve 4 (λ x y m m′ → (x :* y) :* (m :* m′) := (x :* m) :* (y :* m′)) R.refl x y m m′))))

  -- (X + V) − (U + V) = X − U
  cancelV : ∀ X V U → (X R.+ V) R.+ R.- (U R.+ V) R.≈ X R.+ R.- U
  cancelV X V U = R.trans (R.+-cong R.refl (R.sym (R.trans (R.+-cong R.refl R.refl) (AG.⁻¹-∙-comm U V))))
    (R.trans (SolveR.solve 4 (λ X V nU nV → (X :+ V) :+ (nU :+ nV) := (X :+ nU) :+ (V :+ nV)) R.refl X V (R.- U) (R.- V))
      (R.trans (R.+-cong R.refl (R.-‿inverseʳ V)) (R.+-identityʳ _)))

  -- (A + c)(B + d) = A B + (d A + (c B + c d))
  expand : ∀ A B c d → (A R.+ c) R.* (B R.+ d) R.≈ A R.* B R.+ (d R.* A R.+ (c R.* B R.+ c R.* d))
  expand = SolveR.solve 4 (λ A B c d → (A :+ c) :* (B :+ d) := A :* B :+ (d :* A :+ (c :* B :+ c :* d))) R.refl

  -- row q of the covariance product
  step : ∀ n (Mk Ml : Fin n → R.Carrier) (a : Fin n → Fin n → R.Carrier) m q →
    Σ n (λ p → (Mk q R.* (a q p R.+ R.- (m q R.* m p))) R.* Ml p) R.≈
      Σ n (λ p → (Mk q R.* Ml p) R.* a q p) R.+ R.- ((Mk q R.* m q) R.* Σ n (λ j → Ml j R.* m j))
  step n Mk Ml a m q = R.trans (Σ-cong n (λ p → elem (Mk q) (Ml p) (a q p) (m q) (m p)))
    (row n (λ p → (Mk q R.* Ml p) R.* a q p) (Mk q R.* m q) (λ p → Ml p R.* m p))

  -- Σₚ (Σ_q Mₖ_q (a_qp − m_q m_p)) Mₗₚ = X − Aₖ Aₗ
  rhs-eq : ∀ n (Mk Ml : Fin n → R.Carrier) (a : Fin n → Fin n → R.Carrier) m →
    Σ n (λ p → Σ n (λ q → Mk q R.* (a q p R.+ R.- (m q R.* m p))) R.* Ml p) R.≈
      Σ n (λ i → Σ n (λ j → (Mk i R.* Ml j) R.* a i j)) R.+ R.- (Σ n (λ i → Mk i R.* m i) R.* Σ n (λ j → Ml j R.* m j))
  rhs-eq n Mk Ml a m = R.trans (Σ-cong n (λ p → Σ-scaleʳ n (Ml p) (λ q → Mk q R.* (a q p R.+ R.- (m q R.* m p)))))
    (R.trans (Σ-swap n n (λ p q → (Mk q R.* (a q p R.+ R.- (m q R.* m p))) R.* Ml p))
      (R.trans (Σ-cong n (step n Mk Ml a m))
        (rowʳ n (λ q → Σ n (λ p → (Mk q R.* Ml p) R.* a q p)) (λ q → Mk q R.* m q) (Σ n (λ j → Ml j R.* m j)))))

  cov-ring : ∀ n (Mk Ml : Fin n → R.Carrier) (a : Fin n → Fin n → R.Carrier) (m : Fin n → R.Carrier) c d →
    (Σ n (λ i → Σ n (λ j → (Mk i R.* Ml j) R.* a i j))
      R.+ (d R.* Σ n (λ i → Mk i R.* m i) R.+ (c R.* Σ n (λ j → Ml j R.* m j) R.+ c R.* d)))
    R.+ R.- ((Σ n (λ i → Mk i R.* m i) R.+ c) R.* (Σ n (λ j → Ml j R.* m j) R.+ d))
    R.≈ Σ n (λ p → Σ n (λ q → Mk q R.* (a q p R.+ R.- (m q R.* m p))) R.* Ml p)
  cov-ring n Mk Ml a m c d = R.trans (R.+-cong R.refl (R.-‿cong (expand Ak Al c d)))
    (R.trans (cancelV X V (Ak R.* Al)) (R.sym (rhs-eq n Mk Ml a m)))
    where Ak = Σ n (λ i → Mk i R.* m i)
          Al = Σ n (λ j → Ml j R.* m j)
          X = Σ n (λ i → Σ n (λ j → (Mk i R.* Ml j) R.* a i j))
          V = d R.* Ak R.+ (c R.* Al R.+ c R.* d)
