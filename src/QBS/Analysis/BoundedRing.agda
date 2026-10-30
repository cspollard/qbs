{-# OPTIONS --safe --without-K #-}

-- The commutative ring of bounded signed random variables on a probability space, with its expectation.
--
-- `BSF m` is the pairs of a signed function (`SF m`) and a pointwise bound (`Bdd`); two are equal when their
-- parts cross-add pointwise (`≈SF`).  The operations are those of `Analysis/SignedIntegral` and `Analysis/Variance`
-- (`+SF`, `-SF`, `constSF`, `*SF`), and `E` is additive.  Together with `Analysis/Estimator` this gives the
-- estimator theorem for any family of bounded random variables.
--
-- Equality is pointwise equality of the signed values `f⁺ x − f⁻ x` in the ring `Sg`, which is an equivalence
-- (it needs the witness of `Signed`); the ring laws are then the laws of `signedRing`, pointwise.  `E` respects it
-- because bounded elements of `A` can be cancelled (`cancel-bnd`).
module QBS.Analysis.BoundedRing where

open import Level using (suc; zero)
open import Algebra using (CommutativeRing; RawRing)
open import Algebra.Morphism.Structures using (module RingMorphisms)
import Algebra.Morphism.RingMonomorphism as RingMono
import Algebra.Construct.Pointwise
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Signed
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Analysis.Variance using (module Variance)
open import QBS.Analysis.LowerRealsArch using (lowerRealsArch)
open import QBS.Analysis.Archimedean using (Arch)
open import QBS.Analysis.BoundedCancel using (module BoundedCancel)

module BoundedRing (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) where
  open Lebesgue lem using (A; J; J-add)
  open Meas lem using (Meas-⊗)
  open Integration A using (Measure; IsProb)
  open SignedIntegral lem
  open Variance lem
  open Bounded A
  open OmegaSemiring A using (_+_; _*_; _≈_; _≤_; 0#; refl; sym; trans; +-cong; +-comm; +-assoc)
  open SF
  open Sg

  open Arch (lowerRealsArch lem) using (half) renaming (half+half to hh)
  open BoundedCancel A half hh using (cancel-bnd)

  -- the parts of a product, integrated (over an abstract measure, so the types stay small)
  mul⁺ : ∀ {m} (f g : SF m) (bf : Bdd f) →
    J m (f⁺ (f *SF g [ bf ])) (f⁺-meas (f *SF g [ bf ])) ≈
      J m (λ x → f⁺ f x * f⁺ g x) (Meas-⊗ {f⁺ f} {f⁺ g} (f⁺-meas f) (f⁺-meas g)) +
      J m (λ x → f⁻ f x * f⁻ g x) (Meas-⊗ {f⁻ f} {f⁻ g} (f⁻-meas f) (f⁻-meas g))
  mul⁺ {m} f g bf = J-add m {λ x → f⁺ f x * f⁺ g x} {λ x → f⁻ f x * f⁻ g x}
    (Meas-⊗ {f⁺ f} {f⁺ g} (f⁺-meas f) (f⁺-meas g)) (Meas-⊗ {f⁻ f} {f⁻ g} (f⁻-meas f) (f⁻-meas g))

  mul⁻ : ∀ {m} (f g : SF m) (bf : Bdd f) →
    J m (f⁻ (f *SF g [ bf ])) (f⁻-meas (f *SF g [ bf ])) ≈
      J m (λ x → f⁺ f x * f⁻ g x) (Meas-⊗ {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g)) +
      J m (λ x → f⁻ f x * f⁺ g x) (Meas-⊗ {f⁻ f} {f⁺ g} (f⁻-meas f) (f⁺-meas g))
  mul⁻ {m} f g bf = J-add m {λ x → f⁺ f x * f⁻ g x} {λ x → f⁻ f x * f⁺ g x}
    (Meas-⊗ {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g)) (Meas-⊗ {f⁻ f} {f⁺ g} (f⁻-meas f) (f⁺-meas g))

  -- signed values with equal parts are equal
  ≃-parts : ∀ {x y : Sg} → pos x ≈ pos y → neg x ≈ neg y → x ≃ y
  ≃-parts {x} {y} ep en = mk≃ 0# (SubSemiring.Is-0 finite)
    (+-cong {pos x + neg y} {pos y + neg x} {0#} {0#} (+-cong {pos x} {pos y} {neg y} {neg x} ep (sym en)) refl)

  module _ (m : Measure) (pm : IsProb m) where

    -- bounded signed random variables
    BSF : Set₁
    BSF = Σ (SF m) Bdd

    -- the signed value at a point
    val : BSF → R₁ → Sg
    val (f , N , b) x = f⁺ f x − f⁻ f x [ (N , proj₁ (b x)) , (N , proj₂ (b x)) ]

    infix 4 _≈B_
    _≈B_ : BSF → BSF → Set₁
    f ≈B g = ∀ x → val f x ≃ val g x

    Bdd-* : ∀ {f g : SF m} (bf : Bdd f) → Bdd g → Bdd (f *SF g [ bf ])
    Bdd-* (N , b) (M , c) = (N ℕ.* M ℕ.+ N ℕ.* M) , λ x →
      proj₂ (SubSemiring.Is-+ finite (SubSemiring.Is-* finite (N , proj₁ (b x)) (M , proj₁ (c x)))
                                     (SubSemiring.Is-* finite (N , proj₂ (b x)) (M , proj₂ (c x)))) ,
      proj₂ (SubSemiring.Is-+ finite (SubSemiring.Is-* finite (N , proj₁ (b x)) (M , proj₂ (c x)))
                                     (SubSemiring.Is-* finite (N , proj₂ (b x)) (M , proj₁ (c x))))

    Bdd-neg : ∀ {f : SF m} → Bdd f → Bdd (-SF f)
    Bdd-neg (N , b) = N , λ x → proj₂ (b x) , proj₁ (b x)

    0B 1B : BSF
    0B = constSF {m} pm 0S , Bdd-const {m} pm 0S
    1B = constSF {m} pm 1S , Bdd-const {m} pm 1S

    infixl 6 _+B_
    infixl 7 _*B_
    _+B_ _*B_ : BSF → BSF → BSF
    (f , bf) +B (g , bg) = (f +SF g) , Bdd-+ {m} {f} {g} bf bg
    (f , bf) *B (g , bg) = (f *SF g [ bf ]) , Bdd-* {f} {g} bf bg

    -B_ : BSF → BSF
    -B (f , bf) = -SF f , Bdd-neg {f} bf

    -- `val` is a ring homomorphism into the pointwise ring of signed values
    private
      module PW = Algebra.Construct.Pointwise R₁
      Fn = PW.commutativeRing signedRing

      rawB : RawRing (suc zero) (suc zero)
      rawB = record { Carrier = BSF ; _≈_ = _≈B_ ; _+_ = _+B_ ; _*_ = _*B_ ; -_ = -B_ ; 0# = 0B ; 1# = 1B }

      open RingMorphisms rawB (CommutativeRing.rawRing Fn)

      val-hom : IsRingMonomorphism val
      val-hom = record
        { isRingHomomorphism = record
            { isSemiringHomomorphism = record
                { isNearSemiringHomomorphism = record
                    { +-isMonoidHomomorphism = record
                        { isMagmaHomomorphism = record
                            { isRelHomomorphism = record { cong = λ e → e }
                            ; homo = λ f g x → ≃-parts refl refl }
                        ; ε-homo = λ x → ≃-parts refl refl }
                    ; *-homo = λ f g x → ≃-parts refl refl }
                ; 1#-homo = λ x → ≃-parts refl refl }
            ; -‿homo = λ f x → ≃-parts refl refl }
        ; injective = λ e → e
        }

    boundedRing : CommutativeRing (suc zero) (suc zero)
    boundedRing = record
      { Carrier = BSF ; _≈_ = _≈B_ ; _+_ = _+B_ ; _*_ = _*B_ ; -_ = -B_ ; 0# = 0B ; 1# = 1B
      ; isCommutativeRing = RingMono.isCommutativeRing val-hom (CommutativeRing.isCommutativeRing Fn) }

    -- the expectation
    E-B : BSF → Sg
    E-B f = E (proj₁ f)

    -- equal values pointwise: the cross sums agree, by cancelling the (bounded) witness
    ≈B⇒≈SF : ∀ {f g : BSF} → f ≈B g → proj₁ f ≈SF proj₁ g
    ≈B⇒≈SF {f} {g} e x with e x
    ... | mk≃ k fk eq = cancel-bnd {k} {a} {b} fk
        (trans {k + a} {a + k} {k + b} (+-comm k a) (trans {a + k} {b + k} {k + b} eq (+-comm b k)))
      where
        a = f⁺ (proj₁ f) x + f⁻ (proj₁ g) x
        b = f⁺ (proj₁ g) x + f⁻ (proj₁ f) x

    E-B-cong : ∀ {f g} → f ≈B g → E-B f ≃ E-B g
    E-B-cong {f} {g} e = E-cong {m} {proj₁ f} {proj₁ g} (≈B⇒≈SF {f} {g} e)

    E-B-+ : ∀ f g → E-B (f +B g) ≃ E-B f +S E-B g
    E-B-+ (f , _) (g , _) = E-+ f g

    -- constants: the embedding of signed values, with E (κ s) = s and E (κ s · x) = s · E x
    κB : Sg → BSF
    κB s = constSF {m} pm s , Bdd-const {m} pm s

    E-κB : ∀ s → E-B (κB s) ≃ s
    E-κB s = E-const {m} pm s

    E-κB* : ∀ s x → E-B (κB s *B x) ≃ s *S E-B x
    E-κB* s (f , bf) = ≃-trans {E (proj₁ (κB s *B (f , bf)))} {E (scaleSF s f)} {s *S E f}
      (E-cong {m} {proj₁ (κB s *B (f , bf))} {scaleSF s f} (λ x → refl)) (E-scale s f)
