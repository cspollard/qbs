{-# OPTIONS --safe --without-K #-}

-- Variance of a signed random variable (skeleton: holes first).
--
-- `Bdd f`: both parts of `f` are pointwise bounded by a natural number.  For such `f` the product `f · g` is again a
-- signed integrable function for every signed integrable `g`.  With the mean `μ = E f` the centred variable is
-- `f − μ` and  Var f = E[(f − μ)²] = E[f²] − μ².
module QBS.Analysis.Variance where

open import Level using (suc; zero)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_)
open import Data.Empty using (⊥)
open import Algebra using (CommutativeSemiring; CommutativeRing)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import QBS.Borel.Source using (R₁)
open import QBS.Analysis.Omega using (module OmegaSemiring)
open import QBS.Analysis.Measure using (module Integration)
open import QBS.Analysis.LowerReals
open import QBS.Analysis.Meas using (module Meas)
open import QBS.Analysis.Lebesgue using (module Lebesgue)
open import QBS.Analysis.Signed
open import QBS.Analysis.SignedOmega using (module Bounded)
open import QBS.Analysis.SignedIntegral using (module SignedIntegral)
open import QBS.Classical using (LEM₀)

-- the pointwise identity behind  (f − μ)² = f² − μ f − μ f + μ²,  over an abstract commutative semiring
-- (a, b: parts of f; p, n: parts of μ)
module Alg {c ℓ} (S : CommutativeSemiring c ℓ) where
  open CommutativeSemiring S
  open import Algebra.Solver.Ring.NaturalCoefficients.Default S

  expand-alg : ∀ a b p n →
    ((a + n) * (a + n) + (b + p) * (b + p)) + ((((a * b + b * a) + (n * b + p * a)) + (n * b + p * a)) + (p * n + n * p))
    ≈ ((((a * a + b * b) + (n * a + p * b)) + (n * a + p * b)) + (p * p + n * n)) + ((a + n) * (b + p) + (b + p) * (a + n))
  expand-alg a b p n = solve 4 (λ a b p n →
    ((a :+ n) :* (a :+ n) :+ (b :+ p) :* (b :+ p)) :+ ((((a :* b :+ b :* a) :+ (n :* b :+ p :* a)) :+ (n :* b :+ p :* a)) :+ (p :* n :+ n :* p))
    := ((((a :* a :+ b :* b) :+ (n :* a :+ p :* b)) :+ (n :* a :+ p :* b)) :+ (p :* p :+ n :* n)) :+ ((a :+ n) :* (b :+ p) :+ (b :+ p) :* (a :+ n))) refl a b p n

-- 12·(M − μ²) = 1 when 3M = 1 and 2μ = 1, in an abstract signed ring
module Arith {c ℓ p} (R : CommutativeSemiring c ℓ) (F : SubSemiring R p) where
  open Signed R F
  open import Algebra using (CommutativeRing)
  open import Algebra.Solver.Ring.NaturalCoefficients.Default (CommutativeRing.commutativeSemiring signedRing)
  open import Relation.Binary.Reasoning.Setoid Sgˢ

  -- four and twelve copies of x
  x4 x12 : Sg → Sg
  x4 x = (x +S x) +S (x +S x)
  x12 x = x4 x +S (x4 x +S x4 x)

  x4-cong : ∀ {x y} → x ≃ y → x4 x ≃ x4 y
  x4-cong e = +S-cong (+S-cong e e) (+S-cong e e)

  x12-cong : ∀ {x y} → x ≃ y → x12 x ≃ x12 y
  x12-cong e = +S-cong (x4-cong e) (+S-cong (x4-cong e) (x4-cong e))

  -- twelve copies of a sum, split
  x12-+ : ∀ a b → x12 (a +S b) ≃ x12 a +S x12 b
  x12-+ a b = solve 2 (λ a b → x12′ (a :+ b) := x12′ a :+ x12′ b) ≃-refl a b
    where
      x4′ x12′ : ∀ {n} → Polynomial n → Polynomial n
      x4′ x = (x :+ x) :+ (x :+ x)
      x12′ x = x4′ x :+ (x4′ x :+ x4′ x)

  -- 12 M = 4 (3 M);  12 q = 3 (4 q)
  -- twelve copies of a product
  x12-* : ∀ a b → x12 (a *S b) ≃ a *S x12 b
  x12-* a b = solve 2 (λ a b → x12′ (a :* b) := a :* x12′ b) ≃-refl a b
    where
      x4′ x12′ : ∀ {n} → Polynomial n → Polynomial n
      x4′ x = (x :+ x) :+ (x :+ x)
      x12′ x = x4′ x :+ (x4′ x :+ x4′ x)

  x12-as-3 : ∀ x → x12 x ≃ (x4 x +S x4 x) +S x4 x
  x12-as-3 x = solve 1
    (λ x → ((x :+ x) :+ (x :+ x)) :+ (((x :+ x) :+ (x :+ x)) :+ ((x :+ x) :+ (x :+ x)))
           := (((x :+ x) :+ (x :+ x)) :+ ((x :+ x) :+ (x :+ x))) :+ ((x :+ x) :+ (x :+ x)))
    ≃-refl x

  x12-as-4 : ∀ x → x12 x ≃ x4 ((x +S x) +S x)
  x12-as-4 x = solve 1
    (λ x → ((x :+ x) :+ (x :+ x)) :+ (((x :+ x) :+ (x :+ x)) :+ ((x :+ x) :+ (x :+ x)))
           := (((x :+ x) :+ x) :+ ((x :+ x) :+ x)) :+ (((x :+ x) :+ x) :+ ((x :+ x) :+ x)))
    ≃-refl x

  x4-0 : x4 0S ≃ 0S
  x4-0 = ≃-trans (+S-cong (+S-identityˡ 0S) (+S-identityˡ 0S)) (+S-identityˡ 0S)

  -- 4 N = 1 gives 4 (−N) + 1 = 0
  neg4 : ∀ N → x4 N ≃ 1S → x4 (-S N) +S 1S ≃ 0S
  neg4 N e = begin
    x4 (-S N) +S 1S      ≈⟨ +S-cong ≃-refl (≃-sym e) ⟩
    x4 (-S N) +S x4 N    ≈⟨ solve 2 (λ q N → ((q :+ q) :+ (q :+ q)) :+ ((N :+ N) :+ (N :+ N)) := ((q :+ N) :+ (q :+ N)) :+ ((q :+ N) :+ (q :+ N))) ≃-refl (-S N) N ⟩
    x4 (-S N +S N)       ≈⟨ x4-cong (+S-inverseˡ N) ⟩
    x4 0S                ≈⟨ x4-0 ⟩
    0S ∎

  -- 4·1 + 3r = 1 when r + 1 = 0
  finish : ∀ r → r +S 1S ≃ 0S → x4 1S +S ((r +S r) +S r) ≃ 1S
  finish r e = begin
    x4 1S +S ((r +S r) +S r)
      ≈⟨ solve 2 (λ r o → ((o :+ o) :+ (o :+ o)) :+ ((r :+ r) :+ r)
                          := o :+ (((r :+ o) :+ (r :+ o)) :+ (r :+ o))) ≃-refl r 1S ⟩
    1S +S (((r +S 1S) +S (r +S 1S)) +S (r +S 1S))
                                            ≈⟨ +S-cong ≃-refl (+S-cong (+S-cong e e) e) ⟩
    1S +S ((0S +S 0S) +S 0S)                ≈⟨ +S-cong ≃-refl (≃-trans (+S-cong (+S-identityˡ 0S) ≃-refl) (+S-identityˡ 0S)) ⟩
    1S +S 0S                                ≈⟨ ≃-trans (+S-comm 1S 0S) (+S-identityˡ 1S) ⟩
    1S ∎

  var-arith : ∀ M μ → (M +S M) +S M ≃ 1S → μ +S μ ≃ 1S → x12 (M +S (-S (μ *S μ))) ≃ 1S
  var-arith M μ hM hμ = begin
    x12 (M +S (-S N))                              ≈⟨ x12-+ M (-S N) ⟩
    x12 M +S x12 (-S N)                            ≈⟨ +S-cong (≃-trans (x12-as-4 M) (x4-cong hM)) (x12-as-3 (-S N)) ⟩
    x4 1S +S ((x4 (-S N) +S x4 (-S N)) +S x4 (-S N))  ≈⟨ finish (x4 (-S N)) (neg4 N x4N) ⟩
    1S ∎
    where
      N = μ *S μ
      x4N : x4 N ≃ 1S
      x4N = ≃-trans (solve 1 (λ μ → (μ :* μ :+ μ :* μ) :+ (μ :* μ :+ μ :* μ) := (μ :+ μ) :* (μ :+ μ)) ≃-refl μ)
                    (≃-trans (*S-cong hμ hμ) (*S-identityˡ 1S))

module Variance (lem : LEM₀) where
  open Lebesgue lem
  open Meas lem
  open SignedIntegral lem
  open Integration A using (Measure; IsProb; I)
  open OmegaSemiring A using (_≈_; _≤_; ≤-+ʳ; _+_; _*_; 0#; 1#; refl; sym; trans; +-cong; *-cong; ≤-refl; ≤-trans; ≤-reflexive; +-mono; *-mono)
  open Bounded A
  open Sg
  open SF

  -- pointwise bounded parts
  Bdd : ∀ {m} → SF m → Set₁
  Bdd f = Σ ℕ λ N → ∀ x → (f⁺ f x ≤ nat N) × (f⁻ f x ≤ nat N)

  private
    bnd-resp : ∀ {a b} → a ≈ b → Bnd a → Bnd b
    bnd-resp = SubSemiring.Is-resp finite
    bnd-+ : ∀ {a b} → Bnd a → Bnd b → Bnd (a + b)
    bnd-+ = SubSemiring.Is-+ finite
    bnd-* : ∀ {a b} → Bnd a → Bnd b → Bnd (a * b)
    bnd-* = SubSemiring.Is-* finite
    bnd-mono : ∀ {a b} → a ≤ b → Bnd b → Bnd a
    bnd-mono a≤b (n , h) = n , ≤-trans a≤b h

    -- u·a + v·b ≤ N·(a + b) when u, v ≤ N
    mix-bound : ∀ N {u v} a b → u ≤ nat N → v ≤ nat N → u * a + v * b ≤ nat N * (a + b)
    mix-bound N {u} {v} a b hu hv = ≤-trans
      (+-mono (≤-trans (≤-reflexive (OmegaSemiring.*-comm A u a)) (≤-trans (*-mono a hu) (≤-reflexive (OmegaSemiring.*-comm A a (nat N)))))
              (≤-trans (≤-reflexive (OmegaSemiring.*-comm A v b)) (≤-trans (*-mono b hv) (≤-reflexive (OmegaSemiring.*-comm A b (nat N))))))
      (≤-reflexive (sym (OmegaSemiring.distribˡ A (nat N) a b)))

    -- a measurable function dominated by N·(g⁺ + g⁻) has a bounded integral
    J-bound : ∀ m {φ} (p : Meas φ) (g : SF m) N → (∀ x → φ x ≤ nat N * (f⁺ g x + f⁻ g x)) → Bnd (J m φ p)
    J-bound m {φ} p g N le = bnd-mono
      (J-mono m p (Meas-⊗ {λ _ → nat N} {λ x → f⁺ g x + f⁻ g x} (Meas-const (nat N)) S) le)
      (bnd-resp (sym (trans (J-scale m (nat N) {λ x → f⁺ g x + f⁻ g x} S) (*-cong {nat N} {nat N} refl (J-add m (f⁺-meas g) (f⁻-meas g)))))
        (bnd-* (N , ≤-refl) (bnd-+ (f⁺-int g) (f⁻-int g))))
      where S = Meas-⊕ {f⁺ g} {f⁻ g} (f⁺-meas g) (f⁻-meas g)

  -- product with a pointwise-bounded left factor
  _*SF_[_] : ∀ {m} (f g : SF m) → Bdd f → SF m
  _*SF_[_] {m} f g (N , b) = record
    { f⁺ = λ x → f⁺ f x * f⁺ g x + f⁻ f x * f⁻ g x
    ; f⁻ = λ x → f⁺ f x * f⁻ g x + f⁻ f x * f⁺ g x
    ; f⁺-meas = Meas-⊕ {λ x → f⁺ f x * f⁺ g x} {λ x → f⁻ f x * f⁻ g x}
        (Meas-⊗ {f⁺ f} {f⁺ g} (f⁺-meas f) (f⁺-meas g)) (Meas-⊗ {f⁻ f} {f⁻ g} (f⁻-meas f) (f⁻-meas g))
    ; f⁻-meas = Meas-⊕ {λ x → f⁺ f x * f⁻ g x} {λ x → f⁻ f x * f⁺ g x}
        (Meas-⊗ {f⁺ f} {f⁻ g} (f⁺-meas f) (f⁻-meas g)) (Meas-⊗ {f⁻ f} {f⁺ g} (f⁻-meas f) (f⁺-meas g))
    ; f⁺-int = J-bound m _ g N (λ x → mix-bound N (f⁺ g x) (f⁻ g x) (proj₁ (b x)) (proj₂ (b x)))
    ; f⁻-int = J-bound m _ g N (λ x → ≤-trans (mix-bound N (f⁻ g x) (f⁺ g x) (proj₁ (b x)) (proj₂ (b x)))
        (≤-reflexive (*-cong {nat N} {nat N} refl (OmegaSemiring.+-comm A (f⁻ g x) (f⁺ g x)))))
    }

  Bdd-+ : ∀ {m} {f g : SF m} → Bdd f → Bdd g → Bdd (f +SF g)
  Bdd-+ {f = f} {g} (N , bf) (M , bg) = N ℕ.+ M , λ x →
    ≤-trans (+-mono (proj₁ (bf x)) (proj₁ (bg x))) (≤-reflexive (sym (nat-+ N M))) ,
    ≤-trans (+-mono (proj₂ (bf x)) (proj₂ (bg x))) (≤-reflexive (sym (nat-+ N M)))

  Bdd-const : ∀ {m} (pm : IsProb m) (a : Sg) → Bdd (constSF {m} pm a)
  Bdd-const pm a with pos-fin a | neg-fin a
  ... | (n , hn) | (k , hk) = n ℕ.+ k , λ _ →
    ≤-trans hn (≤-trans (≤-+ʳ {nat n} {nat k}) (≤-reflexive (sym (nat-+ n k)))) ,
    ≤-trans hk (≤-trans (≤-trans (≤-+ʳ {nat k} {nat n}) (≤-reflexive (OmegaSemiring.+-comm A (nat k) (nat n)))) (≤-reflexive (sym (nat-+ n k))))

  -- the centred variable f − E f, and the variance
  centre : ∀ {m} → IsProb m → (f : SF m) → SF m
  centre {m} pm f = f +SF constSF {m} pm (-S E f)

  Bdd-centre : ∀ {m} (pm : IsProb m) (f : SF m) → Bdd f → Bdd (centre {m} pm f)
  Bdd-centre {m} pm f b = Bdd-+ {m} {f} {constSF {m} pm (-S E f)} b (Bdd-const {m} pm (-S E f))

  abstract
   Var : ∀ {m} (pm : IsProb m) (f : SF m) (b : Bdd f) → Sg
   Var {m} pm f b = E ((centre {m} pm f) *SF (centre {m} pm f) [ Bdd-centre {m} pm f b ])

  -- (f − μ)² = f² − μ f − μ f + μ², pointwise on the parts
  expand : ∀ {m} (pm : IsProb m) (f : SF m) (b : Bdd f) →
    ((centre {m} pm f) *SF (centre {m} pm f) [ Bdd-centre {m} pm f b ]) ≈SF
    ((((f *SF f [ b ]) +SF scaleSF (-S E f) f) +SF scaleSF (-S E f) f) +SF constSF {m} pm (E f *S E f))
  expand {m} pm f b x = Alg.expand-alg (OmegaSemiring.commutativeSemiring A) (f⁺ f x) (f⁻ f x) (J m (f⁺ f) (f⁺-meas f)) (J m (f⁻ f) (f⁻-meas f))

  -- the signed-ring part of the computation
  ring-fin : ∀ F ES t → ES ≃ -S t → ((F +S ES) +S ES) +S t ≃ F +S -S t
  ring-fin F ES t e = ≃-trans (+S-cong {(F +S ES) +S ES} {(F +S -S t) +S -S t} {t} {t}
      (+S-cong {F +S ES} {F +S -S t} {ES} { -S t } (+S-cong {F} {F} {ES} { -S t } ≃-refl e) e) ≃-refl)
    (≃-trans (+S-assoc (F +S -S t) (-S t) t)
    (≃-trans (+S-cong {F +S -S t} {F +S -S t} { -S t +S t } {0S} ≃-refl (+S-inverseˡ t))
    (≃-trans (+S-comm (F +S -S t) 0S) (+S-identityˡ (F +S -S t)))))

  -- linearity of E on the expansion (abstract summands, so that nothing unfolds)
  lin : ∀ {m} (F S1 K : SF m) (t : Sg) → E K ≃ t →
    E (((F +SF S1) +SF S1) +SF K) ≃ ((E F +S E S1) +S E S1) +S t
  lin {m} F S1 K t eK = ≃-trans {E (((F +SF S1) +SF S1) +SF K)} {E ((F +SF S1) +SF S1) +S E K} {((E F +S E S1) +S E S1) +S t}
    (E-+ ((F +SF S1) +SF S1) K)
    (+S-cong {E ((F +SF S1) +SF S1)} {(E F +S E S1) +S E S1} {E K} {t}
      (≃-trans {E ((F +SF S1) +SF S1)} {E (F +SF S1) +S E S1} {(E F +S E S1) +S E S1} (E-+ (F +SF S1) S1)
        (+S-cong {E (F +SF S1)} {E F +S E S1} {E S1} {E S1} (E-+ F S1) ≃-refl))
      eK)

  open import Algebra.Properties.Ring (CommutativeRing.ring signedRing) using (-‿distribˡ-*)

  neg-mul : ∀ x → (-S x) *S x ≃ -S (x *S x)
  neg-mul x = ≃-sym (-‿distribˡ-* x x)

  -- everything abstract: the variance identity from the pointwise expansion
  var-gen : ∀ {m} (CC F S1 K : SF m) (t : Sg) →
    CC ≈SF (((F +SF S1) +SF S1) +SF K) → E K ≃ t → E S1 ≃ -S t → E CC ≃ E F +S -S t
  var-gen {m} CC F S1 K t e eK eS =
    ≃-trans {E CC} {E (((F +SF S1) +SF S1) +SF K)} {E F +S -S t} (E-cong {m} {CC} {((F +SF S1) +SF S1) +SF K} e)
      (≃-trans {E (((F +SF S1) +SF S1) +SF K)} {((E F +S E S1) +S E S1) +S t} {E F +S -S t}
        (lin {m} F S1 K t eK) (ring-fin (E F) (E S1) t eS))

  -- Var f = E[f²] − (E f)²
  abstract
   var-formula : ∀ {m} (pm : IsProb m) (f : SF m) (b : Bdd f) →
     Var {m} pm f b ≃ E (f *SF f [ b ]) +S (-S (E f *S E f))
   var-formula {m} pm f b = var-gen {m} ((centre {m} pm f) *SF (centre {m} pm f) [ Bdd-centre {m} pm f b ])
     (f *SF f [ b ]) (scaleSF (-S E f) f) (constSF {m} pm (E f *S E f)) (E f *S E f)
     (expand {m} pm f b) (E-const {m} pm (E f *S E f))
     (≃-trans {E (scaleSF (-S E f) f)} {(-S E f) *S E f} { -S (E f *S E f) } (E-scale (-S E f) f) (neg-mul (E f)))
