{-# OPTIONS --safe --without-K #-}

-- Abstract soft conditioning and measures on top of a `ProbMonad`, as small independent structures, each with the laws it
-- needs and the operations derivable from it:
--   `Weights`               weights W: a commutative monoid object with an absorbing zero (`Monoidal.Symmetric.Algebra`);
--                           `SemiringWeights` also have addition
--   `SoftConditioning`      `score : W ⇒ M 1`, a semiring homomorphism from the global weights to the scalars `1 ⇒ M 1` of
--                           the Kleisli category (with `CountableSums`); derives `zero`, `scale`, `zero-bind`
--   `IsNormalizedInclusion` Prob is the normalized (mass one) part of a measure monad M: `ι : Prob ⇒ M` is an equalizer
--                           of mass and 1
--   `CountableSums`        countable sums of kernels in the Kleisli category of any monad, with the zero kernel
--   `Normalization`         optional, for inference: `normalize : M X ⇒ Prob X + 1`
-- `zero⇒` (the weight 0) is an absorbing element of the multiplication, not a zero object.
-- Linearity: binding through a kernel is linear in the measure (`sum-bind-right`) and in the kernel (`sum-bind-left`).
-- Instances: `Model/StatInstance` (discrete), `Continuous/SFiniteStat`.
open import Level using (suc; _⊔_)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as Nat
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Categories.Category.Core using (Category)

module QBS.Statistical {o h e} {C : Category o h e} where

open import Categories.Morphism C using (Mono)
open import Categories.Diagram.Equalizer C using (IsEqualizer; IsEqualizer⇒Mono)
open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.Construction.Kleisli using (Kleisli)
import Categories.Category.Monoidal.Symmetric.Algebra as Algebra
import Categories.Category.CartesianClosed.Canonical as Canonical
import Categories.Category.Cocartesian as Cocartesian
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Monad using (Monad)
open import Categories.Monad.Morphism using (Monad⇒-id)
import Categories.Morphism.Reasoning as MR
import Categories.Monad.Writer as WriterMonad
import Categories.NaturalTransformation as NT

import Categories.Monad.Notation as Notation
open import QBS.Monad.Measure using (MeasureMonad)
open import Categories.Monad.Morphism.Strong using (StrongMonad⇒)
open import QBS.Monad.Probability using (ProbMonad)

-- Weights: a commutative monoid object with an absorbing zero (`Categories.Category.Monoidal.Symmetric.Algebra`) for
-- the symmetric monoidal structure of the products of `CC`.  `Mul` is the multiplication, whose unit is the weight 1;
-- `zero⇒` is the weight 0, absorbing for `Mul` (`zeroʳ`).  Soft conditioning needs no addition of weights.
Weights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
Weights CC = Algebra.CommutativeMonoidWithZero (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

-- Weights that can also be added (e.g. `[0,∞]`): a commutative semiring; `commutativeMonoidWithZero` forgets to `Weights`.
SemiringWeights : Canonical.CartesianClosed C → Set (o ⊔ h ⊔ e)
SemiringWeights CC = Algebra.CommutativeSemiring (CSM.symmetric C (Canonical.CartesianClosed.isCartesian CC))

private variable
  ℛ : Category.Obj C
  CC : Canonical.CartesianClosed C

-- the sequence `f, z, z, …`
single-with : ∀ {a} {A : Set a} → A → A → ℕ → A
single-with z f Nat.zero = f
single-with z f (Nat.suc _) = z

-- the sequence `a, b, z, z, …`
two-with : ∀ {a} {A : Set a} → A → A → A → ℕ → A
two-with z a b Nat.zero = a
two-with z a b (Nat.suc Nat.zero) = b
two-with z a b (Nat.suc (Nat.suc _)) = z

-- Countable sums of kernels: the Kleisli category of `M` has an operation `sum` taking a sequence of kernels `X ⇒ M Y`
-- to a kernel, with the empty sum `𝟘`.  These are external operations on hom-sets (the sequence is an Agda function
-- `ℕ → K [ X , Y ]`), not morphisms of `C`.  For a measure monad `M`, `sum` is the pointwise sum of measures and
-- `𝟘` the zero measure; the sums are those of s-finite measures.  Laws: `sum` is a congruence, a sum with one nonzero
-- term is that term, the sum is invariant under permutations and regroups along ℕ ≅ ℕ × ℕ, and composition on
-- either side is linear.  Binary `⊕` is derived, with its monoid laws.
record CountableSums (M : Monad C) : Set (o ⊔ h ⊔ e) where

  private
    -- the Kleisli category of `M`: `K [ X , Y ]` is `X ⇒ M Y`, `K [ k ∘ h ]` is bind
    K = Kleisli M
    module K = Category K

  field
    -- the empty sum, the zero measure
    𝟘 : ∀ {X Y} → K [ X , Y ]
    sum : ∀ {X Y} → (ℕ → K [ X , Y ]) → K [ X , Y ]

  field
    sum-cong : ∀ {X Y} {f g : ℕ → K [ X , Y ]} → (∀ n → K [ f n ≈ g n ]) → K [ sum f ≈ sum g ]
    sum-single : ∀ {X Y} (f : K [ X , Y ]) → K [ sum (single-with 𝟘 f) ≈ f ]
    -- unfolding the first term: `Σ f = f₀ + Σ (f ∘ suc)` (a consequence of `sum-assoc` once a bijection ℕ ≅ ℕ × ℕ is
    -- constructed; stated separately so that finite sums can be manipulated without one)
    sum-unfold : ∀ {X Y} (f : ℕ → K [ X , Y ]) →
      K [ sum f ≈ sum (two-with 𝟘 (f Nat.zero) (sum (λ n → f (Nat.suc n)))) ]
    -- invariance under a permutation `σ` of ℕ with inverse `τ`
    sum-perm : ∀ {X Y} (f : ℕ → K [ X , Y ]) (σ τ : ℕ → ℕ) → (∀ n → σ (τ n) ≡ n) → (∀ n → τ (σ n) ≡ n) →
      K [ sum (λ n → f (σ n)) ≈ sum f ]
    -- regrouping a double sum along a bijection ℕ ≅ ℕ × ℕ
    sum-assoc : ∀ {X Y} (t : ℕ → ℕ → K [ X , Y ]) (pair : ℕ → ℕ → ℕ) (unpair : ℕ → ℕ × ℕ) →
      (∀ n m → unpair (pair n m) ≡ (n , m)) → (∀ k → pair (proj₁ (unpair k)) (proj₂ (unpair k)) ≡ k) →
      K [ sum (λ n → sum (t n)) ≈ sum (λ k → t (proj₁ (unpair k)) (proj₂ (unpair k))) ]
    -- binding through a kernel is linear, and `𝟘` is absorbing, on either side
    sum-bind-right : ∀ {X Y Z} (k : K [ Y , Z ]) (fs : ℕ → K [ X , Y ]) →
      K [ K [ k ∘ sum fs ] ≈ sum (λ n → K [ k ∘ fs n ]) ]
    sum-bind-left : ∀ {X Y Z} (fs : ℕ → K [ Y , Z ]) (h : K [ X , Y ]) →
      K [ K [ sum fs ∘ h ] ≈ sum (λ n → K [ fs n ∘ h ]) ]
    𝟘-bind-right : ∀ {X Y Z} (k : K [ Y , Z ]) → K [ K [ k ∘ 𝟘 {X} {Y} ] ≈ 𝟘 ]
    𝟘-bind-left : ∀ {X Y Z} (h : K [ X , Y ]) → K [ K [ 𝟘 {Y} {Z} ∘ h ] ≈ 𝟘 ]

  -- the sequence `f, 𝟘, 𝟘, …`
  single : ∀ {X Y} → K [ X , Y ] → ℕ → K [ X , Y ]
  single f = single-with 𝟘 f

  sum-𝟘 : ∀ {X Y} → K [ sum (λ (_ : ℕ) → 𝟘 {X} {Y}) ≈ 𝟘 ]
  sum-𝟘 = K.Equiv.trans (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc _) → K.Equiv.refl })) (sum-single 𝟘)

  -- the sequence `a, b, 𝟘, 𝟘, …`
  two : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → ℕ → K [ X , Y ]
  two a b = two-with 𝟘 a b

  -- binary sum
  infixl 6 _⊕_
  _⊕_ : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ]
  a ⊕ b = sum (two a b)

  private
    -- exchanging 0 and 1
    swap : ℕ → ℕ
    swap Nat.zero = Nat.suc Nat.zero
    swap (Nat.suc Nat.zero) = Nat.zero
    swap (Nat.suc (Nat.suc n)) = Nat.suc (Nat.suc n)

    swap-swap : ∀ n → swap (swap n) ≡ n
    swap-swap Nat.zero = refl
    swap-swap (Nat.suc Nat.zero) = refl
    swap-swap (Nat.suc (Nat.suc n)) = refl

  ⊕-comm : ∀ {X Y} (a b : K [ X , Y ]) → K [ a ⊕ b ≈ b ⊕ a ]
  ⊕-comm a b = K.Equiv.trans (K.Equiv.sym (sum-perm (two a b) swap swap swap-swap swap-swap))
    (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc _)) → K.Equiv.refl }))

  ⊕-identityʳ : ∀ {X Y} (a : K [ X , Y ]) → K [ a ⊕ 𝟘 ≈ a ]
  ⊕-identityʳ a = K.Equiv.trans
    (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc _)) → K.Equiv.refl }))
    (sum-single a)

  ⊕-identityˡ : ∀ {X Y} (a : K [ X , Y ]) → K [ 𝟘 ⊕ a ≈ a ]
  ⊕-identityˡ a = K.Equiv.trans (⊕-comm 𝟘 a) (⊕-identityʳ a)

  ⊕-congʳ : ∀ {X Y} (a : K [ X , Y ]) {b b′} → K [ b ≈ b′ ] → K [ a ⊕ b ≈ a ⊕ b′ ]
  ⊕-congʳ a eq = sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → eq ; (Nat.suc (Nat.suc _)) → K.Equiv.refl })

  private
    -- the sequence `a, b, c, 𝟘, 𝟘, …`
    three : ∀ {X Y} → K [ X , Y ] → K [ X , Y ] → K [ X , Y ] → ℕ → K [ X , Y ]
    three a b c Nat.zero = a
    three a b c (Nat.suc n) = two b c n

    three-unfold : ∀ {X Y} (a b c : K [ X , Y ]) → K [ sum (three a b c) ≈ a ⊕ (b ⊕ c) ]
    three-unfold a b c = K.Equiv.trans (sum-unfold (three a b c))
      (⊕-congʳ a (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc _)) → K.Equiv.refl })))

    -- the cyclic permutation 0 ↦ 2, 1 ↦ 0, 2 ↦ 1 and its inverse
    cyc cyc⁻¹ : ℕ → ℕ
    cyc Nat.zero = Nat.suc (Nat.suc Nat.zero)
    cyc (Nat.suc Nat.zero) = Nat.zero
    cyc (Nat.suc (Nat.suc Nat.zero)) = Nat.suc Nat.zero
    cyc (Nat.suc (Nat.suc (Nat.suc n))) = Nat.suc (Nat.suc (Nat.suc n))
    cyc⁻¹ Nat.zero = Nat.suc Nat.zero
    cyc⁻¹ (Nat.suc Nat.zero) = Nat.suc (Nat.suc Nat.zero)
    cyc⁻¹ (Nat.suc (Nat.suc Nat.zero)) = Nat.zero
    cyc⁻¹ (Nat.suc (Nat.suc (Nat.suc n))) = Nat.suc (Nat.suc (Nat.suc n))

    cyc-cyc⁻¹ : ∀ n → cyc (cyc⁻¹ n) ≡ n
    cyc-cyc⁻¹ Nat.zero = refl
    cyc-cyc⁻¹ (Nat.suc Nat.zero) = refl
    cyc-cyc⁻¹ (Nat.suc (Nat.suc Nat.zero)) = refl
    cyc-cyc⁻¹ (Nat.suc (Nat.suc (Nat.suc n))) = refl

    cyc⁻¹-cyc : ∀ n → cyc⁻¹ (cyc n) ≡ n
    cyc⁻¹-cyc Nat.zero = refl
    cyc⁻¹-cyc (Nat.suc Nat.zero) = refl
    cyc⁻¹-cyc (Nat.suc (Nat.suc Nat.zero)) = refl
    cyc⁻¹-cyc (Nat.suc (Nat.suc (Nat.suc n))) = refl

  -- associativity: both sides are `Σ (a, b, c, 𝟘, …)`, up to commutativity and a cyclic permutation
  ⊕-assoc : ∀ {X Y} (a b c : K [ X , Y ]) → K [ (a ⊕ b) ⊕ c ≈ a ⊕ (b ⊕ c) ]
  ⊕-assoc a b c = K.Equiv.trans (⊕-comm (a ⊕ b) c)
    (K.Equiv.trans (K.Equiv.sym (three-unfold c a b))
      (K.Equiv.trans
        (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc Nat.zero)) → K.Equiv.refl ; (Nat.suc (Nat.suc (Nat.suc _))) → K.Equiv.refl }))
        (K.Equiv.trans (sum-perm (three a b c) cyc cyc⁻¹ cyc-cyc⁻¹ cyc⁻¹-cyc) (three-unfold a b c))))

  -- binding through a kernel is additive in either argument
  ⊕-bind-right : ∀ {X Y Z} (k : K [ Y , Z ]) (a b : K [ X , Y ]) → K [ K [ k ∘ (a ⊕ b) ] ≈ K [ k ∘ a ] ⊕ K [ k ∘ b ] ]
  ⊕-bind-right k a b = K.Equiv.trans (sum-bind-right k (two a b))
    (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc _)) → 𝟘-bind-right k }))

  ⊕-bind-left : ∀ {X Y Z} (a b : K [ Y , Z ]) (h : K [ X , Y ]) → K [ K [ (a ⊕ b) ∘ h ] ≈ K [ a ∘ h ] ⊕ K [ b ∘ h ] ]
  ⊕-bind-left a b h = K.Equiv.trans (sum-bind-left (two a b) h)
    (sum-cong (λ { Nat.zero → K.Equiv.refl ; (Nat.suc Nat.zero) → K.Equiv.refl ; (Nat.suc (Nat.suc _)) → 𝟘-bind-left h }))

-- Soft conditioning on a monad `M` with countable sums.  The weights `W` are a semiring in `C`; the scalars of the Kleisli
-- category `K` of `M` are the kernels `1 ⇒ M 1`, a semiring under `⊕` and Kleisli composition.  `score : W ⇒ M 1` is the
-- measure of mass `w`, and the laws say that it is a semiring homomorphism from the global weights `1 ⇒ W` to the scalars.
-- Everything is stated at global elements, so no strength is needed and `M` is any monad: nothing here uses probability or
-- measures.  Scaling a measure `m : 1 ⇒ M X` by a weight `w` is the Kleisli composite `K [ m ∘ score ∘ w ]`.
record SoftConditioning {CC : Canonical.CartesianClosed C} (SW : SemiringWeights CC) {M : Monad C}
  (CS : CountableSums M) : Set (o ⊔ h ⊔ e) where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; ⟨_,_⟩)
  open Algebra.CommutativeMonoidWithZero (Algebra.CommutativeSemiring.commutativeMonoidWithZero SW)
    renaming (Carrier to W) public
  open Algebra.CommutativeSemiring SW using (μ⁺)
  open CountableSums CS
  private
    module M = Notation M
    K = Kleisli M
    module K = Category K

  field
    -- the weight `w` as a measure on the one-point space with total mass `w`
    score : W ⇒ M.₀ ⊤
    -- the weight 1 is the Dirac mass
    score-one : score ∘ η* ≈ M.η ⊤
    -- the weight 0 is the zero measure
    score-zero : score ∘ zero⇒ ≈ 𝟘 {⊤} {⊤}
    -- a product of weights is the composite of the scores: run `score w`, then `score w′`
    score-mul : ∀ (w w′ : ⊤ ⇒ W) → score ∘ μ* ∘ ⟨ w , w′ ⟩ ≈ K [ (score ∘ w′) ∘ (score ∘ w) ]
    -- a sum of weights is the sum of the scores
    score-add : ∀ (w w′ : ⊤ ⇒ W) → score ∘ μ⁺ ∘ ⟨ w , w′ ⟩ ≈ (score ∘ w) ⊕ (score ∘ w′)

  -- the zero measure
  zero : K [ ⊤ , ⊤ ]
  zero = score ∘ zero⇒

  -- scaling a measure by a weight
  scale : (⊤ ⇒ W) → ∀ {X} → K [ ⊤ , X ] → K [ ⊤ , X ]
  scale w m = K [ m ∘ (score ∘ w) ]

  -- the zero measure is absorbing for bind: any kernel run after it gives the zero measure
  zero-bind : ∀ {Y} (k : K [ ⊤ , Y ]) → K [ K [ k ∘ zero ] ≈ 𝟘 ]
  zero-bind k = K.Equiv.trans (K.∘-resp-≈ʳ score-zero) (𝟘-bind-right k)

-- The probability monad is the affine part of the measure monad: `Prob X` is the equalizer, inside `M X`, of the mass
-- `M ! : M X ⇒ M ⊤` (pushforward to the point) and the constant unit measure `η ⊤ ∘ !`.  So `ι : Prob ⇒ Meas` is monic,
-- and every kernel `Z ⇒ M X` of total mass one factors uniquely through `Prob X`.  This says what a probability measure
-- is, without any division; `normalize` (below) is the separate operation of dividing by mass.
record IsNormalizedInclusion
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC}
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM)) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open HomReasoning
  open MR C
  open Canonical.CartesianClosed CC using (⊤; !)
  private
    module M = Notation (MeasureMonad.monad MM)
    module inc = StrongMonad⇒ inc

  -- the component `ι X : Prob X ⇒ M X` of the inclusion: a probability measure on `X`, regarded as a measure
  open NT.NaturalTransformation inc.α public using () renaming (η to ι)

  field
    -- `Prob X` is the measures of mass one: `ι X` equalizes the mass `M !` with the unit measure `η ⊤ ∘ !`
    ι-equalizer : ∀ X → IsEqualizer (ι X) (M.₁ (! {X})) (M.η ⊤ ∘ !)

  -- a probability measure is determined by the measure it gives
  ι-mono : ∀ X → Mono (ι X)
  ι-mono X = IsEqualizer⇒Mono (ι-equalizer X)

-- Normalisation, an optional extension for inference: `normalize : M X ⇒ Prob X + 1` divides a measure by its mass.  It
-- is a left inverse of scaling a probability measure by an invertible weight (`normalize-scale`), and fails on the zero
-- measure (`normalize-zero`); the degenerate infinite-mass case is left unspecified.
record Normalization
  {P : ProbMonad ℛ CC} {MM : MeasureMonad ℛ CC} {SW : SemiringWeights CC}
  {CS : CountableSums (MeasureMonad.monad MM)}
  (CP : Cocartesian.BinaryCoproducts C)
  (inc : StrongMonad⇒ (ProbMonad.strongMonad P) (MeasureMonad.strongMonad MM))
  (SC : SoftConditioning SW CS) : Set (o ⊔ h ⊔ e)
  where

  open Category C
  open Canonical.CartesianClosed CC using (⊤; !; ⟨_,_⟩)
  open Cocartesian.BinaryCoproducts CP using (_+_; i₁; i₂)
  open SoftConditioning SC
  private
    module M = Notation (MeasureMonad.monad MM)
    module Pr = Notation (ProbMonad.monad P)
    module inc = StrongMonad⇒ inc
    -- the Kleisli category of the measure monad
    K = Kleisli (MeasureMonad.monad MM)

  -- the component `ι X : Prob X ⇒ M X` of the inclusion
  open NT.NaturalTransformation inc.α using () renaming (η to ι)

  -- a weight with a multiplicative inverse
  Invertible : (⊤ ⇒ W) → Set (h ⊔ e)
  Invertible w = Σ (⊤ ⇒ W) λ w⁻¹ → μ* ∘ ⟨ w , w⁻¹ ⟩ ≈ η*

  field
    normalize : ∀ X → M.₀ X ⇒ Pr.₀ X + ⊤
    -- normalizing a probability measure scaled by an invertible weight gives it back
    normalize-scale : ∀ {X} (w : ⊤ ⇒ W) → Invertible w → (p : ⊤ ⇒ Pr.₀ X) →
      normalize X ∘ scale w (ι X ∘ p) ≈ i₁ ∘ p
    -- the zero measure cannot be normalized
    normalize-zero : ∀ {X} (x : ⊤ ⇒ X) → normalize X ∘ M.₁ x ∘ zero ≈ i₂
