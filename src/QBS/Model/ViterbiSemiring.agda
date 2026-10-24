{-# OPTIONS --safe --without-K #-}

-- The Viterbi semiring ([0,∞], max, ×) on lower cuts of the rationals as a normalisable complete
-- semiring.  Sums are suprema (unions of cuts, classically resized to `Set`), so every law about
-- sums over arbitrary index sets is a union argument.  The discrete model over it is the
-- "best path" model; unlike the Boolean semiring it has non-trivial invertible weights.
module QBS.Model.ViterbiSemiring where

import Level as L
open import Function.Base using (_∘_; case_of_)
open import Function.Bundles using (Inverse; _↔_)
open import Algebra.Bundles using (CommutativeSemiring)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty.Polymorphic using (⊥)
import Data.Empty as E
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Data.Rational.Unnormalised.Base using (_≃_; _<_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Model.Semiring
import Algebra.Structures.Biased {A = Cut} _≋_ as Bi

private
  ℓ₁ = L.suc L.zero

----------------------------------------------------------------------------
-- binary maximum

infixl 6 _∨C_
_∨C_ : Cut → Cut → Cut
x ∨C y = record
  { mem = λ q → mem x q ⊎ mem y q
  ; down = λ { le (inj₁ m) → inj₁ (down x le m) ; le (inj₂ m) → inj₂ (down y le m) }
  ; open′ = λ { (inj₁ m) → let q′ , lt , m′ = open′ x m in q′ , lt , inj₁ m′
              ; (inj₂ m) → let q′ , lt , m′ = open′ y m in q′ , lt , inj₂ m′ }
  ; neg = λ lt → inj₁ (neg x lt) }

∨-cong : ∀ {x x′ y y′} → x ≋ x′ → y ≋ y′ → x ∨C y ≋ x′ ∨C y′
∨-cong (f , f′) (g , g′) =
  mk⊑ (λ { q (inj₁ m) → inj₁ (ap f q m) ; q (inj₂ m) → inj₂ (ap g q m) }) ,
  mk⊑ (λ { q (inj₁ m) → inj₁ (ap f′ q m) ; q (inj₂ m) → inj₂ (ap g′ q m) })

∨-comm : ∀ x y → x ∨C y ≋ y ∨C x
∨-comm x y = mk⊑ (λ { q (inj₁ m) → inj₂ m ; q (inj₂ m) → inj₁ m })
           , mk⊑ (λ { q (inj₁ m) → inj₂ m ; q (inj₂ m) → inj₁ m })

∨-assoc : ∀ x y z → (x ∨C y) ∨C z ≋ x ∨C (y ∨C z)
∨-assoc x y z = mk⊑ (λ { q (inj₁ (inj₁ m)) → inj₁ m ; q (inj₁ (inj₂ m)) → inj₂ (inj₁ m) ; q (inj₂ m) → inj₂ (inj₂ m) })
              , mk⊑ (λ { q (inj₁ m) → inj₁ (inj₁ m) ; q (inj₂ (inj₁ m)) → inj₁ (inj₂ m) ; q (inj₂ (inj₂ m)) → inj₂ m })

∨-identityˡ : ∀ x → zeroC ∨C x ≋ x
∨-identityˡ x = mk⊑ (λ { q (inj₁ lt) → neg x lt ; q (inj₂ m) → m }) , mk⊑ (λ q m → inj₂ m)

⊗-distribʳ-∨ : ∀ x y z → (y ∨C z) ⊗ x ≋ (y ⊗ x) ∨C (z ⊗ x)
⊗-distribʳ-∨ x y z = mk⊑ fwd , mk⊑ bwd
  where
    fwd : ∀ q → mem ((y ∨C z) ⊗ x) q → mem ((y ⊗ x) ∨C (z ⊗ x)) q
    fwd q (inj₁ lt) = inj₁ (inj₁ lt)
    fwd q (inj₂ (r , s , p , p′ , inj₁ m , ms , h)) = inj₁ (inj₂ (r , s , p , p′ , m , ms , h))
    fwd q (inj₂ (r , s , p , p′ , inj₂ m , ms , h)) = inj₂ (inj₂ (r , s , p , p′ , m , ms , h))
    bwd : ∀ q → mem ((y ⊗ x) ∨C (z ⊗ x)) q → mem ((y ∨C z) ⊗ x) q
    bwd q (inj₁ (inj₁ lt)) = inj₁ lt
    bwd q (inj₁ (inj₂ (r , s , p , p′ , m , ms , h))) = inj₂ (r , s , p , p′ , inj₁ m , ms , h)
    bwd q (inj₂ (inj₁ lt)) = inj₁ lt
    bwd q (inj₂ (inj₂ (r , s , p , p′ , m , ms , h))) = inj₂ (r , s , p , p′ , inj₂ m , ms , h)

viterbiSemiring : CommutativeSemiring ℓ₁ ℓ₁
viterbiSemiring = record
  { Carrier = Cut ; _≈_ = _≋_ ; _+_ = _∨C_ ; _*_ = _⊗_ ; 0# = zeroC ; 1# = oneC
  ; isCommutativeSemiring = Bi.isCommutativeSemiringˡ record
      { +-isCommutativeMonoid = Bi.isCommutativeMonoidˡ record
          { isSemigroup = record { isMagma = record { isEquivalence = ≋-isEquivalence ; ∙-cong = ∨-cong } ; assoc = ∨-assoc }
          ; identityˡ = ∨-identityˡ ; comm = ∨-comm }
      ; *-isCommutativeMonoid = Bi.isCommutativeMonoidˡ record
          { isSemigroup = record { isMagma = record { isEquivalence = ≋-isEquivalence ; ∙-cong = ⊗-cong } ; assoc = ⊗-assoc }
          ; identityˡ = ⊗-identityˡ ; comm = ⊗-comm }
      ; distribʳ = ⊗-distribʳ-∨
      ; zeroˡ = ⊗-zeroˡ }
  }

----------------------------------------------------------------------------
-- arbitrary suprema, resized classically

module _ (lem : ∀ (P : Set ℓ₁) → P ⊎ (P → ⊥ {ℓ₁})) where
  private
    dec : Set ℓ₁ → Bool
    dec P with lem P
    ... | inj₁ _ = true
    ... | inj₂ _ = false

    dec-true : ∀ {P} → P → dec P ≡ true
    dec-true {P} p with lem P
    ... | inj₁ _ = refl
    ... | inj₂ np with np p
    ...   | ()

    from-true : ∀ {P} → dec P ≡ true → P
    from-true {P} e with lem P
    ... | inj₁ p = p

    exfalso : ∀ {A : Set} → ⊥ {ℓ₁} → A
    exfalso ()

    lift⊥ : E.⊥ → ⊥ {ℓ₁}
    lift⊥ ()

  sumC : {I : Set ℓ₁} → (I → Cut) → Cut
  sumC {I} f = record
    { mem = λ q → q < 0Q ⊎ (dec (Σ I (λ i → mem (f i) q)) ≡ true)
    ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt)
               ; le (inj₂ e) → let (i , m) = from-true e in inj₂ (dec-true (i , down (f i) le m)) }
    ; open′ = λ { (inj₁ lt) → let r , q<r , r<0 = dense lt in r , q<r , inj₁ r<0
                ; (inj₂ e) → let (i , m) = from-true e
                                 q′ , lt , m′ = open′ (f i) m
                             in q′ , lt , inj₂ (dec-true (i , m′)) }
    ; neg = λ lt → inj₁ lt }

  private
    sum-cong : ∀ {I : Set ℓ₁} {f g : I → Cut} → (∀ i → f i ≋ g i) → sumC f ≋ sumC g
    sum-cong h =
      mk⊑ (λ { q (inj₁ lt) → inj₁ lt
             ; q (inj₂ e) → let (i , m) = from-true e in inj₂ (dec-true (i , ap (proj₁ (h i)) q m)) }) ,
      mk⊑ (λ { q (inj₁ lt) → inj₁ lt
             ; q (inj₂ e) → let (i , m) = from-true e in inj₂ (dec-true (i , ap (proj₂ (h i)) q m)) })

  viterbiComplete : CompleteSemiring ℓ₁
  viterbiComplete = record
    { commutativeSemiring = viterbiSemiring
    ; ∑ = sumC
    ; ∑-cong = sum-cong
    ; ∑-empty = λ f →
        mk⊑ (λ { q (inj₁ lt) → lt ; q (inj₂ e) → let (i , _) = from-true e in exfalso i })
        , mk⊑ (λ q lt → inj₁ lt)
    ; ∑-unit = λ f →
        mk⊑ (λ { q (inj₁ lt) → neg (f tt) lt ; q (inj₂ e) → proj₂ (from-true e) })
        , mk⊑ (λ q m → inj₂ (dec-true (tt , m)))
    ; ∑-⊎ = λ {I} {J} f →
        mk⊑ (λ { q (inj₁ lt) → inj₁ (inj₁ lt)
               ; q (inj₂ e) → case from-true e of λ
                   { (inj₁ i , m) → inj₁ (inj₂ (dec-true (i , m)))
                   ; (inj₂ j , m) → inj₂ (inj₂ (dec-true (j , m))) } })
        , mk⊑ (λ { q (inj₁ (inj₁ lt)) → inj₁ lt
                 ; q (inj₁ (inj₂ e)) → let (i , m) = from-true e in inj₂ (dec-true (inj₁ i , m))
                 ; q (inj₂ (inj₁ lt)) → inj₁ lt
                 ; q (inj₂ (inj₂ e)) → let (j , m) = from-true e in inj₂ (dec-true (inj₂ j , m)) })
    ; ∑-Σ = λ {I} {J} f →
        mk⊑ (λ { q (inj₁ lt) → inj₁ lt
               ; q (inj₂ e) → let ((i , j) , m) = from-true e in inj₂ (dec-true (i , inj₂ (dec-true (j , m)))) })
        , mk⊑ (λ { q (inj₁ lt) → inj₁ lt
                 ; q (inj₂ e) → case from-true e of λ
                     { (i , inj₁ lt) → inj₁ lt
                     ; (i , inj₂ e′) → let (j , m) = from-true e′ in inj₂ (dec-true ((i , j) , m)) } })
    ; ∑-reindex = λ {I} {J} e f →
        mk⊑ (λ { q (inj₁ lt) → inj₁ lt
               ; q (inj₂ d) → let (i , m) = from-true d in inj₂ (dec-true (Inverse.to e i , m)) })
        , mk⊑ (λ { q (inj₁ lt) → inj₁ lt
                 ; q (inj₂ d) → let (j , m) = from-true d in
                     inj₂ (dec-true (Inverse.from e j ,
                       subst (λ u → mem (f u) q) (sym (Inverse.inverseˡ e refl)) m)) })
    ; ∑-distribˡ = λ {I} x f →
        mk⊑ (λ { q (inj₁ lt) → inj₁ lt
               ; q (inj₂ (r , s , p , p′ , mr , inj₁ lt , h)) → E.⊥-elim (<-irrefl ≃-refl (<-trans p′ lt))
               ; q (inj₂ (r , s , p , p′ , mr , inj₂ e , h)) →
                   let (i , ms) = from-true e in
                   inj₂ (dec-true (i , inj₂ (r , s , p , p′ , mr , ms , h))) })
        , mk⊑ (λ { q (inj₁ lt) → inj₁ lt
                 ; q (inj₂ e) → case from-true e of λ
                     { (i , inj₁ lt) → inj₁ lt
                     ; (i , inj₂ (r , s , p , p′ , mr , ms , h)) →
                         inj₂ (r , s , p , p′ , mr , inj₂ (dec-true (i , ms)) , h) } })
    }

  -- weights invertible iff neither 0 nor ∞, decided classically
  viterbiNormalizable : NormalizableSemiring ℓ₁
  viterbiNormalizable = record
    { complete = viterbiComplete
    ; invertible? = λ m → case lem (Σ Cut (λ n → m ⊗ n ≋ oneC)) of λ
        { (inj₁ p) → inj₁ p ; (inj₂ no) → inj₂ (λ n e → no (n , e)) }
    ; nontrivial = λ e → lift⊥ (<-irrefl ≃-refl (ap (proj₂ e) 0Q 0<1))
    }
