{-# OPTIONS --safe --without-K #-}

-- Ordered-field facts about the unnormalised rationals in the form used for lower cuts: plain
-- statements without instance arguments, plus the Archimedean property.  Unnormalised rationals
-- keep arithmetic computational; equality is ≃ and the order respects it.
module QBS.Analysis.RationalLemmas where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤ
open import Data.Rational.Unnormalised.Base as Q using
  (ℚᵘ; mkℚᵘ; 0ℚᵘ; 1ℚᵘ; _+_; _*_; -_; 1/_; _<_; _≤_; _≃_; *≡*; *≤*; *<*; ↥_; ↧_; ↧ₙ_; Positive; NonNegative; positive; nonNegative)
import Data.Rational.Unnormalised.Properties as P
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl; cong; subst)

Q = ℚᵘ
0Q 1Q : Q
0Q = 0ℚᵘ
1Q = 1ℚᵘ

infix 4 _≤Q_ _<Q_ _≃Q_
_≤Q_ _<Q_ _≃Q_ : Q → Q → Set
_≤Q_ = _≤_
_<Q_ = _<_
_≃Q_ = _≃_

≃-refl : ∀ {p} → p ≃ p
≃-refl = P.≃-refl
≃-sym : ∀ {p q} → p ≃ q → q ≃ p
≃-sym = P.≃-sym
≃-trans : ∀ {p q r} → p ≃ q → q ≃ r → p ≃ r
≃-trans = P.≃-trans

≤-refl : ∀ {p} → p ≤ p
≤-refl = P.≤-refl
≤-trans : ∀ {p q r} → p ≤ q → q ≤ r → p ≤ r
≤-trans = P.≤-trans
≤-≃ : ∀ {p q} → p ≃ q → p ≤ q
≤-≃ = P.≤-reflexive
≤-antisym : ∀ {p q} → p ≤ q → q ≤ p → p ≃ q
≤-antisym = P.≤-antisym
<-≤ : ∀ {p q} → p < q → p ≤ q
<-≤ = P.<⇒≤
<-trans : ∀ {p q r} → p < q → q < r → p < r
<-trans = P.<-trans
≤-<-trans : ∀ {p q r} → p ≤ q → q < r → p < r
≤-<-trans = P.≤-<-trans
<-≤-trans : ∀ {p q r} → p < q → q ≤ r → p < r
<-≤-trans = P.<-≤-trans
<-irrefl : ∀ {p q} → p ≃ q → ¬ (p < q)
<-irrefl = P.<-irrefl
≃-<ʳ : ∀ {p q r} → q ≃ r → p < q → p < r
≃-<ʳ = P.<-respʳ-≃
≃-<ˡ : ∀ {p q r} → q ≃ r → q < p → r < p
≃-<ˡ = P.<-respˡ-≃
dense : ∀ {p q} → p < q → Σ Q (λ r → p < r × r < q)
dense = P.<-dense
total : ∀ p q → p ≤ q ⊎ q ≤ p
total = P.≤-total
not-≤⇒< : ∀ {p q} → ¬ (p ≤ q) → q < p
not-≤⇒< = P.≰⇒>

≤-resp : ∀ {p p′ q q′} → p ≃ p′ → q ≃ q′ → p ≤ q → p′ ≤ q′
≤-resp e e′ le = ≤-trans (≤-≃ (≃-sym e)) (≤-trans le (≤-≃ e′))

+-cong : ∀ {p p′ q q′} → p ≃ p′ → q ≃ q′ → p + q ≃ p′ + q′
+-cong = P.+-cong
*-cong : ∀ {p p′ q q′} → p ≃ p′ → q ≃ q′ → p * q ≃ p′ * q′
*-cong = P.*-cong
+-comm : ∀ p q → p + q ≃ q + p
+-comm = P.+-comm
+-assoc : ∀ p q r → (p + q) + r ≃ p + (q + r)
+-assoc = P.+-assoc
+-identityˡ : ∀ p → 0Q + p ≃ p
+-identityˡ = P.+-identityˡ
+-identityʳ : ∀ p → p + 0Q ≃ p
+-identityʳ = P.+-identityʳ
+-inverseʳ : ∀ p → p + (- p) ≃ 0Q
+-inverseʳ = P.+-inverseʳ
*-comm : ∀ p q → p * q ≃ q * p
*-comm = P.*-comm
*-assoc : ∀ p q r → (p * q) * r ≃ p * (q * r)
*-assoc = P.*-assoc
*-identityˡ : ∀ p → 1Q * p ≃ p
*-identityˡ = P.*-identityˡ
*-zeroˡ : ∀ p → 0Q * p ≃ 0Q
*-zeroˡ = P.*-zeroˡ
*-distribˡ-+ : ∀ p q r → p * (q + r) ≃ p * q + p * r
*-distribˡ-+ = P.*-distribˡ-+
*-distribʳ-+ : ∀ p q r → (q + r) * p ≃ q * p + r * p
*-distribʳ-+ = P.*-distribʳ-+

+-mono-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
+-mono-≤ = P.+-mono-≤
+-mono-<-≤ : ∀ {a b c d} → a < b → c ≤ d → a + c < b + d
+-mono-<-≤ = P.+-mono-<-≤
+-mono-≤-< : ∀ {a b c d} → a ≤ b → c < d → a + c < b + d
+-mono-≤-< = P.+-mono-≤-<
+-mono-< : ∀ {a b c d} → a < b → c < d → a + c < b + d
+-mono-< = P.+-mono-<

-- positivity
pos : ∀ {p} → 0Q < p → Positive p
pos = positive
nonneg : ∀ {p} → 0Q ≤ p → NonNegative p
nonneg = nonNegative

*-mono-<-pos : ∀ {r p q} → 0Q < r → p < q → r * p < r * q
*-mono-<-pos {r} 0<r p<q = P.*-monoʳ-<-pos r {{pos 0<r}} p<q
*-mono-≤-nn : ∀ {r p q} → 0Q ≤ r → p ≤ q → r * p ≤ r * q
*-mono-≤-nn {r} 0≤r p≤q = P.*-monoʳ-≤-nonNeg r {{nonneg 0≤r}} p≤q
*-pos : ∀ {p q} → 0Q < p → 0Q < q → 0Q < p * q
*-pos {p} {q} 0<p 0<q = ≃-<ˡ (P.*-zeroʳ p) (*-mono-<-pos {p} {0Q} {q} 0<p 0<q)

-- division by a positive number
inv : ∀ {s} → 0Q < s → Σ Q (λ t → t * s ≃ 1Q)
inv {s} 0<s = (1/_ s {{P.pos⇒nonZero s {{pos 0<s}}}}) , P.*-inverseˡ s {{P.pos⇒nonZero s {{pos 0<s}}}}

----------------------------------------------------------------------------
-- natural numbers and the Archimedean property

nat : ℕ → Q
nat k = mkℚᵘ (+ k) 0

nat-suc : ∀ k → nat (suc k) ≃ nat k + 1Q
nat-suc k = *≡* (≡.trans (ℤ.*-identityʳ (+ suc k))
  (≡.sym (≡.trans (ℤ.*-identityʳ _)
    (≡.trans (≡.cong₂ ℤ._+_ (ℤ.*-identityʳ (+ k)) (ℤ.*-identityʳ (+ 1)))
      (≡.cong +_ (ℕ.+-comm k 1))))))

nat-bound : ∀ p → Σ ℕ (λ k → p ≤ nat k)
nat-bound (mkℚᵘ (+ m) d) = m , *≤* (≡.subst₂ ℤ._≤_ (ℤ.pos-* m 1) (ℤ.pos-* m (suc d))
  (ℤ.+≤+ (ℕ.*-monoʳ-≤ m (ℕ.s≤s ℕ.z≤n))))
nat-bound (mkℚᵘ -[1+ m ] d) = 0 , *≤* (≡.subst (ℤ._≤ (+ 0) ℤ.* (+ suc d))
  (≡.sym (ℤ.*-identityʳ -[1+ m ])) (≡.subst (-[1+ m ] ℤ.≤_) (≡.sym (ℤ.*-zeroˡ (+ suc d))) ℤ.-≤+))

nat-suc* : ∀ k ε → nat (suc k) * ε ≃ nat k * ε + ε
nat-suc* k ε = ≃-trans (*-cong (nat-suc k) (≃-refl {ε}))
  (≃-trans (*-distribʳ-+ ε (nat k) 1Q) (+-cong (≃-refl {nat k * ε}) (*-identityˡ ε)))

arch : ∀ p {ε} → 0Q < ε → Σ ℕ (λ k → p ≤ nat k * ε)
arch p {ε} 0<ε with inv 0<ε
... | t , hte with nat-bound (p * t)
... | k , h = k , ≤-resp (≃-sym eq) (*-comm ε (nat k)) step
  where
    eq : p ≃ (p * t) * ε
    eq = ≃-sym (≃-trans (*-assoc p t ε) (≃-trans (*-cong (≃-refl {p}) hte) (P.*-identityʳ p)))
    step : (p * t) * ε ≤ ε * nat k
    step = ≤-trans (≤-≃ (*-comm (p * t) ε)) (*-mono-≤-nn (<-≤ 0<ε) h)

----------------------------------------------------------------------------
-- further helpers

open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

add-sub : ∀ r q → r + (q + - r) ≃ q
add-sub = solve 2 (λ r q → r :+ (q :+ :- r) := q) ≃-refl

sub-add : ∀ q q′ → (q + - q′) + q′ ≃ q
sub-add = solve 2 (λ q q′ → (q :+ :- q′) :+ q′ := q) ≃-refl

-- trichotomy-based decisions
pos-or-nonpos : ∀ s → 0Q < s ⊎ s ≤ 0Q
pos-or-nonpos s with P.<-cmp 0Q s
... | tri< a _ _ = inj₁ a
... | tri≈ _ b _ = inj₂ (≤-≃ (≃-sym b))
... | tri> _ _ c = inj₂ (<-≤ c)

neg-or-nonneg : ∀ s → s < 0Q ⊎ 0Q ≤ s
neg-or-nonneg s with P.<-cmp s 0Q
... | tri< a _ _ = inj₁ a
... | tri≈ _ b _ = inj₂ (≤-≃ (≃-sym b))
... | tri> _ _ c = inj₂ (<-≤ c)

-- a negative number is a sum of two negatives
split-neg : ∀ {q} → q < 0Q → Σ Q (λ a → Σ Q (λ b → a < 0Q × b < 0Q × q ≤ a + b))
split-neg {q} q<0 with dense q<0
... | a , q<a , a<0 = a , q + - a ,
  a<0 ,
  ≃-<ʳ (+-inverseʳ a) (+-mono-<-≤ q<a (≤-refl {(- a)})) ,
  ≤-≃ (≃-sym (≃-trans (+-comm a (q + - a)) (sub-add q a)))

-- q < q′ gives a negative difference
neg-diff : ∀ {q q′} → q < q′ → q + - q′ < 0Q
neg-diff {q} {q′} q<q′ = ≃-<ʳ (+-inverseʳ q′) (+-mono-<-≤ q<q′ (≤-refl {(- q′)}))

0<1 : 0Q < 1Q
0<1 = P.positive⁻¹ 1Q

*-mono-<-posʳ : ∀ {s p q} → 0Q < s → p < q → p * s < q * s
*-mono-<-posʳ {s} {p} {q} 0<s p<q = ≃-<ˡ (*-comm s p) (≃-<ʳ (*-comm s q) (*-mono-<-pos 0<s p<q))

*-mono-≤-nnʳ : ∀ {s p q} → 0Q ≤ s → p ≤ q → p * s ≤ q * s
*-mono-≤-nnʳ {s} {p} {q} 0≤s p≤q = ≤-resp (*-comm s p) (*-comm s q) (*-mono-≤-nn 0≤s p≤q)

*-cancel-<ʳ : ∀ {s p q} → 0Q < s → p * s < q * s → p < q
*-cancel-<ʳ {s} 0<s lt = P.*-cancelʳ-<-nonNeg s {{nonneg (<-≤ 0<s)}} lt

-- r ∈ (q/q′, 1) with r > 0
scale-down : ∀ {q q′} → 0Q ≤ q → q < q′ → Σ Q (λ r → 0Q < r × r < 1Q × q ≤ r * q′)
scale-down {q} {q′} 0≤q q<q′ with dense q<q′
... | q″ , q<q″ , q″<q′ with inv (≤-<-trans 0≤q q<q′)
... | t , ht = q″ * t , *-cancel-<ʳ 0<q′ lt1 , *-cancel-<ʳ 0<q′ lt2 , ≤-trans (<-≤ q<q″) (≤-≃ (≃-sym rq′))
  where
    0<q′ = ≤-<-trans 0≤q q<q′
    0<q″ = ≤-<-trans 0≤q q<q″
    rq′ : (q″ * t) * q′ ≃ q″
    rq′ = ≃-trans (*-assoc q″ t q′) (≃-trans (*-cong (≃-refl {q″}) ht) (P.*-identityʳ q″))
    lt1 : 0Q * q′ < (q″ * t) * q′
    lt1 = ≃-<ʳ (≃-sym rq′) (≃-<ˡ (≃-sym (*-zeroˡ q′)) 0<q″)
    lt2 : (q″ * t) * q′ < 1Q * q′
    lt2 = ≃-<ˡ (≃-sym rq′) (≃-<ʳ (≃-sym (*-identityˡ q′)) q″<q′)

≤-or-> : ∀ p q → p ≤ q ⊎ q < p
≤-or-> p q with P.<-cmp p q
... | tri< a _ _ = inj₁ (<-≤ a)
... | tri≈ _ b _ = inj₁ (≤-≃ b)
... | tri> _ _ c = inj₂ c

-- adding a positive number
lt-add : ∀ {s ε} → 0Q < ε → s < s + ε
lt-add {s} {ε} 0<ε = ≃-<ˡ (+-identityʳ s) (+-mono-≤-< (≤-refl {s}) 0<ε)

-- differences
pos-diff : ∀ {p q} → p < q → 0Q < q + - p
pos-diff {p} {q} p<q = ≃-<ˡ (+-inverseʳ p) (+-mono-<-≤ p<q (≤-refl {(- p)}))

neg-pos : ∀ {q} → q < 0Q → 0Q < 0Q + - q
neg-pos {q} q<0 = ≃-<ˡ (+-inverseʳ q) (+-mono-<-≤ q<0 (≤-refl {(- q)}))

-- ring identities
ring₁ : ∀ r q → r + (q + (0Q + - q)) ≃ r
ring₁ = solve 2 (λ r q → r :+ (q :+ (con 0Q :+ :- q)) := r) ≃-refl

ring₂ : ∀ r q δ ε → r + ((q + δ) + (ε + - δ)) ≃ r + (q + ε)
ring₂ = solve 4 (λ r q δ ε → r :+ ((q :+ δ) :+ (ε :+ :- δ)) := r :+ (q :+ ε)) ≃-refl

ring₃ : ∀ r δ q u → (r + δ) + ((q + - r) + ((u + - q) + - δ)) ≃ u
ring₃ = solve 4 (λ r δ q u → (r :+ δ) :+ ((q :+ :- r) :+ ((u :+ :- q) :+ :- δ)) := u) ≃-refl

ring₄ : ∀ r q q′ → q ≃ (r + q′) + (- (r + (q′ + - q)))
ring₄ = solve 3 (λ r q q′ → q := (r :+ q′) :+ :- (r :+ (q′ :+ :- q))) ≃-refl

ring₅ : ∀ a s → ((a + s) + - a) ≃ s
ring₅ = solve 2 (λ a s → (a :+ s) :+ :- a := s) ≃-refl

ring₆ : ∀ x → (0Q + - x) + (x + x) ≃ x
ring₆ = solve 1 (λ x → (con 0Q :+ :- x) :+ (x :+ x) := x) ≃-refl

ring₇ : ∀ b n ε → b + (n + ε) ≃ (b + n) + ε
ring₇ = solve 3 (λ b n ε → b :+ (n :+ ε) := (b :+ n) :+ ε) ≃-refl
