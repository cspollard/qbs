{-# OPTIONS --safe --without-K #-}

-- Ordered-field facts about the unnormalised rationals in the form used for lower cuts: plain
-- statements without instance arguments, plus the Archimedean property.  Unnormalised rationals
-- keep arithmetic computational; equality is ≃ and the order respects it.
module QBS.Analysis.RationalLemmas where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤ
open import Data.Rational.Unnormalised.Base public using (ℚᵘ; 0ℚᵘ; 1ℚᵘ; ½)
open import Data.Rational.Unnormalised.Base using
  (mkℚᵘ; _+_; _*_; -_; 1/_; _<_; _≤_; _≃_; *≡*; *≤*; *<*; ↥_; ↧_; ↧ₙ_; Positive; NonNegative; positive; nonNegative)
import Data.Rational.Unnormalised.Properties as P
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl; cong; subst)

infix 4 _≤ᵘ_ _<ᵘ_ _≃ᵘ_
_≤ᵘ_ _<ᵘ_ _≃ᵘ_ : ℚᵘ → ℚᵘ → Set
_≤ᵘ_ = _≤_
_<ᵘ_ = _<_
_≃ᵘ_ = _≃_

-- stdlib's lemmas, under this module's names
open P public using
  ( ≃-refl; ≃-sym; ≃-trans; ≤-refl; ≤-trans; ≤-antisym; <-trans; ≤-<-trans; <-≤-trans; <-irrefl )
  renaming ( ≤-reflexive to ≤-≃; <-dense to dense; <⇒≤ to <-≤; <-respʳ-≃ to ≃-<ʳ; <-respˡ-≃ to ≃-<ˡ
           ; ≤-total to total; ≰⇒> to not-≤⇒< )

≤-resp : ∀ {p p′ q q′} → p ≃ p′ → q ≃ q′ → p ≤ q → p′ ≤ q′
≤-resp e e′ le = ≤-trans (≤-≃ (≃-sym e)) (≤-trans le (≤-≃ e′))

open P public using
  ( +-cong; *-cong; +-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseʳ; *-comm; *-assoc; *-identityˡ; *-zeroˡ
  ; *-distribˡ-+; *-distribʳ-+; +-mono-≤; +-mono-<-≤; +-mono-≤-<; +-mono-< )

-- positivity
pos : ∀ {p} → 0ℚᵘ < p → Positive p
pos = positive
nonneg : ∀ {p} → 0ℚᵘ ≤ p → NonNegative p
nonneg = nonNegative

*-mono-<-pos : ∀ {r p q} → 0ℚᵘ < r → p < q → r * p < r * q
*-mono-<-pos {r} 0<r p<q = P.*-monoʳ-<-pos r {{pos 0<r}} p<q
*-mono-≤-nn : ∀ {r p q} → 0ℚᵘ ≤ r → p ≤ q → r * p ≤ r * q
*-mono-≤-nn {r} 0≤r p≤q = P.*-monoʳ-≤-nonNeg r {{nonneg 0≤r}} p≤q
*-pos : ∀ {p q} → 0ℚᵘ < p → 0ℚᵘ < q → 0ℚᵘ < p * q
*-pos {p} {q} 0<p 0<q = P.positive⁻¹ (p * q) {{P.pos*pos⇒pos p {{pos 0<p}} q {{pos 0<q}}}}

-- division by a positive number
inv : ∀ {s} → 0ℚᵘ < s → Σ ℚᵘ (λ t → t * s ≃ 1ℚᵘ)
inv {s} 0<s = (1/_ s {{P.pos⇒nonZero s {{pos 0<s}}}}) , P.*-inverseˡ s {{P.pos⇒nonZero s {{pos 0<s}}}}

----------------------------------------------------------------------------
-- natural numbers and the Archimedean property

nat : ℕ → ℚᵘ
nat k = mkℚᵘ (+ k) 0

nat-suc : ∀ k → nat (suc k) ≃ nat k + 1ℚᵘ
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
  (≃-trans (*-distribʳ-+ ε (nat k) 1ℚᵘ) (+-cong (≃-refl {nat k * ε}) (*-identityˡ ε)))

arch : ∀ p {ε} → 0ℚᵘ < ε → Σ ℕ (λ k → p ≤ nat k * ε)
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
pos-or-nonpos : ∀ s → 0ℚᵘ < s ⊎ s ≤ 0ℚᵘ
pos-or-nonpos s with P.<-cmp 0ℚᵘ s
... | tri< a _ _ = inj₁ a
... | tri≈ _ b _ = inj₂ (≤-≃ (≃-sym b))
... | tri> _ _ c = inj₂ (<-≤ c)

neg-or-nonneg : ∀ s → s < 0ℚᵘ ⊎ 0ℚᵘ ≤ s
neg-or-nonneg s with P.<-cmp s 0ℚᵘ
... | tri< a _ _ = inj₁ a
... | tri≈ _ b _ = inj₂ (≤-≃ (≃-sym b))
... | tri> _ _ c = inj₂ (<-≤ c)

-- a negative number is a sum of two negatives
split-neg : ∀ {q} → q < 0ℚᵘ → Σ ℚᵘ (λ a → Σ ℚᵘ (λ b → a < 0ℚᵘ × b < 0ℚᵘ × q ≤ a + b))
split-neg {q} q<0 with dense q<0
... | a , q<a , a<0 = a , q + - a ,
  a<0 ,
  ≃-<ʳ (+-inverseʳ a) (+-mono-<-≤ q<a (≤-refl {(- a)})) ,
  ≤-≃ (≃-sym (≃-trans (+-comm a (q + - a)) (sub-add q a)))

-- q < q′ gives a negative difference
neg-diff : ∀ {q q′} → q < q′ → q + - q′ < 0ℚᵘ
neg-diff {q} {q′} q<q′ = ≃-<ʳ (+-inverseʳ q′) (+-mono-<-≤ q<q′ (≤-refl {(- q′)}))

0<1 : 0ℚᵘ < 1ℚᵘ
0<1 = P.positive⁻¹ 1ℚᵘ

-- sums of positives and of negatives (the stdlib's `pos+pos⇒pos`, with the adapter)
+-pos : ∀ {a b} → 0ℚᵘ < a → 0ℚᵘ < b → 0ℚᵘ < a + b
+-pos {a} {b} 0<a 0<b = P.positive⁻¹ (a + b) {{P.pos+pos⇒pos a {{pos 0<a}} b {{pos 0<b}}}}

+-neg : ∀ {a b} → a < 0ℚᵘ → b < 0ℚᵘ → a + b < 0ℚᵘ
+-neg a<0 b<0 = ≃-<ʳ (+-identityˡ 0ℚᵘ) (+-mono-< a<0 b<0)

≤-+ʳ : ∀ a b → 0ℚᵘ ≤ b → a ≤ a + b
≤-+ʳ a b 0≤b = P.p≤p+q a b {{nonneg 0≤b}}

½+½ : ½ + ½ ≃ 1ℚᵘ
½+½ = *≡* refl

0<½ : 0ℚᵘ < ½
0<½ = P.positive⁻¹ ½

-- `nat` is non-negative and monotone
nat-nonneg : ∀ k → 0ℚᵘ ≤ nat k
nat-nonneg zero = ≤-refl
nat-nonneg (suc k) = ≤-trans (nat-nonneg k) (≤-trans (≤-+ʳ (nat k) 1ℚᵘ (<-≤ 0<1)) (≤-≃ (≃-sym (nat-suc k))))

nat-mono : ∀ {j k} → j ℕ.≤ k → nat j ≤ nat k
nat-mono {k = k} ℕ.z≤n = nat-nonneg k
nat-mono (ℕ.s≤s le) = ≤-resp (≃-sym (nat-suc _)) (≃-sym (nat-suc _)) (+-mono-≤ (nat-mono le) (≤-refl {1ℚᵘ}))

*-mono-<-posʳ : ∀ {s p q} → 0ℚᵘ < s → p < q → p * s < q * s
*-mono-<-posʳ {s} 0<s p<q = P.*-monoˡ-<-pos s {{pos 0<s}} p<q

*-mono-≤-nnʳ : ∀ {s p q} → 0ℚᵘ ≤ s → p ≤ q → p * s ≤ q * s
*-mono-≤-nnʳ {s} 0≤s p≤q = P.*-monoˡ-≤-nonNeg s {{nonneg 0≤s}} p≤q

*-cancel-<ʳ : ∀ {s p q} → 0ℚᵘ < s → p * s < q * s → p < q
*-cancel-<ʳ {s} 0<s lt = P.*-cancelʳ-<-nonNeg s {{nonneg (<-≤ 0<s)}} lt

-- r ∈ (q/q′, 1) with r > 0
scale-down : ∀ {q q′} → 0ℚᵘ ≤ q → q < q′ → Σ ℚᵘ (λ r → 0ℚᵘ < r × r < 1ℚᵘ × q ≤ r * q′)
scale-down {q} {q′} 0≤q q<q′ with dense q<q′
... | q″ , q<q″ , q″<q′ with inv (≤-<-trans 0≤q q<q′)
... | t , ht = q″ * t , *-cancel-<ʳ 0<q′ lt1 , *-cancel-<ʳ 0<q′ lt2 , ≤-trans (<-≤ q<q″) (≤-≃ (≃-sym rq′))
  where
    0<q′ = ≤-<-trans 0≤q q<q′
    0<q″ = ≤-<-trans 0≤q q<q″
    rq′ : (q″ * t) * q′ ≃ q″
    rq′ = ≃-trans (*-assoc q″ t q′) (≃-trans (*-cong (≃-refl {q″}) ht) (P.*-identityʳ q″))
    lt1 : 0ℚᵘ * q′ < (q″ * t) * q′
    lt1 = ≃-<ʳ (≃-sym rq′) (≃-<ˡ (≃-sym (*-zeroˡ q′)) 0<q″)
    lt2 : (q″ * t) * q′ < 1ℚᵘ * q′
    lt2 = ≃-<ˡ (≃-sym rq′) (≃-<ʳ (≃-sym (*-identityˡ q′)) q″<q′)

≤-or-> : ∀ p q → p ≤ q ⊎ q < p
≤-or-> p q with P.<-cmp p q
... | tri< a _ _ = inj₁ (<-≤ a)
... | tri≈ _ b _ = inj₁ (≤-≃ b)
... | tri> _ _ c = inj₂ c

-- adding a positive number
lt-add : ∀ {s ε} → 0ℚᵘ < ε → s < s + ε
lt-add {s} {ε} 0<ε = ≃-<ˡ (+-identityʳ s) (+-mono-≤-< (≤-refl {s}) 0<ε)

-- differences
pos-diff : ∀ {p q} → p < q → 0ℚᵘ < q + - p
pos-diff {p} {q} p<q = ≃-<ˡ (+-inverseʳ p) (+-mono-<-≤ p<q (≤-refl {(- p)}))

neg-pos : ∀ {q} → q < 0ℚᵘ → 0ℚᵘ < 0ℚᵘ + - q
neg-pos {q} q<0 = ≃-<ˡ (+-inverseʳ q) (+-mono-<-≤ q<0 (≤-refl {(- q)}))

-- ring identities
ring₁ : ∀ r q → r + (q + (0ℚᵘ + - q)) ≃ r
ring₁ = solve 2 (λ r q → r :+ (q :+ (con 0ℚᵘ :+ :- q)) := r) ≃-refl

ring₂ : ∀ r q δ ε → r + ((q + δ) + (ε + - δ)) ≃ r + (q + ε)
ring₂ = solve 4 (λ r q δ ε → r :+ ((q :+ δ) :+ (ε :+ :- δ)) := r :+ (q :+ ε)) ≃-refl

ring₃ : ∀ r δ q u → (r + δ) + ((q + - r) + ((u + - q) + - δ)) ≃ u
ring₃ = solve 4 (λ r δ q u → (r :+ δ) :+ ((q :+ :- r) :+ ((u :+ :- q) :+ :- δ)) := u) ≃-refl

ring₄ : ∀ r q q′ → q ≃ (r + q′) + (- (r + (q′ + - q)))
ring₄ = solve 3 (λ r q q′ → q := (r :+ q′) :+ :- (r :+ (q′ :+ :- q))) ≃-refl

ring₅ : ∀ a s → ((a + s) + - a) ≃ s
ring₅ = solve 2 (λ a s → (a :+ s) :+ :- a := s) ≃-refl

ring₆ : ∀ x → (0ℚᵘ + - x) + (x + x) ≃ x
ring₆ = solve 1 (λ x → (con 0ℚᵘ :+ :- x) :+ (x :+ x) := x) ≃-refl

ring₇ : ∀ b n ε → b + (n + ε) ≃ (b + n) + ε
ring₇ = solve 3 (λ b n ε → b :+ (n :+ ε) := (b :+ n) :+ ε) ≃-refl
