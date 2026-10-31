{-# OPTIONS --safe --without-K #-}

-- The extended non-negative reals [0, ∞] as lower cuts of the rationals: a value is the set of
-- rationals strictly below it (so it contains every negative rational).  Order is inclusion;
-- suprema of chains are unions.  Compare the lower reals of Vickers / Jones–Plotkin valuations.
module QBS.Analysis.LowerReals where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import QBS.Analysis.RationalLemmas

record Cut : Set₁ where
  field
    mem : ℚᵘ → Set
    down : ∀ {p q} → q ≤ p → mem p → mem q
    open′ : ∀ {p} → mem p → Σ ℚᵘ (λ q → p < q × mem q)
    neg : ∀ {p} → p < 0ℚᵘ → mem p
open Cut

infix 4 _⊑_ _≋_
record _⊑_ (x y : Cut) : Set₁ where
  constructor mk⊑
  field ap : ∀ q → mem x q → mem y q
open _⊑_

_≋_ : Cut → Cut → Set₁
x ≋ y = x ⊑ y × y ⊑ x

⊑-refl : ∀ {x} → x ⊑ x
⊑-refl = mk⊑ (λ _ m → m)

⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
⊑-trans p q = mk⊑ (λ r m → ap q r (ap p r m))

≋-refl : ∀ {x} → x ≋ x
≋-refl = ⊑-refl , ⊑-refl

≋-sym : ∀ {x y} → x ≋ y → y ≋ x
≋-sym (p , q) = q , p

≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
≋-trans (p , q) (p′ , q′) = ⊑-trans p p′ , ⊑-trans q′ q

⊑-≋ : ∀ {x y} → x ≋ y → x ⊑ y
⊑-≋ = proj₁

----------------------------------------------------------------------------
-- constants

zeroC oneC infC : Cut
zeroC = record
  { mem = _< 0ℚᵘ
  ; down = λ le lt → ≤-<-trans le lt
  ; open′ = λ lt → dense lt
  ; neg = λ lt → lt }
oneC = record
  { mem = _< 1ℚᵘ
  ; down = λ le lt → ≤-<-trans le lt
  ; open′ = λ lt → dense lt
  ; neg = λ lt → <-trans lt 0<1 }
infC = record
  { mem = λ _ → ⊤
  ; down = λ _ _ → tt
  ; open′ = λ {p} _ → p + 1ℚᵘ , ≃-<ˡ (+-identityʳ p) (+-mono-≤-< (≤-refl {p}) 0<1) , tt
  ; neg = λ _ → tt }

----------------------------------------------------------------------------
-- addition and multiplication

infixl 6 _⊕_
infixl 7 _⊗_

_⊕_ : Cut → Cut → Cut
x ⊕ y = record
  { mem = λ q → Σ ℚᵘ (λ r → Σ ℚᵘ (λ s → mem x r × mem y s × q ≤ r + s))
  ; down = λ le (r , s , mr , ms , h) → r , s , mr , ms , ≤-trans le h
  ; open′ = λ (r , s , mr , ms , h) →
      let r′ , r<r′ , mr′ = open′ x mr
      in r′ + s , ≤-<-trans h (+-mono-<-≤ r<r′ (≤-refl {s})) , r′ , s , mr′ , ms , ≤-refl
  ; neg = λ lt → let a , b , a<0 , b<0 , h = split-neg lt in a , b , neg x a<0 , neg y b<0 , h }

_⊗_ : Cut → Cut → Cut
x ⊗ y = record
  { mem = λ q → q < 0ℚᵘ ⊎ Σ ℚᵘ (λ r → Σ ℚᵘ (λ s → 0ℚᵘ < r × 0ℚᵘ < s × mem x r × mem y s × q ≤ r * s))
  ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt)
             ; le (inj₂ (r , s , p , p′ , mr , ms , h)) → inj₂ (r , s , p , p′ , mr , ms , ≤-trans le h) }
  ; open′ = λ { (inj₁ lt) → let r , q<r , r<0 = dense lt in r , q<r , inj₁ r<0
              ; (inj₂ (r , s , 0<r , 0<s , mr , ms , h)) →
                  let r′ , r<r′ , mr′ = open′ x mr
                  in r′ * s , ≤-<-trans h (*-mono-<-posʳ 0<s r<r′)
                     , inj₂ (r′ , s , <-trans 0<r r<r′ , 0<s , mr′ , ms , ≤-refl) }
  ; neg = λ lt → inj₁ lt }

----------------------------------------------------------------------------
-- monotonicity

⊕-mono : ∀ {x x′ y y′} → x ⊑ x′ → y ⊑ y′ → x ⊕ y ⊑ x′ ⊕ y′
⊕-mono f g = mk⊑ (λ q (r , s , mr , ms , h) → r , s , ap f r mr , ap g s ms , h)

⊗-mono : ∀ {x x′ y y′} → x ⊑ x′ → y ⊑ y′ → x ⊗ y ⊑ x′ ⊗ y′
⊗-mono f g = mk⊑ (λ { q (inj₁ lt) → inj₁ lt
  ; q (inj₂ (r , s , p , p′ , mr , ms , h)) → inj₂ (r , s , p , p′ , ap f r mr , ap g s ms , h) })

⊕-cong : ∀ {x x′ y y′} → x ≋ x′ → y ≋ y′ → x ⊕ y ≋ x′ ⊕ y′
⊕-cong (f , f′) (g , g′) = ⊕-mono f g , ⊕-mono f′ g′

⊗-cong : ∀ {x x′ y y′} → x ≋ x′ → y ≋ y′ → x ⊗ y ≋ x′ ⊗ y′
⊗-cong (f , f′) (g , g′) = ⊗-mono f g , ⊗-mono f′ g′

----------------------------------------------------------------------------
-- addition laws

⊕-comm⊑ : ∀ x y → x ⊕ y ⊑ y ⊕ x
⊕-comm⊑ x y = mk⊑ (λ q (r , s , mr , ms , h) → s , r , ms , mr , ≤-trans h (≤-≃ (+-comm r s)))

⊕-comm : ∀ x y → x ⊕ y ≋ y ⊕ x
⊕-comm x y = ⊕-comm⊑ x y , ⊕-comm⊑ y x

⊕-assoc⊑ : ∀ x y z → (x ⊕ y) ⊕ z ⊑ x ⊕ (y ⊕ z)
⊕-assoc⊑ x y z = mk⊑ (λ q (u , t , (r , s , mr , ms , hu) , mt , h) →
  r , s + t , mr , (s , t , ms , mt , ≤-refl) ,
  ≤-trans h (≤-trans (+-mono-≤ hu (≤-refl {t})) (≤-≃ (+-assoc r s t))))

⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ≋ x ⊕ (y ⊕ z)
⊕-assoc x y z = ⊕-assoc⊑ x y z , back
  where
    back : x ⊕ (y ⊕ z) ⊑ (x ⊕ y) ⊕ z
    back = mk⊑ (λ q (r , u , mr , (s , t , ms , mt , hu) , h) →
      r + s , t , (r , s , mr , ms , ≤-refl) , mt ,
      ≤-trans h (≤-trans (+-mono-≤ (≤-refl {r}) hu) (≤-≃ (≃-sym (+-assoc r s t)))))

-- the summands are below the sum
⊕-inl : ∀ x y → x ⊑ x ⊕ y
⊕-inl x y = mk⊑ (λ q mq →
  let q′ , q<q′ , mq′ = open′ x mq
  in q′ , q + - q′ , mq′ , neg y (neg-diff q<q′) , ≤-≃ (≃-sym (≃-trans (+-comm q′ (q + - q′)) (sub-add q q′))))

⊕-inr : ∀ x y → y ⊑ x ⊕ y
⊕-inr x y = ⊑-trans (⊕-inl y x) (⊑-≋ (⊕-comm y x))

⊕-identityˡ : ∀ x → zeroC ⊕ x ≋ x
⊕-identityˡ x = fwd , ⊕-inr zeroC x
  where
    fwd : zeroC ⊕ x ⊑ x
    fwd = mk⊑ (λ q (r , s , r<0 , ms , h) →
      down x (<-≤ (≤-<-trans h (≃-<ʳ (+-identityˡ s) (+-mono-<-≤ r<0 (≤-refl {s}))))) ms)

----------------------------------------------------------------------------
-- multiplication laws

⊗-comm⊑ : ∀ x y → x ⊗ y ⊑ y ⊗ x
⊗-comm⊑ x y = mk⊑ (λ { q (inj₁ lt) → inj₁ lt
  ; q (inj₂ (r , s , p , p′ , mr , ms , h)) → inj₂ (s , r , p′ , p , ms , mr , ≤-trans h (≤-≃ (*-comm r s))) })

⊗-comm : ∀ x y → x ⊗ y ≋ y ⊗ x
⊗-comm x y = ⊗-comm⊑ x y , ⊗-comm⊑ y x

⊗-zeroˡ : ∀ x → zeroC ⊗ x ≋ zeroC
⊗-zeroˡ x = mk⊑ fwd , mk⊑ (λ q lt → inj₁ lt)
  where
    fwd : ∀ q → mem (zeroC ⊗ x) q → q < 0ℚᵘ
    fwd q (inj₁ lt) = lt
    fwd q (inj₂ (r , s , 0<r , 0<s , r<0 , ms , h)) = ⊥-elim (<-irrefl ≃-refl (<-trans r<0 0<r))

⊗-assoc⊑ : ∀ x y z → (x ⊗ y) ⊗ z ⊑ x ⊗ (y ⊗ z)
⊗-assoc⊑ x y z = mk⊑ (λ { q (inj₁ lt) → inj₁ lt
  ; q (inj₂ (u , t , 0<u , 0<t , inj₁ u<0 , mt , h)) → ⊥-elim (<-irrefl ≃-refl (<-trans u<0 0<u))
  ; q (inj₂ (u , t , 0<u , 0<t , inj₂ (r , s , 0<r , 0<s , mr , ms , hu) , mt , h)) →
      inj₂ (r , s * t , 0<r , *-pos 0<s 0<t , mr , inj₂ (s , t , 0<s , 0<t , ms , mt , ≤-refl) ,
        ≤-trans h (≤-trans (*-mono-≤-nnʳ (<-≤ 0<t) hu) (≤-≃ (*-assoc r s t)))) })

⊗-assoc : ∀ x y z → (x ⊗ y) ⊗ z ≋ x ⊗ (y ⊗ z)
⊗-assoc x y z = ⊗-assoc⊑ x y z ,
  ⊑-trans (proj₁ (⊗-comm x (y ⊗ z))) (⊑-trans (proj₁ (⊗-cong (⊗-comm y z) ≋-refl))
    (⊑-trans (⊗-assoc⊑ z y x) (⊑-trans (proj₁ (⊗-comm z (y ⊗ x))) (proj₁ (⊗-cong (⊗-comm y x) ≋-refl)))))

⊗-identityˡ : ∀ x → oneC ⊗ x ≋ x
⊗-identityˡ x = mk⊑ fwd , mk⊑ bwd
  where
    fwd : ∀ q → mem (oneC ⊗ x) q → mem x q
    fwd q (inj₁ lt) = neg x lt
    fwd q (inj₂ (r , s , 0<r , 0<s , r<1 , ms , h)) =
      down x (≤-trans h (≤-trans (*-mono-≤-nnʳ (<-≤ 0<s) (<-≤ r<1)) (≤-≃ (*-identityˡ s)))) ms
    bwd : ∀ q → mem x q → mem (oneC ⊗ x) q
    bwd q mq with neg-or-nonneg q
    ... | inj₁ lt = inj₁ lt
    ... | inj₂ 0≤q =
      let q′ , q<q′ , mq′ = open′ x mq
          r , 0<r , r<1 , h = scale-down 0≤q q<q′
      in inj₂ (r , q′ , 0<r , ≤-<-trans 0≤q q<q′ , r<1 , mq′ , h)

-- a witness slightly above, for strict inequalities
slack : ∀ x y {q r w} → mem x r → 0ℚᵘ < r → mem y w → 0ℚᵘ < w → q ≤ r * w →
  Σ ℚᵘ (λ b → mem (x ⊗ y) b × q < b)
slack x y {q} {r} {w} mr 0<r mw 0<w h =
  let w′ , w<w′ , mw′ = open′ y mw
  in r * w′ , inj₂ (r , w′ , 0<r , <-trans 0<w w<w′ , mr , mw′ , ≤-refl) , ≤-<-trans h (*-mono-<-pos 0<r w<w′)

⊗-distrib-fwd : ∀ x y z q → mem (x ⊗ (y ⊕ z)) q → mem ((x ⊗ y) ⊕ (x ⊗ z)) q
⊗-distrib-fwd x y z q (inj₁ lt) = let a , b , a<0 , b<0 , h = split-neg lt in a , b , inj₁ a<0 , inj₁ b<0 , h
⊗-distrib-fwd x y z q (inj₂ (r , w , 0<r , 0<w , mr , (s₁ , s₂ , m₁ , m₂ , hw) , h)) with pos-or-nonpos s₁ | pos-or-nonpos s₂
... | inj₁ 0<s₁ | inj₁ 0<s₂ =
  r * s₁ , r * s₂ , inj₂ (r , s₁ , 0<r , 0<s₁ , mr , m₁ , ≤-refl) , inj₂ (r , s₂ , 0<r , 0<s₂ , mr , m₂ , ≤-refl) ,
  ≤-trans h (≤-trans (*-mono-≤-nn (<-≤ 0<r) hw) (≤-≃ (*-distribˡ-+ r s₁ s₂)))
... | inj₁ 0<s₁ | inj₂ s₂≤0 =
  let w≤s₁ = ≤-trans hw (≤-trans (+-mono-≤ (≤-refl {s₁}) s₂≤0) (≤-≃ (+-identityʳ s₁)))
      b , mb , q<b = slack x y mr 0<r (down y w≤s₁ m₁) 0<w h
  in b , q + - b , mb , inj₁ (neg-diff q<b) , ≤-≃ (≃-sym (add-sub b q))
... | inj₂ s₁≤0 | inj₁ 0<s₂ =
  let w≤s₂ = ≤-trans hw (≤-trans (+-mono-≤ s₁≤0 (≤-refl {s₂})) (≤-≃ (+-identityˡ s₂)))
      b , mb , q<b = slack x z mr 0<r (down z w≤s₂ m₂) 0<w h
  in q + - b , b , inj₁ (neg-diff q<b) , mb , ≤-≃ (≃-sym (sub-add q b))
... | inj₂ s₁≤0 | inj₂ s₂≤0 =
  ⊥-elim (<-irrefl ≃-refl (<-≤-trans 0<w (≤-trans hw (≤-trans (+-mono-≤ s₁≤0 s₂≤0) (≤-≃ (+-identityˡ 0ℚᵘ))))))

-- two positive products r₁ s₁ and r₂ s₂ are dominated by a single r ≥ r₁, r₂: a + b ≤ r (s₁ + s₂)
both-r : ∀ x y z {q a b r r₁ r₂ s₁ s₂} → mem x r → 0ℚᵘ < r → r₁ ≤ r → r₂ ≤ r → 0ℚᵘ < s₁ → 0ℚᵘ < s₂ →
  mem y s₁ → mem z s₂ → a ≤ r₁ * s₁ → b ≤ r₂ * s₂ → q ≤ a + b → mem (x ⊗ (y ⊕ z)) q
both-r x y z {q} {a} {b} {r} {r₁} {r₂} {s₁} {s₂} mr 0<r le₁ le₂ 0<s₁ 0<s₂ m₁ m₂ ha hb h =
  inj₂ (r , s₁ + s₂ , 0<r , ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<s₁ 0<s₂) , mr , (s₁ , s₂ , m₁ , m₂ , ≤-refl) ,
    ≤-trans h (≤-trans (+-mono-≤ ha hb) (≤-trans (+-mono-≤ (*-mono-≤-nnʳ (<-≤ 0<s₁) le₁) (*-mono-≤-nnʳ (<-≤ 0<s₂) le₂))
      (≤-≃ (≃-sym (*-distribˡ-+ r s₁ s₂))))))

⊗-distrib-bwd : ∀ x y z q → mem ((x ⊗ y) ⊕ (x ⊗ z)) q → mem (x ⊗ (y ⊕ z)) q
⊗-distrib-bwd x y z q (a , b , inj₁ a<0 , inj₁ b<0 , h) =
  inj₁ (≤-<-trans h (≃-<ʳ (+-identityˡ 0ℚᵘ) (+-mono-< a<0 b<0)))
⊗-distrib-bwd x y z q (a , b , inj₁ a<0 , inj₂ (r , s , 0<r , 0<s , mr , ms , hb) , h) =
  inj₂ (r , s , 0<r , 0<s , mr , ap (⊕-inr y z) s ms ,
    <-≤ (<-≤-trans (≤-<-trans h (≃-<ʳ (+-identityˡ b) (+-mono-<-≤ a<0 (≤-refl {b})))) hb))
⊗-distrib-bwd x y z q (a , b , inj₂ (r , s , 0<r , 0<s , mr , ms , ha) , inj₁ b<0 , h) =
  inj₂ (r , s , 0<r , 0<s , mr , ap (⊕-inl y z) s ms ,
    <-≤ (<-≤-trans (≤-<-trans h (≃-<ʳ (+-identityʳ a) (+-mono-≤-< (≤-refl {a}) b<0))) ha))
⊗-distrib-bwd x y z q (a , b , inj₂ (r₁ , s₁ , 0<r₁ , 0<s₁ , mr₁ , m₁ , ha) , inj₂ (r₂ , s₂ , 0<r₂ , 0<s₂ , mr₂ , m₂ , hb) , h)
  with total r₁ r₂
... | inj₁ le = both-r x y z {q} {a} {b} {r₂} {r₁} {r₂} {s₁} {s₂} mr₂ 0<r₂ le ≤-refl 0<s₁ 0<s₂ m₁ m₂ ha hb h
... | inj₂ le = both-r x y z {q} {a} {b} {r₁} {r₁} {r₂} {s₁} {s₂} mr₁ 0<r₁ ≤-refl le 0<s₁ 0<s₂ m₁ m₂ ha hb h

⊗-distribˡ : ∀ x y z → x ⊗ (y ⊕ z) ≋ (x ⊗ y) ⊕ (x ⊗ z)
⊗-distribˡ x y z = mk⊑ (⊗-distrib-fwd x y z) , mk⊑ (⊗-distrib-bwd x y z)

⊗-distribʳ : ∀ x y z → (y ⊕ z) ⊗ x ≋ (y ⊗ x) ⊕ (z ⊗ x)
⊗-distribʳ x y z = ≋-trans (⊗-comm (y ⊕ z) x) (≋-trans (⊗-distribˡ x y z) (⊕-cong (⊗-comm x y) (⊗-comm x z)))

----------------------------------------------------------------------------
-- order and suprema

0-least : ∀ {x} → zeroC ⊑ x
0-least {x} = mk⊑ (λ q lt → neg x lt)

-- the union of a family of cuts
unionC : (ℕ → Cut) → Cut
unionC c = record
  { mem = λ q → Σ ℕ (λ n → mem (c n) q)
  ; down = λ le (n , m) → n , down (c n) le m
  ; open′ = λ (n , m) → let q′ , lt , m′ = open′ (c n) m in q′ , lt , n , m′
  ; neg = λ lt → zero , neg (c zero) lt }

union-ub : ∀ c n → c n ⊑ unionC c
union-ub c n = mk⊑ (λ q m → n , m)

union-lub : ∀ c {b} → (∀ n → c n ⊑ b) → unionC c ⊑ b
union-lub c le = mk⊑ (λ q (n , m) → ap (le n) q m)

⊕-union : ∀ a c → a ⊕ unionC c ≋ unionC (λ n → a ⊕ c n)
⊕-union a c = mk⊑ (λ q (r , s , mr , (n , ms) , h) → n , r , s , mr , ms , h)
  , mk⊑ (λ q (n , r , s , mr , ms , h) → r , s , mr , (n , ms) , h)

⊗-union : ∀ a c → a ⊗ unionC c ≋ unionC (λ n → a ⊗ c n)
⊗-union a c = mk⊑ fwd , mk⊑ bwd
  where
    fwd : ∀ q → mem (a ⊗ unionC c) q → mem (unionC (λ n → a ⊗ c n)) q
    fwd q (inj₁ lt) = zero , inj₁ lt
    fwd q (inj₂ (r , s , p , p′ , mr , (n , ms) , h)) = n , inj₂ (r , s , p , p′ , mr , ms , h)
    bwd : ∀ q → mem (unionC (λ n → a ⊗ c n)) q → mem (a ⊗ unionC c) q
    bwd q (n , inj₁ lt) = inj₁ lt
    bwd q (n , inj₂ (r , s , p , p′ , mr , ms , h)) = inj₂ (r , s , p , p′ , mr , (n , ms) , h)

----------------------------------------------------------------------------
-- classical part: subtraction below 1 and cancellation

open import Data.Rational.Unnormalised.Base using (_+_)
open import QBS.Classical using (LEM₀)

module Classical (lem : LEM₀) where

  -- a bounded cut has an element within ε of its supremum
  near-sup : ∀ c {ε} → c ⊑ oneC → 0ℚᵘ < ε →
    Σ ℚᵘ (λ r → mem c r × (∀ r′ → mem c r′ → r′ ≤ r + ε))
  near-sup c {ε} bd 0<ε with lem (Σ ℚᵘ (λ r → mem c r × (∀ r′ → mem c r′ → r′ ≤ r + ε)))
  ... | inj₁ yes = yes
  ... | inj₂ no = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (ap bd rk mrk) final))
    where
      b₀ : ℚᵘ
      b₀ = 0ℚᵘ + - 1ℚᵘ

      b₀<0 : b₀ < 0ℚᵘ
      b₀<0 = neg-diff 0<1

      step : ∀ r → mem c r → Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′)
      step r mr with lem (Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′))
      ... | inj₁ yes = yes
      ... | inj₂ none = ⊥-elim (no (r , mr , λ r′ m′ → help r′ m′ (≤-or-> r′ (r + ε))))
        where
          help : ∀ r′ → mem c r′ → r′ ≤ r + ε ⊎ r + ε < r′ → r′ ≤ r + ε
          help r′ m′ (inj₁ le) = le
          help r′ m′ (inj₂ lt) = ⊥-elim (none (r′ , m′ , lt))

      iter : ∀ n → Σ ℚᵘ (λ r → mem c r × b₀ + nat n * ε ≤ r)
      iter zero = b₀ , neg c b₀<0 ,
        ≤-≃ (≃-trans (+-cong (≃-refl {b₀}) (*-zeroˡ ε)) (+-identityʳ b₀))
      iter (suc n) with iter n
      ... | r , mr , h with step r mr
      ... | r′ , mr′ , lt = r′ , mr′ ,
        ≤-trans (≤-≃ (≃-trans (+-cong (≃-refl {b₀}) (nat-suc* n ε)) (ring₇ b₀ (nat n * ε) ε)))
          (<-≤ (≤-<-trans (+-mono-≤ h (≤-refl {ε})) lt))

      k = proj₁ (arch (1ℚᵘ + 1ℚᵘ) 0<ε)
      hk = proj₂ (arch (1ℚᵘ + 1ℚᵘ) 0<ε)

      rk = proj₁ (iter k)
      mrk = proj₁ (proj₂ (iter k))
      hrk = proj₂ (proj₂ (iter k))

      final : 1ℚᵘ ≤ rk
      final = ≤-trans (≤-≃ (≃-sym (ring₆ 1ℚᵘ))) (≤-trans (+-mono-≤ (≤-refl {b₀}) hk) hrk)

  -- the complement 1 − c of a cut below 1
  complC : ∀ c → c ⊑ oneC → Cut
  complC c bd = record
    { mem = λ q → Σ ℚᵘ (λ ε → 0ℚᵘ < ε × (∀ r → mem c r → r + (q + ε) ≤ 1ℚᵘ))
    ; down = λ le (ε , 0<ε , h) →
        ε , 0<ε , (λ r m → ≤-trans (+-mono-≤ (≤-refl {r}) (+-mono-≤ le (≤-refl {ε}))) (h r m))
    ; open′ = λ {q} (ε , 0<ε , h) →
        let δ , 0<δ , δ<ε = dense 0<ε
        in q + δ , lt-add 0<δ , ε + - δ , pos-diff δ<ε , (λ r m → ≤-trans (≤-≃ (ring₂ r q δ ε)) (h r m))
    ; neg = λ {q} q<0 →
        0ℚᵘ + - q , neg-pos q<0 , (λ r m → ≤-trans (≤-≃ (ring₁ r q)) (<-≤ (ap bd r m))) }

  complement-ok : ∀ c (bd : c ⊑ oneC) → c ⊕ complC c bd ≋ oneC
  complement-ok c bd = mk⊑ fwd , mk⊑ bwd
    where
      fwd : ∀ q → mem (c ⊕ complC c bd) q → q < 1ℚᵘ
      fwd q (r , s , mr , (ε , 0<ε , h) , le) =
        ≤-<-trans le (<-≤-trans (+-mono-≤-< (≤-refl {r}) (lt-add 0<ε)) (h r mr))
      bwd : ∀ q → q < 1ℚᵘ → mem (c ⊕ complC c bd) q
      bwd q q<1 =
        let η = 1ℚᵘ + - q
            δ , 0<δ , δ<η = dense (pos-diff q<1)
            r , mr , hr = near-sup c bd 0<δ
        in r , q + - r , mr ,
           (η + - δ , pos-diff δ<η , λ r′ m′ → ≤-trans (+-mono-≤ (hr r′ m′) (≤-refl {(q + - r) + (η + - δ)}))
               (≤-≃ (ring₃ r δ q 1ℚᵘ))) ,
           ≤-≃ (≃-sym (add-sub r q))

  cancel-⊑ : ∀ {a x y} → a ⊑ oneC → a ⊕ x ⊑ a ⊕ y → x ⊑ y
  cancel-⊑ {a} {x} {y} bd f = mk⊑ (λ q mq →
    let q′ , q<q′ , mq′ = open′ x mq
        δ = q′ + - q
        r , mr , hr = near-sup a bd (pos-diff q<q′)
        r″ , s , mr″ , ms , h = ap f (r + q′) (r , q′ , mr , mq′ , ≤-refl)
        le₁ : r + q′ ≤ (r + δ) + s
        le₁ = ≤-trans h (+-mono-≤ (hr r″ mr″) (≤-refl {s}))
        q≤s : q ≤ s
        q≤s = ≤-trans (≤-≃ (ring₄ r q q′))
                (≤-trans (+-mono-≤ le₁ (≤-refl {(- (r + δ))})) (≤-≃ (ring₅ (r + δ) s)))
    in down y q≤s ms)

  cancel : ∀ {a x y} → a ⊑ oneC → a ⊕ x ≋ a ⊕ y → x ≋ y
  cancel bd (f , g) = cancel-⊑ bd f , cancel-⊑ bd g

----------------------------------------------------------------------------
-- the instance

import Level as L
open import Algebra.Bundles using (CommutativeSemiring)
open import Algebra.Structures {A = Cut} _≋_
import Algebra.Structures.Biased {A = Cut} _≋_ as Bi
open import Relation.Binary.Structures using (IsEquivalence)
open import QBS.Analysis.Omega using (OmegaSemiring)

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = record { refl = ≋-refl ; sym = ≋-sym ; trans = ≋-trans }

cutSemiring : CommutativeSemiring (L.suc L.zero) (L.suc L.zero)
cutSemiring = record
  { Carrier = Cut ; _≈_ = _≋_ ; _+_ = _⊕_ ; _*_ = _⊗_ ; 0# = zeroC ; 1# = oneC
  ; isCommutativeSemiring = Bi.isCommutativeSemiringˡ record
      { +-isCommutativeMonoid = Bi.isCommutativeMonoidˡ record
          { isSemigroup = record { isMagma = record { isEquivalence = ≋-isEquivalence ; ∙-cong = ⊕-cong } ; assoc = ⊕-assoc }
          ; identityˡ = ⊕-identityˡ ; comm = ⊕-comm }
      ; *-isCommutativeMonoid = Bi.isCommutativeMonoidˡ record
          { isSemigroup = record { isMagma = record { isEquivalence = ≋-isEquivalence ; ∙-cong = ⊗-cong } ; assoc = ⊗-assoc }
          ; identityˡ = ⊗-identityˡ ; comm = ⊗-comm }
      ; distribʳ = ⊗-distribʳ
      ; zeroˡ = ⊗-zeroˡ }
  }

LowerRealsOmega : LEM₀ → OmegaSemiring (L.suc L.zero)
LowerRealsOmega lem = record
  { ordered = record
        { commutativeSemiring = cutSemiring
      ; _≤_ = _⊑_
      ; ≤-reflexive = proj₁
      ; ≤-trans = ⊑-trans
      ; ≤-antisym = _,_
      ; 0-least = 0-least
      ; ≤-+ʳ = λ {a} {b} → ⊕-inl a b
      ; +-mono = ⊕-mono
      ; *-mono = λ c → ⊗-mono ⊑-refl
      ; complement = λ {c} h → complC c h , complement-ok c h
        }
  ; ⨆ = λ c _ → unionC c
  ; ⨆-ub = λ c _ n → union-ub c n
  ; ⨆-lub = λ c _ le → union-lub c le
  ; +-⨆ = λ a c _ _ → ⊕-union a c
  ; *-⨆ = λ a c _ _ → ⊗-union a c
  ; cancel = cancel
  }
  where open Classical lem
