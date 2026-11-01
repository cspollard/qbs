{-# OPTIONS --safe --without-K #-}

-- The minimum of two lower cuts is their intersection: the `Min` structure on the extended
-- non-negative reals as lower cuts of the rationals.
module QBS.Analysis.LowerRealsMin where

open import Function.Base using (case_of_)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; -_; _<_; _≤_)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.Omega using (OmegaSemiring)
open import QBS.Analysis.LowerRealsArch using (qC; qC-add)
open import QBS.Analysis.Min
open import QBS.Classical using (LEM₀)

infixl 7 _⊓_

_⊓_ : Cut → Cut → Cut
x ⊓ y = record
  { mem = λ q → mem x q × mem y q
  ; down = λ le (mx , my) → down x le mx , down y le my
  ; open′ = λ (mx , my) →
      let q₁ , lt₁ , m₁ = open′ x mx
          q₂ , lt₂ , m₂ = open′ y my
      in case total q₁ q₂ of λ
         { (inj₁ le) → q₁ , lt₁ , (m₁ , down y le m₂)
         ; (inj₂ le) → q₂ , lt₂ , (down x le m₁ , m₂) }
  ; neg = λ lt → neg x lt , neg y lt
  }

-- a point q of x and c yields a decomposition of q into points of x ∩ c and (negative) points of y ∩ c
big : ∀ (x y c : Cut) {q} → mem x q → mem c q → mem ((x ⊓ c) ⊕ (y ⊓ c)) q
big x y c {q} mx mc =
  let a₁ , q<a₁ , ma₁ = open′ x mx
      c₁ , q<c₁ , mc₁ = open′ c mc
  in case total a₁ c₁ of λ
     { (inj₁ le) → pick a₁ q<a₁ (ma₁ , down c le mc₁)
     ; (inj₂ le) → pick c₁ q<c₁ (down x le ma₁ , mc₁) }
  where
    pick : ∀ w → q < w → mem (x ⊓ c) w → mem ((x ⊓ c) ⊕ (y ⊓ c)) q
    pick w q<w mw = w , q + - w , mw , (neg y n , neg c n) , ≤-≃ (≃-sym (add-sub w q))
      where n : q + - w < 0ℚᵘ
            n = neg-diff q<w

-- min (a + b, c) ≤ min (a, c) + min (b, c)
add-⊓ : ∀ a b c → ((a ⊕ b) ⊓ c) ⊑ ((a ⊓ c) ⊕ (b ⊓ c))
add-⊓ a b c = mk⊑ (λ q ((r , s , mr , ms , le) , mc) →
  case ≤-or-> q r of λ
  { (inj₁ q≤r) → big a b c (down a q≤r mr) mc
  ; (inj₂ r<q) → case ≤-or-> q s of λ
      { (inj₁ q≤s) → ap (⊕-comm⊑ (b ⊓ c) (a ⊓ c)) q (big b a c (down b q≤s ms) mc)
      ; (inj₂ s<q) → r , s , (mr , down c (<-≤ r<q) mc) , (ms , down c (<-≤ s<q) mc) , le } })

-- the powers of two as rationals and as cuts
ntwo : ℕ → ℚᵘ
ntwo zero = 1ℚᵘ
ntwo (suc k) = ntwo k + ntwo k

ntwo-pos : ∀ k → 0ℚᵘ < ntwo k
ntwo-pos zero = 0<1
ntwo-pos (suc k) = +-pos (ntwo-pos k) (ntwo-pos k)

ntwo-≥1 : ∀ k → 1ℚᵘ ≤ ntwo k
ntwo-≥1 zero = ≤-refl
ntwo-≥1 (suc k) = ≤-trans (ntwo-≥1 k) (≤-+ʳ (ntwo k) (ntwo k) (<-≤ (ntwo-pos k)))

nat-lt : ∀ k → nat k < ntwo k
nat-lt zero = 0<1
nat-lt (suc k) = ≃-<ˡ (≃-sym (nat-suc k))
  (<-≤-trans (+-mono-<-≤ (nat-lt k) (≤-refl {1ℚᵘ})) (+-mono-≤ (≤-refl {ntwo k}) (ntwo-≥1 k)))

ntwo-big : ∀ q → Σ ℕ (λ k → q < ntwo k)
ntwo-big q with nat-bound q
... | k , le = k , ≤-<-trans le (nat-lt k)

module _ (lem : LEM₀) where
  open Pow (LowerRealsOmega lem) using (pw)

  pw-qC : ∀ k → pw k ≋ qC (ntwo k) (ntwo-pos k)
  pw-qC zero = mk⊑ (λ s x → x) , mk⊑ (λ s x → x)
  pw-qC (suc k) = ≋-trans (⊕-cong (pw-qC k) (pw-qC k)) (qC-add (ntwo-pos k) (ntwo-pos k))

  min-sup : ∀ a (inc : OmegaSemiring.Increasing (LowerRealsOmega lem) (λ k → a ⊓ pw k)) →
    a ⊑ unionC (λ k → a ⊓ pw k)
  min-sup a inc = mk⊑ (λ q m →
    let k , lt = ntwo-big q in k , (m , ap (proj₂ (pw-qC k)) q lt))

lowerRealsMin : ∀ lem → Min (LowerRealsOmega lem)
lowerRealsMin lem = record
  { mn = _⊓_
  ; mn-≤l = mk⊑ (λ q m → proj₁ m)
  ; mn-≤r = mk⊑ (λ q m → proj₂ m)
  ; mn-glb = λ f g → mk⊑ (λ q m → ap f q m , ap g q m)
  ; mn-⨆ = λ c _ b _ → mk⊑ (λ q ((n , mc) , mb) → n , (mc , mb))
  ; mn-add = λ {a} {b} {c} → add-⊓ a b c
  ; mn-sup = min-sup lem
  }
