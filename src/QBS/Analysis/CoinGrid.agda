{-# OPTIONS --safe --without-K #-}

-- Dyadic grid approximations of a measurable function h : R → [0,1]: the simple function that
-- equals the largest grid point a·2⁻ᵏ strictly below h x (and 0 if h x ≤ 2⁻ᵏ).  It lies below h
-- and within 2⁻ᵏ of it.
module QBS.Analysis.CoinGrid where

import Level as L
open import Level using (lift; lower)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
import Relation.Binary.PropositionalEquality.Core as ≡
open ≡ using (_≡_)

open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import QBS.Analysis.RationalLemmas
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Borel.Core
open import QBS.Borel.Source using (R₁)
open import QBS.Borel.Measure using (Disjoint)
open import QBS.Borel.PiLambda using (∁)
open import QBS.Analysis.Omega
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsArch using (tp; tp-pos; nat-nonneg; ≤-+ʳ′)
open import QBS.Analysis.BorelMeasure
open import QBS.Analysis.CoinSimple
open import QBS.Analysis.LevelSets
open Cut
open _⊑_

----------------------------------------------------------------------------
-- rational constants as cuts

rC : Q → Cut
rC r = record
  { mem = λ s → s < r ⊎ s < 0Q
  ; down = λ { le (inj₁ lt) → inj₁ (≤-<-trans le lt) ; le (inj₂ lt) → inj₂ (≤-<-trans le lt) }
  ; open′ = λ { (inj₁ lt) → let t , a , b = dense lt in t , a , inj₁ b
              ; (inj₂ lt) → let t , a , b = dense lt in t , a , inj₂ b }
  ; neg = inj₂ }

rC-mono : ∀ {r r′} → r ≤ r′ → rC r ⊑ rC r′
rC-mono le = mk⊑ (λ { s (inj₁ lt) → inj₁ (<-≤-trans lt le) ; s (inj₂ lt) → inj₂ lt })

rC-cong : ∀ {r r′} → r ≃ r′ → rC r ≋ rC r′
rC-cong e = rC-mono (≤-≃ e) , rC-mono (≤-≃ (≃-sym e))

rC-add-⊑ : ∀ a b → rC (a + b) ⊑ rC a ⊕ rC b
rC-add-⊑ a b = mk⊑ go
  where
    go : ∀ s → mem (rC (a + b)) s → mem (rC a ⊕ rC b) s
    go s (inj₁ lt) with dense (≃-<ʳ (solve 2 (λ a b → (a :+ b) :+ :- b := a) ≃-refl a b) (+-mono-<-≤ lt (≤-refl {(- b)})))
    ... | ρ , s-b<ρ , ρ<a = ρ , s + - ρ , inj₁ ρ<a , inj₁ tb ,
          ≤-≃ (≃-sym (solve 2 (λ ρ s → ρ :+ (s :+ :- ρ) := s) ≃-refl ρ s))
      where
        tb : s + - ρ < b
        tb = ≃-<ʳ (solve 2 (λ ρ b → ρ :+ (b :+ :- ρ) := b) ≃-refl ρ b)
              (≃-<ˡ (solve 3 (λ s b ρ → (s :+ :- b) :+ (b :+ :- ρ) := s :+ :- ρ) ≃-refl s b ρ)
                (+-mono-<-≤ s-b<ρ (≤-refl {b + - ρ})))
    go s (inj₂ lt) with split-neg lt
    ... | a′ , b′ , a<0 , b<0 , le = a′ , b′ , inj₂ a<0 , inj₂ b<0 , le

----------------------------------------------------------------------------
-- the grid points

th : ℕ → ℕ → Q
th k a = nat a * tp k

th-suc : ∀ k a → th k (suc a) ≃ th k a + tp k
th-suc k a = ≃-trans (nat-suc* a (tp k)) ≃-refl

nat-mono′ : ∀ {a b} → a ℕ.≤′ b → nat a ≤ nat b
nat-mono′ ℕ.≤′-refl = ≤-refl
nat-mono′ {a} (ℕ.≤′-step {b} le) = ≤-trans (nat-mono′ le)
  (≤-trans (≤-+ʳ′ (nat b) 1Q (<-≤ 0<1)) (≤-≃ (≃-sym (nat-suc b))))

th-mono : ∀ k {a b} → a ℕ.≤′ b → th k a ≤ th k b
th-mono k le = *-mono-≤-nnʳ (<-≤ (tp-pos k)) (nat-mono′ le)

th-zero : ∀ k → th k 0 ≃ 0Q
th-zero k = *-zeroˡ (tp k)

rC-th-suc : ∀ k a → rC (th k (suc a)) ⊑ rC (th k a) ⊕ rC (tp k)
rC-th-suc k a = ⊑-trans (⊑-≋ (rC-cong (th-suc k a))) (rC-add-⊑ (th k a) (tp k))

module Grid (lem : ∀ (P : Set) → P ⊎ (P → ⊥)) (B : BM.BorelMeasure lem) where
  open Simple lem B
  open LevelSets lem using (Lvl; LS)
  open Sf

  module _ (k : ℕ) (h : R₁ → Cut) (LV : ∀ q → Borel (Lvl h q)) (bd : ∀ x → h x ⊑ oneC) where

    T : ℕ → Pred
    T a = Lvl h (th k a)

    gcell : ℕ → Pred
    gcell zero = ∁ (T 1)
    gcell (suc a) = λ c → T (suc a) c × (T (suc (suc a)) c → ⊥)

    gB : ∀ a → Borel (gcell a)
    gB zero = compl (LV (th k 1))
    gB (suc a) = inter₂ (LV (th k (suc a))) (compl (LV (th k (suc (suc a)))))

    T-anti : ∀ {a b} c → a ℕ.≤′ b → T b c → T a c
    T-anti {a} {b} c le = down (h (lift c)) (th-mono k le)

    -- a point of the a-th cell is not above the next grid point
    top-not : ∀ a c → gcell a c → T (suc a) c → ⊥
    top-not zero c g t = g t
    top-not (suc a) c (_ , n) t = n t

    gcell-T : ∀ a c → gcell (suc a) c → T (suc a) c
    gcell-T a c (t , _) = t

    strict : ∀ x a b → a ℕ.< b → gcell a x → gcell b x → ⊥
    strict x a zero () ga gb
    strict x a (suc b) lt ga gb = top-not a x ga (T-anti x (ℕₚ.≤⇒≤′ lt) (gcell-T b x gb))

    g-dj : Disjoint gcell
    g-dj x a b ga gb with ℕₚ.<-cmp a b
    ... | tri≈ _ e _ = e
    ... | tri< lt _ _ = ⊥-elim (strict x a b lt ga gb)
    ... | tri> _ _ gt = ⊥-elim (strict x b a gt gb ga)

    -- some grid point is above h x
    above : Σ ℕ (λ N → ∀ x → T (suc N) x → ⊥)
    above with arch 1Q {tp k} (tp-pos k)
    ... | N , one≤ = N , λ x t →
      <-irrefl ≃-refl (<-≤-trans (ap (bd (lift x)) (th k (suc N)) t)
        (≤-trans one≤ (th-mono k (ℕₚ.≤⇒≤′ (ℕₚ.n≤1+n N)))))

    find : ∀ x M → (T (suc M) x → ⊥) → Σ ℕ (λ a → gcell a x)
    find x zero nt = zero , nt
    find x (suc M) nt with lem (T (suc M) x)
    ... | inj₁ y = suc M , y , nt
    ... | inj₂ n = find x M n

    g-cov : ∀ x → Σ ℕ (λ a → gcell a x)
    g-cov x = find x (proj₁ above) (proj₂ above x)

    grid : Sf
    grid = record { V = gcell ; bV = gB ; dj = g-dj ; cov = g-cov ; ρ = λ a → rC (th k a) }

    -- the grid function lies below h ...
    grid-minor : ∀ a x → gcell a x → rC (th k a) ⊑ h (lift x)
    grid-minor zero x g = mk⊑ λ { s (inj₁ lt) → neg (h (lift x)) (≃-<ʳ (th-zero k) lt) ; s (inj₂ lt) → neg (h (lift x)) lt }
    grid-minor (suc a) x (t , _) = mk⊑ λ { s (inj₁ lt) → down (h (lift x)) (<-≤ lt) t ; s (inj₂ lt) → neg (h (lift x)) lt }

    -- ... and h lies below the next grid point
    grid-upper : ∀ a x → gcell a x → h (lift x) ⊑ rC (th k (suc a))
    grid-upper a x g = mk⊑ λ s m → inj₁ (go s m (≤-or-> (th k (suc a)) s))
      where
        go : ∀ s → mem (h (lift x)) s → (th k (suc a) ≤ s ⊎ s < th k (suc a)) → s < th k (suc a)
        go s m (inj₁ le) = ⊥-elim (top-not a x g (down (h (lift x)) le m))
        go s m (inj₂ lt) = lt
