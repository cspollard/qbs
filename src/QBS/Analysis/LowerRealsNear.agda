{-# OPTIONS --safe --without-K #-}

-- Finite lower reals are approached from below, and what follows, used by dominated convergence.
--   * `near-sup-bnd c M`: a cut bounded by the rational M has an element within ε of every other element
--     (`LowerReals.near-sup` for the bound 1, with the same excluded-middle iteration);
--   * `cancel-bnd-⊑`: `a ⊕ x ⊑ a ⊕ y` gives `x ⊑ y` for a rationally bounded a (the order version of
--     `BoundedCancel.cancel-bnd`);
--   * `inter-add`: if `a ⊑ b n ⊕ d` for every n and d is bounded, then `a ⊑ interC b ⊕ d`;
--   * `min-split-⊑`: for `a ⊑ b`, `a ⊕ (b ⊓ c) ⊑ (a ⊓ c) ⊕ b`.
module QBS.Analysis.LowerRealsNear where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open import QBS.Analysis.LowerRealsMin using (_⊓_)
open import QBS.Analysis.LowerRealsInf using (interC)
open import QBS.Classical using (LEM₀)
open Cut
open _⊑_

-- a rational bound
BndQ : Cut → Set
BndQ t = Σ ℚᵘ (λ M → ∀ r → mem t r → r < M)

module Near (lem : LEM₀) where

  -- if no element is within ε of the supremum, every element has a larger one by more than ε
  Near : Cut → ℚᵘ → Set
  Near c ε = Σ ℚᵘ (λ r → mem c r × (∀ r′ → mem c r′ → r′ ≤ r + ε))

  nsb-step : ∀ c ε → (Near c ε → ⊥) → ∀ r → mem c r → Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′)
  nsb-step c ε no r mr with lem (Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′))
  ... | inj₁ yes = yes
  ... | inj₂ none = ⊥-elim (no (r , mr , λ r′ m′ → help r′ m′ (≤-or-> r′ (r + ε))))
    where
      help : ∀ r′ → mem c r′ → r′ ≤ r + ε ⊎ r + ε < r′ → r′ ≤ r + ε
      help r′ m′ (inj₁ le) = le
      help r′ m′ (inj₂ lt) = ⊥-elim (none (r′ , m′ , lt))

  -- the iterates climb by more than ε each time
  nsb-iter : ∀ c ε → (∀ r → mem c r → Σ ℚᵘ (λ r′ → mem c r′ × r + ε < r′)) →
    ∀ n → Σ ℚᵘ (λ r → mem c r × (0ℚᵘ + - 1ℚᵘ) + nat n * ε ≤ r)
  nsb-iter c ε st zero = _ , neg c (neg-diff 0<1) ,
    ≤-≃ (≃-trans (+-cong (≃-refl {0ℚᵘ + - 1ℚᵘ}) (*-zeroˡ ε)) (+-identityʳ (0ℚᵘ + - 1ℚᵘ)))
  nsb-iter c ε st (suc n) with nsb-iter c ε st n
  ... | r , mr , h with st r mr
  ... | r′ , mr′ , lt = r′ , mr′ ,
    ≤-trans (≤-≃ (≃-trans (+-cong (≃-refl {0ℚᵘ + - 1ℚᵘ}) (nat-suc* n ε)) (ring₇ (0ℚᵘ + - 1ℚᵘ) (nat n * ε) ε)))
      (<-≤ (≤-<-trans (+-mono-≤ h (≤-refl {ε})) lt))

  -- a cut bounded by M has an element within ε of its supremum
  near-sup-bnd : ∀ c M {ε} → (∀ r → mem c r → r < M) → 0ℚᵘ < ε → Near c ε
  near-sup-bnd c M {ε} bd 0<ε with lem (Near c ε)
  ... | inj₁ yes = yes
  ... | inj₂ no = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (bd rk mrk) final))
    where
      it : ∀ n → Σ ℚᵘ (λ r → mem c r × (0ℚᵘ + - 1ℚᵘ) + nat n * ε ≤ r)
      it = nsb-iter c ε (nsb-step c ε no)
      k = proj₁ (arch (M + 1ℚᵘ) 0<ε)
      rk = proj₁ (it k)
      mrk = proj₁ (proj₂ (it k))
      eqM : M ≃ (0ℚᵘ + - 1ℚᵘ) + (M + 1ℚᵘ)
      eqM = solve 1 (λ M → M := (con 0ℚᵘ :+ :- con 1ℚᵘ) :+ (M :+ con 1ℚᵘ)) ≃-refl M
      final : M ≤ rk
      final = ≤-trans (≤-≃ eqM) (≤-trans (+-mono-≤ (≤-refl {0ℚᵘ + - 1ℚᵘ}) (proj₂ (arch (M + 1ℚᵘ) 0<ε)))
        (proj₂ (proj₂ (it k))))

  -- cancellation of a rationally bounded summand
  cancel-bnd-⊑ : ∀ {a x y} → BndQ a → a ⊕ x ⊑ a ⊕ y → x ⊑ y
  cancel-bnd-⊑ {a} {x} {y} (M , bd) f = mk⊑ (λ q mq →
    let q′ , q<q′ , mq′ = open′ x mq
        δ = q′ + - q
        r , mr , hr = near-sup-bnd a M bd (pos-diff q<q′)
        r″ , s , mr″ , ms , h = ap f (r + q′) (r , q′ , mr , mq′ , ≤-refl)
        le₁ : r + q′ ≤ (r + δ) + s
        le₁ = ≤-trans h (+-mono-≤ (hr r″ mr″) (≤-refl {s}))
        q≤s : q ≤ s
        q≤s = ≤-trans (≤-≃ (ring₄ r q q′))
                (≤-trans (+-mono-≤ le₁ (≤-refl {(- (r + δ))})) (≤-≃ (ring₅ (r + δ) s)))
    in down y q≤s ms)

  w-gt : ∀ q q₂ m s* → m < q₂ → (q + - s*) < q₂ + - (s* + (m + - q))
  w-gt q q₂ m s* m<q₂ = ≃-<ʳ
    (solve 4 (λ q q₂ m s → (q :+ :- s) :+ (q₂ :+ :- m) := q₂ :+ :- (s :+ (m :+ :- q))) ≃-refl q q₂ m s*)
    (lt-add {q + - s*} (pos-diff m<q₂))

  w-mem : ∀ {b d : Cut} {q₂} s* {η} → (Σ ℚᵘ (λ r → Σ ℚᵘ (λ s → mem b r × mem d s × q₂ ≤ r + s))) →
    (∀ s → mem d s → s ≤ s* + η) → mem b (q₂ + - (s* + η))
  w-mem {b} s* {η} (r , s , mr , ms , le) hs =
    down b (≤-trans (+-mono-≤ (≤-trans le (+-mono-≤ (≤-refl {r}) (hs s ms))) (≤-refl {(- (s* + η))}))
      (≤-≃ (solve 2 (λ r t → (r :+ t) :+ :- t := r) ≃-refl r (s* + η)))) mr

  -- the interior of an intersection commutes with adding a bounded cut
  inter-add : ∀ {a} {b : ℕ → Cut} {d} → BndQ d → (∀ n → a ⊑ b n ⊕ d) → a ⊑ interC b ⊕ d
  inter-add {a} {b} {d} (M , bd) h = mk⊑ (λ q mq →
    let q₂ , q<q₂ , m₂ = open′ a mq
        m , q<m , m<q₂ = dense q<q₂
        s* , ms* , hs = near-sup-bnd d M bd (pos-diff q<m)
    in q + - s* , s* , (_ , w-gt q q₂ m s* m<q₂ , (λ n → w-mem {b n} {d} s* (ap (h n) q₂ m₂) hs)) , ms* ,
       ≤-≃ (≃-sym (sub-add q s*)))

  -- a + min (b, c) ≤ min (a, c) + b for a ≤ b
  min-split-⊑ : ∀ {a b} c → a ⊑ b → a ⊕ (b ⊓ c) ⊑ (a ⊓ c) ⊕ b
  min-split-⊑ {a} {b} c ab = mk⊑ (λ q (r , s , mr , (mbs , mcs) , le) → go q r s mr mbs mcs le (lem (mem c r)))
    where
      go : ∀ q r s → mem a r → mem b s → mem c s → q ≤ r + s → mem c r ⊎ (mem c r → ⊥) →
        mem ((a ⊓ c) ⊕ b) q
      go q r s mr mbs mcs le (inj₁ mcr) = r , s , (mr , mcr) , mbs , le
      go q r s mr mbs mcs le (inj₂ ncr) = s , r , (down a (<-≤ s<r) mr , mcs) , ap ab r mr ,
        ≤-trans le (≤-≃ (+-comm r s))
        where s<r = not-≤⇒< (λ r≤s → ncr (down c r≤s mcs))
