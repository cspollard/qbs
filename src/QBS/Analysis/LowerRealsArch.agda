{-# OPTIONS --safe --without-K #-}

-- The `Arch` structure (a half, tolerances 2⁻ⁿ, Archimedean closure, order cancellation, tails)
-- on the extended non-negative reals as lower cuts of the rationals.
module QBS.Analysis.LowerRealsArch where

import Level as L
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)

open import QBS.Analysis.RationalLemmas
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.Omega
open import QBS.Analysis.Archimedean
open import QBS.Analysis.Half using (module Half)
open import QBS.Classical using (LEM₀)

----------------------------------------------------------------------------
-- the rationals ½ⁿ

private
  2Q : ℚᵘ
  2Q = 1ℚᵘ + 1ℚᵘ

  0<2 : 0ℚᵘ < 2Q
  0<2 = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-<-≤ 0<1 (<-≤ 0<1))

hf : ℚᵘ
hf = proj₁ (inv 0<2)

hf*2 : hf * 2Q ≃ 1ℚᵘ
hf*2 = proj₂ (inv 0<2)

hf+hf : hf + hf ≃ 1ℚᵘ
hf+hf = ≃-trans (≃-sym (solve 1 (λ h → h :* (con 1ℚᵘ :+ con 1ℚᵘ) := h :+ h) ≃-refl hf)) hf*2

0<hf : 0ℚᵘ < hf
0<hf with pos-or-nonpos hf
... | inj₁ p = p
... | inj₂ np = ⊥-elim (<-irrefl ≃-refl (<-≤-trans 0<1 (≤-resp hf*2 (*-zeroˡ 2Q)
    (≤-trans (*-mono-≤-nnʳ (<-≤ 0<2) np) (≤-≃ (*-zeroˡ 2Q))))))

tp : ℕ → ℚᵘ
tp zero = 1ℚᵘ
tp (suc n) = hf * tp n

tp-pos : ∀ n → 0ℚᵘ < tp n
tp-pos zero = 0<1
tp-pos (suc n) = *-pos 0<hf (tp-pos n)

tp-double : ∀ n → tp (suc n) + tp (suc n) ≃ tp n
tp-double n = ≃-trans (≃-sym (*-distribʳ-+ (tp n) hf hf))
  (≃-trans (*-cong hf+hf (≃-refl {tp n})) (*-identityˡ (tp n)))

tp-lt : ∀ n → tp (suc n) < tp n
tp-lt n = ≃-<ˡ (≃-refl) (≃-<ʳ (tp-double n) (lt-add {tp (suc n)} {tp (suc n)} (tp-pos (suc n))))

nat-nonneg : ∀ k → 0ℚᵘ ≤ nat k
nat-nonneg zero = ≤-refl
nat-nonneg (suc k) = ≤-resp (≃-refl) (≃-sym (nat-suc k))
  (≤-trans (nat-nonneg k) (≤-≃ (≃-sym (+-identityʳ (nat k)))) |> λ h → ≤-trans h (+-mono-≤ (≤-refl {nat k}) (<-≤ 0<1)))
  where _|>_ = λ {A B : Set} (v : A) (f : A → B) → f v

nat-1≤1 : nat 1 ≤ 1ℚᵘ
nat-1≤1 = ≤-≃
    (≃-trans (nat-suc 0) (≃-trans (+-cong (≃-refl {nat 0}) (≃-refl {1ℚᵘ})) (≃-trans (+-cong z (≃-refl {1ℚᵘ})) (+-identityˡ 1ℚᵘ))))
  where z : nat 0 ≃ 0ℚᵘ
        z = ≃-refl

tp-≤1 : ∀ n → tp n ≤ 1ℚᵘ
tp-≤1 zero = ≤-refl
tp-≤1 (suc n) = ≤-trans (<-≤ (tp-lt n)) (tp-≤1 n)

tp-nat : ∀ n → nat (suc n) * tp n ≤ 1ℚᵘ
tp-nat zero = ≤-trans (≤-≃ (*-identityʳ′ (nat 1))) nat-1≤1
  where *-identityʳ′ : ∀ p → p * 1ℚᵘ ≃ p
        *-identityʳ′ p = ≃-trans (*-comm p 1ℚᵘ) (*-identityˡ p)
tp-nat (suc n) = ≤-trans (≤-≃ eq)
  (≤-trans (+-mono-≤ (*-mono-≤-nn (<-≤ 0<hf) (tp-nat n)) (*-mono-≤-nn (<-≤ 0<hf) (tp-≤1 n))) (≤-≃ two))
  where
    eq : nat (suc (suc n)) * tp (suc n) ≃ hf * (nat (suc n) * tp n) + hf * tp n
    eq = ≃-trans (*-cong (nat-suc (suc n)) (≃-refl {tp (suc n)}))
      (solve 3 (λ N h t → (N :+ con 1ℚᵘ) :* (h :* t) := h :* (N :* t) :+ h :* t) ≃-refl (nat (suc n)) hf (tp n))
    two : hf * 1ℚᵘ + hf * 1ℚᵘ ≃ 1ℚᵘ
    two = ≃-trans (+-cong (≃-trans (*-comm hf 1ℚᵘ) (*-identityˡ hf)) (≃-trans (*-comm hf 1ℚᵘ) (*-identityˡ hf))) hf+hf

-- the tolerances tend to zero
≤-+ʳ′ : ∀ a b → 0ℚᵘ ≤ b → a ≤ a + b
≤-+ʳ′ a b 0≤b = ≤-trans (≤-≃ (≃-sym (+-identityʳ a))) (+-mono-≤ (≤-refl {a}) 0≤b)

tp-small : ∀ δ → 0ℚᵘ < δ → Σ ℕ (λ n → tp n < δ)
tp-small δ 0<δ with arch 2Q {δ} 0<δ
... | k , 2≤kδ with ≤-or-> δ (tp k)
... | inj₂ lt = k , lt
... | inj₁ δ≤t = ⊥-elim (<-irrefl ≃-refl (<-≤-trans (lt-add {1ℚᵘ} {1ℚᵘ} 0<1) two≤one))
  where
    two≤one : 2Q ≤ 1ℚᵘ
    two≤one = ≤-trans 2≤kδ
      (≤-trans (≤-+ʳ′ (nat k * δ) δ (<-≤ 0<δ))
        (≤-trans (≤-≃ (≃-sym (nat-suc* k δ)))
          (≤-trans (*-mono-≤-nn (nat-nonneg (suc k)) δ≤t) (tp-nat k))))

----------------------------------------------------------------------------
-- rational cuts

qC : (q : ℚᵘ) → 0ℚᵘ < q → Cut
qC q 0<q = record
  { mem = _< q
  ; down = λ le lt → ≤-<-trans le lt
  ; open′ = λ lt → dense lt
  ; neg = λ lt → <-trans lt 0<q }

qC-cong : ∀ {q q′} (0<q : 0ℚᵘ < q) (0<q′ : 0ℚᵘ < q′) → q ≃ q′ → qC q 0<q ≋ qC q′ 0<q′
qC-cong 0<q 0<q′ e = mk⊑ (λ s lt → ≃-<ʳ e lt) , mk⊑ (λ s lt → ≃-<ʳ (≃-sym e) lt)

pos+ : ∀ {a b} → 0ℚᵘ < a → 0ℚᵘ < b → 0ℚᵘ < a + b
pos+ 0<a 0<b = ≃-<ˡ (+-identityˡ 0ℚᵘ) (+-mono-< 0<a 0<b)

qC-add : ∀ {a b} (0<a : 0ℚᵘ < a) (0<b : 0ℚᵘ < b) → qC a 0<a ⊕ qC b 0<b ≋ qC (a + b) (pos+ 0<a 0<b)
qC-add {a} {b} 0<a 0<b = mk⊑ fwd , mk⊑ bwd
  where
    fwd : ∀ s → mem (qC a 0<a ⊕ qC b 0<b) s → s < a + b
    fwd s (r , t , ra , tb , h) = ≤-<-trans h (+-mono-< ra tb)
    bwd : ∀ s → s < a + b → mem (qC a 0<a ⊕ qC b 0<b) s
    bwd s lt with dense (≃-<ʳ (solve 2 (λ a b → (a :+ b) :+ :- b := a) ≃-refl a b) (+-mono-<-≤ lt (≤-refl {(- b)})))
    ... | ρ , s-b<ρ , ρ<a = ρ , s + - ρ , ρ<a , tb , ≤-≃ (≃-sym (solve 2 (λ ρ s → ρ :+ (s :+ :- ρ) := s) ≃-refl ρ s))
      where
        tb : s + - ρ < b
        tb = ≃-<ʳ (solve 3 (λ ρ b s → ρ :+ (b :+ :- ρ) := b) ≃-refl ρ b s)
              (≃-<ˡ (solve 3 (λ s b ρ → (s :+ :- b) :+ (b :+ :- ρ) := s :+ :- ρ) ≃-refl s b ρ)
                (+-mono-<-≤ s-b<ρ (≤-refl {b + - ρ})))

hpC : ℕ → Cut
hpC n = qC (tp n) (tp-pos n)

halfC : Cut
halfC = qC hf 0<hf

hpC-double : ∀ n → hpC (suc n) ⊕ hpC (suc n) ≋ hpC n
hpC-double n = ≋-trans (qC-add (tp-pos (suc n)) (tp-pos (suc n)))
  (qC-cong (pos+ (tp-pos (suc n)) (tp-pos (suc n))) (tp-pos n) (tp-double n))

halfC-double : halfC ⊕ halfC ≋ oneC
halfC-double = ≋-trans (qC-add 0<hf 0<hf) (qC-cong (pos+ 0<hf 0<hf) 0<1 hf+hf)

----------------------------------------------------------------------------
-- the instance

module _ (lem : LEM₀) where
  open Classical lem

  -- the rational tolerances are the powers of `halfC`
  hpC≈ : ∀ n → hpC n ≋ Half.hp (LowerRealsOmega lem) halfC halfC-double n
  hpC≈ = Half.hp-unique (LowerRealsOmega lem) halfC halfC-double hpC (⊑-refl , ⊑-refl) hpC-double

  arch-⊑ : ∀ {x y} → (∀ n → x ⊑ y ⊕ hpC n) → x ⊑ y
  arch-⊑ {x} {y} h = mk⊑ λ q m →
    let q′ , q<q′ , mq′ = open′ x m
        δ = q′ + - q
        n , tn<δ = tp-small δ (pos-diff q<q′)
        r , t , mr , mt , le = ap (h n) q′ mq′
    in go q q′ n tn<δ r t mr mt le
    where
      go : ∀ q q′ n → tp n < q′ + - q → ∀ r t → mem y r → t < tp n → q′ ≤ r + t → mem y q
      go q q′ n tn<δ r t mr mt le with ≤-or-> r q
      ... | inj₂ q<r = down y (<-≤ q<r) mr
      ... | inj₁ r≤q = ⊥-elim (<-irrefl ≃-refl (≤-<-trans le (≃-<ʳ eq (+-mono-≤-< r≤q (<-trans mt tn<δ)))))
        where
          eq : q + (q′ + - q) ≃ q′
          eq = add-sub q q′

  way-below-⊑ : ∀ c → unionC c ⊑ oneC → ∀ n → Σ ℕ (λ N → unionC c ⊑ c N ⊕ hpC n)
  way-below-⊑ c bd n with near-sup (unionC c) {tp (suc n)} bd (tp-pos (suc n))
  ... | r , (N , rN) , near = N , mk⊑ (λ q mq → r , tp (suc n) , rN , tp-lt n , near q mq)

  lowerRealsArch : Arch (LowerRealsOmega lem)
  lowerRealsArch = record
    { half = halfC
    ; half+half = halfC-double
    ; arch = λ h → arch-⊑ (λ n → ⊑-trans (h n) (⊕-mono ⊑-refl (proj₂ (hpC≈ n))))
    ; cancel≤ = cancel-⊑
    ; way-below = λ c inc bd n →
        let N , le = way-below-⊑ c bd n in N , ⊑-trans le (⊕-mono ⊑-refl (proj₁ (hpC≈ n)))
    }
