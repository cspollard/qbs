{-# OPTIONS --safe --without-K #-}

-- The exponential on the lower reals [0, ∞] (`Analysis/Exp` instantiated at `LowerRealsOmega`): the
-- reciprocals `1/(n+1)` are the rational cuts `qC (1/(n+1))`; the only work is the product of two
-- rational cuts (`qC-mul`) and `natE (n+1) ≋ qC (n+1)`, which give `1/(n+1) · (n+1) = 1`.
-- Export: `expC lem : Cut → Cut` with `expC-zero`, `expC-mono`, `expC-cong`, `1+≤expC`, `Add.exp-add`, and
-- the bound `expC-bound : x ⊑ natE N → ∀ s ∈ expC x, s < 3ᴺ` (`pow3 N`), from `exp x ≤ 3ᴺ` for `x ≤ N`.
module QBS.Analysis.ExpLower where

open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Rational.Unnormalised.Base using (_+_; _*_; -_; _<_; _≤_; _≃_)
open import Data.Rational.Unnormalised.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; :-_; _:=_; con)

open import QBS.Analysis.RationalLemmas
open import QBS.Analysis.LowerReals
open Cut
open _⊑_
open import QBS.Analysis.LowerRealsArch using (qC; qC-cong; qC-add)
open import QBS.Analysis.Omega
open import QBS.Analysis.Exp
open import QBS.Classical using (LEM₀)

P-id : ∀ q → q * 1ℚᵘ ≃ q
P-id q = ≃-trans (*-comm q 1ℚᵘ) (*-identityˡ q)

-- positivity of a reciprocal
pos-inv : ∀ {s t} → 0ℚᵘ < s → t * s ≃ 1ℚᵘ → 0ℚᵘ < t
pos-inv {s} {t} 0<s h with pos-or-nonpos t
... | inj₁ 0<t = 0<t
... | inj₂ t≤0 = ⊥-elim (<-irrefl ≃-refl
  (<-≤-trans 0<1 (≤-trans (≤-≃ (≃-sym h)) (≤-trans (*-mono-≤-nnʳ (<-≤ 0<s) t≤0) (≤-≃ (*-zeroˡ s))))))

-- the product of rational cuts
qC-mul-fwd : ∀ {a b} (0<a : 0ℚᵘ < a) (0<b : 0ℚᵘ < b) q → mem (qC a 0<a ⊗ qC b 0<b) q → q < a * b
qC-mul-fwd {a} {b} 0<a 0<b q (inj₁ q<0) = <-trans q<0 (*-pos 0<a 0<b)
qC-mul-fwd {a} {b} 0<a 0<b q (inj₂ (r , s , 0<r , 0<s , r<a , s<b , h)) =
  ≤-<-trans h (<-trans (*-mono-<-posʳ 0<s r<a) (*-mono-<-pos 0<a s<b))

-- some `s < b` with `q₂ < a s`
pick-s : ∀ {a b q₂} → 0ℚᵘ < a → 0ℚᵘ < q₂ → q₂ < a * b → Σ ℚᵘ (λ s → 0ℚᵘ < s × s < b × q₂ < a * s)
pick-s {a} {b} {q₂} 0<a 0<q₂ q₂<ab =
  let ta , hta = inv 0<a
      0<ta = pos-inv 0<a hta
      qt<b : q₂ * ta < b
      qt<b = ≃-<ʳ (≃-trans (solve 3 (λ a b t → (a :* b) :* t := (t :* a) :* b) ≃-refl a b ta)
                    (≃-trans (*-cong hta (≃-refl {b})) (*-identityˡ b)))
                  (*-mono-<-posʳ 0<ta q₂<ab)
      s , qt<s , s<b = dense qt<b
  in s , <-trans (*-pos 0<q₂ 0<ta) qt<s , s<b ,
     ≃-<ˡ (≃-trans (*-assoc q₂ ta a) (≃-trans (*-cong (≃-refl {q₂}) hta) (P-id q₂)))
       (≃-<ʳ (*-comm s a) (*-mono-<-posʳ 0<a qt<s))

qC-mul-bwd : ∀ {a b} (0<a : 0ℚᵘ < a) (0<b : 0ℚᵘ < b) q → q < a * b → mem (qC a 0<a ⊗ qC b 0<b) q
qC-mul-bwd {a} {b} 0<a 0<b q lt with neg-or-nonneg q
... | inj₁ q<0 = inj₁ q<0
... | inj₂ 0≤q =
  let q₂ , q<q₂ , q₂<ab = dense lt
      0<q₂ = ≤-<-trans 0≤q q<q₂
      s , 0<s , s<b , q₂<as = pick-s {a} {b} 0<a 0<q₂ q₂<ab
      ts , hts = inv 0<s
      0<ts = pos-inv 0<s hts
      rs : (q₂ * ts) * s ≃ q₂
      rs = ≃-trans (*-assoc q₂ ts s) (≃-trans (*-cong (≃-refl {q₂}) hts) (P-id q₂))
      r<a : q₂ * ts < a
      r<a = *-cancel-<ʳ 0<s (≃-<ˡ (≃-sym rs) q₂<as)
  in inj₂ (q₂ * ts , s , *-pos 0<q₂ 0<ts , 0<s , r<a , s<b , ≤-trans (<-≤ q<q₂) (≤-≃ (≃-sym rs)))

qC-mul : ∀ {a b} (0<a : 0ℚᵘ < a) (0<b : 0ℚᵘ < b) → qC a 0<a ⊗ qC b 0<b ≋ qC (a * b) (*-pos 0<a 0<b)
qC-mul 0<a 0<b = mk⊑ (qC-mul-fwd 0<a 0<b) , mk⊑ (qC-mul-bwd 0<a 0<b)

----------------------------------------------------------------------------
-- the reciprocals of the positive integers

0<nat : ∀ n → 0ℚᵘ < nat (suc n)
0<nat n = ≃-<ʳ (≃-sym (nat-suc n)) (<-≤-trans 0<1 (≤-trans (≤-+ʳ 1ℚᵘ (nat n) (nat-nonneg n))
  (≤-≃ (+-comm 1ℚᵘ (nat n)))))

qinv : ℕ → ℚᵘ
qinv n = proj₁ (inv (0<nat n))

qinv-ok : ∀ n → qinv n * nat (suc n) ≃ 1ℚᵘ
qinv-ok n = proj₂ (inv (0<nat n))

module _ (lem : LEM₀) where
  private
    A = LowerRealsOmega lem
  open Exp A using (natE; pw; module WithInv)

  -- the cut `natE (n+1)` (the n+1-fold sum of one) is the rational cut `n+1`
  natE≋ : ∀ n → natE (suc n) ≋ qC (nat (suc n)) (0<nat n)
  natE≋ zero = ≋-trans (⊕-identityˡ oneC) (⊑-refl , ⊑-refl)
  natE≋ (suc n) = ≋-trans (⊕-cong (natE≋ n) (⊑-refl {oneC} , ⊑-refl))
    (≋-trans (qC-add (0<nat n) 0<1)
      (qC-cong (+-pos (0<nat n) 0<1) (0<nat (suc n)) (≃-sym (nat-suc (suc n)))))

  qinvC : ℕ → Cut
  qinvC n = qC (qinv n) (pos-inv (0<nat n) (qinv-ok n))

  inv-ok : ∀ n → qinvC n ⊗ natE (suc n) ≋ oneC
  inv-ok n = ≋-trans (⊗-cong (⊑-refl , ⊑-refl) (natE≋ n))
    (≋-trans (qC-mul (pos-inv (0<nat n) (qinv-ok n)) (0<nat n))
      (≋-trans (qC-cong (*-pos (pos-inv (0<nat n) (qinv-ok n)) (0<nat n)) 0<1 (qinv-ok n)) (⊑-refl , ⊑-refl)))

  open WithInv qinvC inv-ok public
    renaming (exp to expC; exp-zero to expC-zero; exp-mono to expC-mono; exp-cong to expC-cong;
              1+≤exp to 1+≤expC; exp≤three^ to expC≤three^; exp≤quad to expC≤quad)

  -- `3ᴺ`
  pow3 : ℕ → ℚᵘ
  pow3 zero = 1ℚᵘ
  pow3 (suc n) = (1ℚᵘ + (1ℚᵘ + 1ℚᵘ)) * pow3 n

  0<pow3 : ∀ n → 0ℚᵘ < pow3 n
  0<pow3 zero = 0<1
  0<pow3 (suc n) = *-pos (+-pos 0<1 (+-pos 0<1 0<1)) (0<pow3 n)

  -- the elements of `1 + (1 + 1)` are below `3`
  three-bd : ∀ s → mem (oneC ⊕ (oneC ⊕ oneC)) s → s < 1ℚᵘ + (1ℚᵘ + 1ℚᵘ)
  three-bd s (r , t , r<1 , (a , b , a<1 , b<1 , h) , le) =
    ≤-<-trans le (≤-<-trans (+-mono-≤ (≤-refl {r}) h)
      (+-mono-<-≤ r<1 (<-≤ (≤-<-trans (+-mono-≤ (≤-refl {a}) (≤-refl {b}))
        (<-trans (+-mono-<-≤ a<1 (≤-refl {b})) (+-mono-≤-< (≤-refl {1ℚᵘ}) b<1))))))

  -- the elements of `3ᴺ` are below `pow3 N`
  pw3-bd : ∀ N s → mem (pw (oneC ⊕ (oneC ⊕ oneC)) N) s → s < pow3 N
  pw3-bd zero s m = m
  pw3-bd (suc N) s (inj₁ s<0) = <-trans s<0 (0<pow3 (suc N))
  pw3-bd (suc N) s (inj₂ (r , t , 0<r , 0<t , mr , mt , h)) =
    ≤-<-trans h (<-trans (*-mono-<-posʳ 0<t (three-bd r mr)) (*-mono-<-pos (+-pos 0<1 (+-pos 0<1 0<1)) (pw3-bd N t mt)))

  -- `x ≤ N` bounds `exp x` by `3ᴺ`
  expC-bound : ∀ x N → x ⊑ natE N → ∀ s → mem (expC x) s → s < pow3 N
  expC-bound x N h s m = pw3-bd N s (ap (expC≤three^ N h) s m)
